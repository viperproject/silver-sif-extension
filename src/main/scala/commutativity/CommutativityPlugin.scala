package commutativity

import viper.silver.ast.utility.Expressions
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{And, Assert, Bool, CondExp, CurrentPerm, EqCmp, Exhale, FieldAccessPredicate, Forall, FullPerm, FuncApp, Function, Implies, Inhale, Let, LocalVarAssign, LocalVarDecl, Method, NewStmt, NoPerm, NoTrafos, NodeTrafo, PermGeCmp, PermGtCmp, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Result, Seqn, Stmt, Trigger, WildcardPerm}
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.sif.{SIFExtendedTransformer, SIFLowEventExp}
import viper.silver.verifier._

import scala.collection.mutable.ListBuffer
import scala.collection.{Set, mutable}

class CommutativityPlugin extends ParserPluginTemplate with SilverPlugin {

  var nameCtr = 0

  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  override lazy val newDeclAtEnd = P(lockSpec)
  override lazy val newExpAtStart = P(pointsToPred | joinable | low | lowEvent | locked | lock | guard)
  override lazy val newStmtAtStart = P(fork | join | newLock | acquire | release)

  lazy val cStyleMethod : P[PMethod] = P(ctyp ~ idndef ~ parens(cvardecl.rep(sep=",")) ~ "{" ~ "}").map{
    case (t, name, params) => PMethod(name, params, Seq(PFormalArgDecl(PIdnDef("$res"), t)), Seq(), Seq(), None)
  }

  lazy val cvardecl : P[PFormalArgDecl] = P(ctyp ~ idndef).map{
    case (t, name) => PFormalArgDecl(name, t)
  }

  lazy val ctyp : P[PType] = P(keyword("int").map(_ => PPrimitiv("Int")) | keyword("bool").map(_ => PPrimitiv("Bool")) | idnuse.map(_ => PPrimitiv("Ref")))

  lazy val fork : P[PFork] = P(idnuse ~ ":=" ~ "fork" ~/ idnuse ~ parens(actualArgList)).map{
    case (t, m, args) => PFork(m, t, args)
  }

  lazy val join : P[PJoin] = P((idnuse.rep(sep = ",") ~ ":=").? ~ "join" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map{
    case (targets, m, token) => PJoin(m, if (targets.isDefined) targets.get else Seq(), token)
  }

  lazy val newLock: P[PNewLock] = P(idnuse ~ ":=" ~ "newLock" ~/ "[" ~ idnuse ~ "]" ~ parens(idnuse.rep(sep = ","))).map{
    case (target, lockType, fields) => PNewLock(lockType, target, fields)
  }

  lazy val acquire: P[PAcquire] = P("acquire" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map{
    case (lockType, arg) => PAcquire(lockType, arg)
  }

  lazy val release: P[PRelease] = P("release" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ ("," ~/ idnuse ~ parens(exp)).?)).map{
    case (lockType, (arg, act)) => PRelease(lockType, arg, act)
  }

  lazy val lockSpec : P[PLockSpec] = P("lockType" ~/ idndef ~ "{" ~ "type" ~ typ ~ invariantDecl("invariant", 2) ~ invariantDecl("secInvariant", 1) ~ actionDeclList ~ actionDef.rep ~ proof.rep  ~ "}").map{
    case (name, t, i, si, alist, actions, proofs) => PLockSpec(name, t, i, si, alist, actions, proofs)
  }
  def invariantDecl(name: String, nParams: Int) : P[PInvariantDef] = P(name ~/ parens(idndef.rep(sep=",", exactly = nParams)) ~ "=" ~ atom).map{
    case (params, e) => PInvariantDef(params, e)
  }
  lazy val actionDeclList = P("actions" ~/ "=" ~  "[" ~ actionDecl.rep(sep=",") ~ "]")
  lazy val actionDecl : P[PLockActionDecl] = P("(" ~ idndef ~ "," ~ typ ~ "," ~ typ ~ "," ~ (dupl | nondupl) ~ ")").map{
    case (id, t1, t2, d) => PLockActionDecl(id, t1, t2, d.equals("duplicable"))
  }
  lazy val dupl : P[String] = P(keyword("duplicable")).!
  lazy val nondupl : P[String] = P(keyword("unique")).!
  lazy val actionDef : P[PLockActionDef] = P("action" ~/ idnuse ~ parens(idndef.rep(exactly=2, sep=",")) ~
    keyword("requires") ~ exp ~ keyword("ensures") ~ exp ~
    "{" ~ atom ~ "," ~ atom ~ "}").map{
    case (name, params, pre, post, newVal, retVal) => PLockActionDef(name, params, newVal, retVal, pre, post)
  }
  lazy val proof : P[PProof] = P("proof" ~/ proofType ~ "[" ~ idnuse.rep(sep=",") ~ "]" ~ parens(idndef.rep(sep=",")) ~ "{" ~  stmts ~ "}").map{
    case (ptype, actions, params, pstmt) => PProof(ptype, actions, params, PSeqn(pstmt))
  }
  lazy val proofType : P[String] = P("reordering".! | "commutativity".! | "preservation".!)

  lazy val pointsToPred : P[PPointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ pointsToRhs ~ "]").map{
    case (fa, p, rhs) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PPointsToPredicate(fa, perm, rhs)
    }
  }
  lazy val pointsToRhs : P[PNode] = P(anyVal | definingVar | atom)
  lazy val definingVar : P[PLetNestedScope] = P("?" ~ idndef ~ "&&" ~ exp).map{
    case (i, b) => PLetNestedScope(PFormalArgDecl(i, PPrimitiv("Ref")), b)
  }
  lazy val anyVal : P[PExp] = P("_").map{case _ => PAnyVal()}
  lazy val joinable : P[PJoinable] = P(keyword("joinable") ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map{
    case (method, arg) => PJoinable(method, arg)
  }
  lazy val low : P[PLow] = P(keyword("low") ~/ parens(exp)).map{
    case arg => PLow(arg)
  }
  lazy val lowEvent : P[PLowEvent] = P(keyword("lowEvent")).map{
    case arg => PLowEvent()
  }
  lazy val locked : P[PLocked] = P(keyword("locked") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLocked(ltype, argLock, argVal)
  }
  lazy val lock : P[PLock] = P(keyword("lock") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLock(ltype, argLock, argVal)
  }
  lazy val guard : P[PGuard] = P(keyword("guard") ~/ "[" ~ idnuse ~"," ~ idnuse ~ "]" ~ parens(exp)).map{
    case (ltype, argLock, argVal) => PGuard(ltype, argLock, argVal)
  }

  override lazy val extendedKeywords = Set("lockType", "action", "invariant", "secInvariant", "proof", "reordering", "commutativity", "preservation", "locked", "lock", "guard", "joinable", "duplicable", "unique")

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewExpAtStart(newExpAtStart)
    ParserExtension.addNewKeywords(extendedKeywords)
    ParserExtension.addNewStmtAtStart(newStmtAtStart)
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    input.transform({
      case PDomainType(name, args) if name.name == "Lock" && args.length == 0 => PPrimitiv("Ref")
      case PDomainType(name, args) if name.name == "Thread" && args.length == 0 => PPrimitiv("Ref")
      case PAssume(e) => PInhale(e)
    })()
  }

  def getFreshInt(): Int = {
    nameCtr += 1
    nameCtr - 1
  }

  override def beforeConsistencyCheck(input: Program): Program = {

    val lockSpecs = mutable.HashMap[String, LockSpec]()
    var lockMethods : Seq[Method] = Seq()
    val lockPredNames = mutable.HashMap[String, String]()
    val lockedPredNames = mutable.HashMap[String, String]()
    val actionGuardNames = mutable.HashMap[String, mutable.HashMap[String, String]]()
    val bottomFuncNames = mutable.HashMap[String, String]()

    input.extensions.foreach{
      case l@LockSpec(name, t, inv, secInv, actions, proofs) => {
        if (!Expressions.isPure(secInv.inv)){
          reportError(TypecheckerError("Security invariant must be pure", secInv.inv.pos))
        }
        inv.inv.visit{
          case _: Lock => reportError(TypecheckerError("Invariants must not contain lock() assertions.", inv.inv.pos))
          case _: Locked => reportError(TypecheckerError("Invariants must not contain locked() assertions.", inv.inv.pos))
        }

        lockSpecs.update(name, l)
        lockPredNames.update(name, "$lockpred$" + name)
        lockedPredNames.update(name, "$lockedpred$" + name)
        bottomFuncNames.update(name, "$bottomfunc$" + name)
        val guardNames = mutable.HashMap[String, String]()
        actionGuardNames.update(name, guardNames)


        for (a <- actions){
          guardNames.update(a.name, "$guard$"+name+"$"+a.name)
          if (!Expressions.isPure(a.pre)){
            reportError(TypecheckerError("Precondition must be pure", a.pre.pos))
          }
          if (!Expressions.isPure(a.post)){
            reportError(TypecheckerError("Postcondition must be pure", a.post.pos))
          }
          if (!Expressions.isPure(a.newVal)){
            reportError(TypecheckerError("Action definition must be pure", a.newVal.pos))
          }
          if (!Expressions.isPure(a.returnVal)){
            reportError(TypecheckerError("Action definition must be pure", a.returnVal.pos))
          }
        }
      }
    }


    val joinableNames: Map[String, String] = input.methods.map(m=> m.name->("$joinable$" + m.name)).toMap
    val joinablePreds = joinableNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockPreds = lockPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedPreds = lockedPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)(), LocalVarDecl("$val", lockSpecs.get(n._1).get.t)()), None)())
    val guardPreds = actionGuardNames.map(ls => ls._2.map(a => Predicate(a._2, Seq(LocalVarDecl("$rec", Ref)()), None)())).flatten
    val bottomFuncs = bottomFuncNames.map(n => Function(n._2, Seq(), lockSpecs.get(n._1).get.t, Seq(), Seq(), None)())


    val newPredicates = input.predicates ++ joinablePreds ++ lockPreds ++ lockedPreds ++ guardPreds
    val newFunctions = input.functions ++ bottomFuncs
    val newMethods = ListBuffer[Method]()
    input.methods.foreach(newMethods.append(_))

    input.extensions.foreach{
      case l@LockSpec(name, t, inv, secInv, actions, proofs) => {

        ////// invariant uniquely defines value (ud)
        // declare 1 lock, 2 value vars
        val udLockVar = LocalVarDecl("$udVar$" + getFreshInt(), Ref)()
        val udVal1 = LocalVarDecl("$udVar1$" + getFreshInt(), t)()
        val udVal2 = LocalVarDecl("$udVar2$" + getFreshInt(), t)()

        // inhale perms
        val perms = inv.permissionsWithArgs(Seq(udLockVar.localVar, udVal1.localVar))

        // inhale val def on first and second var
        val valDef1 = inv.pureWithArgs(Seq(udLockVar.localVar, udVal1.localVar))
        val valDef2 = inv.pureWithArgs(Seq(udLockVar.localVar, udVal2.localVar))

        // assert same var
        val sameVal = EqCmp(udVal1.localVar, udVal2.localVar)()

        val udMethod = Method("$udCheck$" + name + "$" + getFreshInt(), Seq(udLockVar, udVal1, udVal2), Seq(), Seq(perms, valDef1, valDef2), Seq(sameVal), Some(Seqn(Seq(), Seq())()))()
        newMethods.append(udMethod)

        for (a <- actions){

          ////// actionX2 preserves secinv
          // declare original, final val, ret val variables
          val presOrigVar = LocalVarDecl("$presOrig$" + getFreshInt(), t)()
          val presArgVar = LocalVarDecl("$presArg$" + getFreshInt(), a.argType)()
          val presFinalVar = LocalVarDecl("$presFinal$" + getFreshInt(), t)()
          val presRetVar = LocalVarDecl("$presRet$" + getFreshInt(), a.retType)()

          // assume secInv and precond
          val presSecInv = secInv.withArgs(Seq(presOrigVar.localVar))
          val presPrecond = a.pre.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar)

          // define results
          val presFinalVal = a.newVal.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar)
          val presRetVal = a.returnVal.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar)
          val presFinalValEq = EqCmp(presFinalVar.localVar, presFinalVal)()
          val presRetValEq = EqCmp(presRetVar.localVar, presRetVal)()

          // assert post and secinv
          val presPostcond = a.post.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar).replace(Result(a.retType)(), presRetVar.localVar)
          val presSecInvFinal = secInv.withArgs(Seq(presFinalVar.localVar))
          val presProof = proofs.find(p => p.proofType == "preservation" && p.actions.length == 1 && p.actions(0) == a.name)
          val presBody = presProof match {
            case None => Some(Seqn(Seq(), Seq())())
            case Some(p) => Some(p.body.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar))
          }
          val presMethod = Method("$presCheck$" + getFreshInt(), Seq(presOrigVar, presArgVar, presFinalVar, presRetVar), Seq(), Seq(presSecInv, presPrecond, presFinalValEq, presRetValEq), Seq(presPostcond, presSecInvFinal), presBody)()
          newMethods.append(presMethod)

          ////// (optional) precondition implies welldef of newVal


          ////// (optional) precondition implies welldef of retVal


          ////// (optional) precondition implies welldef of post

          val a1 = a
          for (a2 <- actions){
            if (actions.indexOf(a1) < actions.indexOf(a2) || (a1 == a2 && a1.duplicable)){
              // for every action with every other action including itself

              ////// actions can be reordered
              // all vars
              val reoOrigDecl = LocalVarDecl("$reoOrig$" + getFreshInt(), t)()
              val reoArg1Decl = LocalVarDecl("$reoArg1$" + getFreshInt(), a1.argType)()
              val reoArg2Decl = LocalVarDecl("$reoArg2$" + getFreshInt(), a2.argType)()
              val reoTmpOpt1Decl = LocalVarDecl("$reoTmpOpt11$" + getFreshInt(), t)()
              val reoTmpOpt2Decl = LocalVarDecl("$reoTmpOpt2$" + getFreshInt(), t)()

              // assumptions: secinv, opt1 pres hold
              val reoOrigSecInv = secInv.withArgs(Seq(reoOrigDecl.localVar))
              val reoOpt1Pre2 = a2.pre.replace(a2.params(0).localVar, reoOrigDecl.localVar).replace(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt1TmpDef = EqCmp(reoTmpOpt1Decl.localVar, a2.newVal.replace(a2.params(0).localVar, reoOrigDecl.localVar).replace(a2.params(1).localVar, reoArg2Decl.localVar))()
              val reoOpt1Pre1 = a1.pre.replace(a1.params(0).localVar, reoTmpOpt1Decl.localVar).replace(a1.params(1).localVar, reoArg1Decl.localVar)

              // opt2 pres hold
              val reoOpt2Pre1 = a1.pre.replace(a1.params(0).localVar, reoOrigDecl.localVar).replace(a1.params(1).localVar, reoArg1Decl.localVar)
              val reoOpt2TmpDef = EqCmp(reoTmpOpt2Decl.localVar, a1.newVal.replace(a1.params(0).localVar, reoOrigDecl.localVar).replace(a1.params(1).localVar, reoArg1Decl.localVar))()
              val reoOpt2Pre2 = a2.pre.replace(a2.params(0).localVar, reoTmpOpt2Decl.localVar).replace(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt2Pre2Impl = Implies(reoOpt2TmpDef, reoOpt2Pre2)()

              val reoName = "$reoCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
              val reoParams = Seq(reoOrigDecl, reoArg1Decl, reoArg2Decl, reoTmpOpt1Decl, reoTmpOpt2Decl)
              val reoPres = Seq(reoOrigSecInv, reoOpt1Pre2, reoOpt1TmpDef, reoOpt1Pre1)
              val reoPosts = Seq(reoOpt2Pre1, reoOpt2Pre2Impl)

              val reoProof = proofs.find(p => p.proofType == "reordering" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val reoBody = if (reoProof.isDefined){
                reoProof.get.body.replace(reoProof.get.params(0).localVar, reoOrigDecl.localVar).replace(reoProof.get.params(1).localVar, reoArg1Decl.localVar).replace(reoProof.get.params(2).localVar, reoArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val reoMethod = Method(reoName, reoParams, Seq(), reoPres, reoPosts, Some(reoBody))()
              newMethods.append(reoMethod)



              ////// actions commute
              // all vars
              val commOrigDecl = LocalVarDecl("$commOrig$" + getFreshInt(), t)()
              val commFinalDecl = LocalVarDecl("$commFinal$" + getFreshInt(), t)()
              val commChoiceDecl = LocalVarDecl("$commChoice$" + getFreshInt(), Bool)()
              val commOrig1Decl = LocalVarDecl("$commOrig1$" + getFreshInt(), t)()
              val commOrig2Decl = LocalVarDecl("$commOrig2$" + getFreshInt(), t)()
              val commArg1Decl = LocalVarDecl("$commArg1$" + getFreshInt(), a1.argType)()
              val commArg2Decl = LocalVarDecl("$commArg2$" + getFreshInt(), a2.argType)()
              val commRes1Decl = LocalVarDecl("$commRes1$" + getFreshInt(), t)()
              val commRes2Decl = LocalVarDecl("$commRes2$" + getFreshInt(), t)()
              val commRet1Decl = LocalVarDecl("$commRet1$" + getFreshInt(), a1.retType)()
              val commRet2Decl = LocalVarDecl("$commRet2$" + getFreshInt(), a2.retType)()

              // pres hold
              val commPreA1 = a1.pre.replace(a1.params(0).localVar, commOrig1Decl.localVar).replace(a1.params(1).localVar, commArg1Decl.localVar)
              val commPreA2 = a2.pre.replace(a2.params(0).localVar, commOrig2Decl.localVar).replace(a2.params(1).localVar, commArg2Decl.localVar)
              val commOrigSecInv = secInv.withArgs(Seq(commOrigDecl.localVar))

              // define results
              val commResA1 = EqCmp(commRes1Decl.localVar, a1.newVal.replace(a1.params(0).localVar, commOrig1Decl.localVar).replace(a1.params(1).localVar, commArg1Decl.localVar))()
              val commResA2 = EqCmp(commRes2Decl.localVar, a2.newVal.replace(a2.params(0).localVar, commOrig2Decl.localVar).replace(a2.params(1).localVar, commArg2Decl.localVar))()
              val commRetA1 = EqCmp(commRet1Decl.localVar, a1.returnVal.replace(a1.params(0).localVar, commOrig1Decl.localVar).replace(a1.params(1).localVar, commArg1Decl.localVar))()
              val commRetA2 = EqCmp(commRet2Decl.localVar, a2.returnVal.replace(a2.params(0).localVar, commOrig2Decl.localVar).replace(a2.params(1).localVar, commArg2Decl.localVar))()

              // define both execution orders
              val commOpt1Orig = EqCmp(commOrigDecl.localVar, commOrig1Decl.localVar)()
              val commOpt1ResOrig = EqCmp(commOrig2Decl.localVar, commRes1Decl.localVar)()
              val commOpt1Final = EqCmp(commFinalDecl.localVar, commRes2Decl.localVar)()
              val commOpt2Orig = EqCmp(commOrigDecl.localVar, commOrig2Decl.localVar)()
              val commOpt2ResOrig = EqCmp(commOrig1Decl.localVar, commRes2Decl.localVar)()
              val commOpt2Final = EqCmp(commFinalDecl.localVar, commRes1Decl.localVar)()
              val commOpt1 = And(And(commOpt1Orig, commOpt1ResOrig)(), commOpt1Final)()
              val commOpt2 = And(And(commOpt2Orig, commOpt2ResOrig)(), commOpt2Final)()
              val commOptions = CondExp(commChoiceDecl.localVar, commOpt1, commOpt2)()

              // checks
              val commCheckSecInv = secInv.withArgs(Seq(commFinalDecl.localVar))
              val commCheckPostA1 = a1.post.replace(a1.params(0).localVar, commOrig1Decl.localVar).replace(a1.params(1).localVar, commArg1Decl.localVar).replace(Result(a1.retType)(), commRet1Decl.localVar)
              val commCheckPostA2 = a2.post.replace(a2.params(0).localVar, commOrig2Decl.localVar).replace(a2.params(1).localVar, commArg2Decl.localVar).replace(Result(a2.retType)(), commRet2Decl.localVar)

              val commName = "$commCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
              val commParams = Seq(commOrigDecl, commFinalDecl, commChoiceDecl, commOrig1Decl, commOrig2Decl, commArg1Decl, commArg2Decl, commRes1Decl, commRes2Decl, commRet1Decl, commRet2Decl)
              val commPres = Seq(commPreA1, commPreA2, commOrigSecInv, commResA1, commResA2, commRetA1, commRetA2, commOptions)
              val commPosts = Seq(commCheckSecInv, commCheckPostA1, commCheckPostA2)

              val commProof = proofs.find(p => p.proofType == "commutativity" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val commBody = if (commProof.isDefined){
                commProof.get.body.replace(commProof.get.params(0).localVar, commOrigDecl.localVar).replace(commProof.get.params(1).localVar, commArg1Decl.localVar).replace(commProof.get.params(2).localVar, commArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val commMethod = Method(commName, commParams, Seq(), commPres, commPosts, Some(commBody))()
              newMethods.append(commMethod)
            }
          }
        }
      }
    }

    val withAdded = input.copy(extensions = Seq(), predicates = newPredicates, functions = newFunctions, methods = newMethods)(input.pos, input.info, input.errT)

    val res = withAdded.transform({
      case pt@PointsToPredicate(fa, p, None) => FieldAccessPredicate(fa, p)()
      case pt@PointsToPredicate(fa, p, Some(e)) => And(FieldAccessPredicate(fa, p)(), EqCmp(fa, e)())()
      case pt@VarDefiningPointsToPredicate(fa, p, v, Some(b)) => And(FieldAccessPredicate(fa, p)(errT=NodeTrafo(pt)), Let(v, fa, b)(errT=NodeTrafo(pt)))(errT = NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, None) => FieldAccessPredicate(fa, p)()
      case Joinable(m, e) => {
        val pa = PredicateAccess(Seq(e), joinableNames.get(m).get)()
        PredicateAccessPredicate(pa, FullPerm()())()
      }
      case Lock(lt, r, amount) => {
        val pa = PredicateAccess(Seq(r), lockPredNames.get(lt).get)()
        PredicateAccessPredicate(pa, amount)()
      }
      case Locked(lt, r, value) => {
        val pa = PredicateAccess(Seq(r, value), lockedPredNames.get(lt).get)()
        PredicateAccessPredicate(pa, FullPerm()())()
      }
      case Guard(lt, g, lock) => {
        val action = lockSpecs.get(lt).get.actions.find(a => a.name == g).get
        val pa = PredicateAccess(Seq(lock), actionGuardNames.get(lt).get.get(g).get)()
        PredicateAccessPredicate(pa, if (action.duplicable) WildcardPerm()() else FullPerm()())()
      }
      case nl@NewLock(lt, target, fields) => {
        val newStmt = NewStmt(target, fields)()
        val fp = FullPerm()()
        val lockPredAcc = PredicateAccess(Seq(target), lockPredNames.get(lt).get)()
        val lockPred = PredicateAccessPredicate(lockPredAcc, fp)()
        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(nl.pos, nl.info, lockSpecs.get(lt).get.t, NoTrafos)
        val lockedPredAcc = PredicateAccess(Seq(target, bottomApp), lockedPredNames.get(lt).get)()
        val lockedPred = PredicateAccessPredicate(lockedPredAcc, fp)()
        val inhale = Inhale(And(lockPred, lockedPred)())()
        val guardInhales = ListBuffer[Inhale]()
        val lockSpec = lockSpecs.get(lt).get
        val guardNames = actionGuardNames.get(lt).get
        for (a <- lockSpec.actions){
          val pa = PredicateAccess(Seq(target), guardNames.get(a.name).get)()
          guardInhales.append(Inhale(PredicateAccessPredicate(pa, fp)())())
        }
        Seqn(Seq(newStmt, inhale) ++ guardInhales, Seq())()
      }
      case a@Acquire(lt, lockExp) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValVarName = "$invVal$" + getFreshInt()
        val invValVarDecl = LocalVarDecl(invValVarName, lockSpec.t)()
        // inhale inv
        val inv = lockSpec.invariant.withArgs(Seq(lockExp, invValVarDecl.localVar))
        val inhaleInv = Inhale(inv)()
        // if full lock perm inhale secinv
        val secInv = lockSpec.secInv.withArgs(Seq(invValVarDecl.localVar))
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val lockPerm = CurrentPerm(lockPredAcc)()
        val hasFullLockPerm = PermGeCmp(lockPerm, FullPerm()())()
        val inhaleSecInv = Inhale(Implies(hasFullLockPerm, secInv)())()
        // inhale locked
        val lockedAccess = PredicateAccess(Seq(lockExp, invValVarDecl.localVar), lockedPredNames.get(lt).get)()
        val lockedPredAcc = PredicateAccessPredicate(lockedAccess, FullPerm()())()
        val inhaleLocked = Inhale(lockedPredAcc)()
        Seqn(Seq(inhaleInv, inhaleSecInv, inhaleLocked), Seq(invValVarDecl))(errT=NodeTrafo(a))
      }
      case r@Release(lt, lockExp, opAction) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValVarName = "$invVal$" + getFreshInt()
        val invValVarDecl = LocalVarDecl(invValVarName, lockSpec.t)()
        val invPerms = lockSpec.invariant.permissionsWithArgs(Seq(lockExp, invValVarDecl.localVar))
        val assertInvPerms = Assert(invPerms)()
        val exhaleInvPerms = Exhale(invPerms)()
        val valueDefinition = Inhale(lockSpec.invariant.pureWithArgs(Seq(lockExp, invValVarDecl.localVar)))()

        // either bottom or unchanged
        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(r.pos, r.info, lockSpecs.get(lt).get.t, NoTrafos)
        val bottomLockedPred = PredicateAccess(Seq(lockExp, bottomApp), lockedPredNames.get(lt).get)()
        val currentLockedPred = PredicateAccess(Seq(lockExp, invValVarDecl.localVar), lockedPredNames.get(lt).get)()
        val currentLockedPerm = CurrentPerm(currentLockedPred)()
        val fp = FullPerm()()

        val (actionChecks: Seq[Stmt], actionDecls: Seq[LocalVarDecl]) = opAction match {
          case None => {
            val hasCurrentLocked = PermGeCmp(currentLockedPerm, fp)()
            val toExhaleIfCurrent = PredicateAccessPredicate(currentLockedPred, fp)()
            val toExhaleIfBottom = And(PredicateAccessPredicate(bottomLockedPred, fp)(), lockSpec.secInv.withArgs(Seq(invValVarDecl.localVar)))()

            val lockedToExhale = CondExp(hasCurrentLocked, toExhaleIfCurrent, toExhaleIfBottom)()
            val exhaleLocked = Exhale(lockedToExhale)()
            val stmtSeq = Seq(exhaleLocked)
            (stmtSeq, Seq())
          }
          case Some((actionName, actionArg)) => {
            val action = lockSpec.actions.find(a => a.name == actionName).get
            // assert LowEvent
            val checkLowEvent = Assert(SIFLowEventExp()())()
            // assert perm(lock(lockExp)) > 0
            val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
            val hasLockPerm = PermGtCmp(CurrentPerm(lockPredAcc)(), NoPerm()())()
            val assertLockPerm = Assert(hasLockPerm)()
            // assert perm(guard(action, lockExp)) >= 1
            val guardPredAcc = PredicateAccess(Seq(lockExp), actionGuardNames.get(lt).get.get(actionName).get)()
            val hasGuardPerm = if (action.duplicable) PermGtCmp(CurrentPerm(guardPredAcc)(), NoPerm()())() else PermGeCmp(CurrentPerm(guardPredAcc)(), fp)()
            val assertGuardPerm = Assert(hasGuardPerm)()
            // var oldVal
            val oldValVarName = "$oldVal$" + getFreshInt()
            val oldValVarDecl = LocalVarDecl(oldValVarName, lockSpec.t)()
            // inhale forall v :: perm(locked(lockExp, v)) >= write ==> oldVal == v
            val vVar = LocalVarDecl("$v", lockSpec.t)()
            val oldVarEquality = EqCmp(vVar.localVar, oldValVarDecl.localVar)()
            val lockedOldPred = PredicateAccess(Seq(lockExp, vVar.localVar), lockedPredNames.get(lt).get)()
            val trigger = Trigger(Seq(lockedOldPred))()
            val oldVarImplication = Implies(PermGeCmp(CurrentPerm(lockedOldPred)(), fp)(), oldVarEquality)()
            val defineOldVar = Inhale(Forall(Seq(vVar), Seq(trigger), oldVarImplication)())()
            // exhale       actionPre(oldVal, arg)
            //              current == actionFunc(oldVal, arg) &&
            //              locked(lockExp, oldVal)
            val assertActionPre = Assert(action.pre.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg))()
            val actionNewVal = action.newVal.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg)
            val assertCurrentIsNewVal = Assert(EqCmp(actionNewVal, invValVarDecl.localVar)())()
            val actualLockedPred = PredicateAccess(Seq(lockExp, oldValVarDecl.localVar), lockedPredNames.get(lt).get)()
            val exhaleLocked = Exhale(PredicateAccessPredicate(actualLockedPred, fp)())()
            // inhale post(oldVal, arg, actionFunc(oldVal, arg))
            val retVal = action.returnVal.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg)
            val post = action.post.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg).replace(Result(action.retType)(), retVal)
            val inhalePost = Inhale(post)()
            val stmtSeq = Seq(checkLowEvent, assertLockPerm, assertGuardPerm, defineOldVar, assertActionPre, assertCurrentIsNewVal, exhaleLocked, inhalePost)
            (stmtSeq, Seq(oldValVarDecl))
          }
        }

        Seqn(Seq(assertInvPerms, valueDefinition, exhaleInvPerms) ++ actionChecks, Seq(invValVarDecl) ++ actionDecls)()
      }
      case Fork(m, token, args) => {
        val havocVar = LocalVarDecl("$havoctoken$" + getFreshInt(), Ref)()
        val havocToken = LocalVarAssign(token, havocVar.localVar)()
        val method = input.findMethod(m)
        var pres = method.pres
        for (i <- 0 until args.length){
          pres = pres.map(pre => pre.replace(method.formalArgs(i).localVar, args(i)))
        }
        val exhalePres = pres.map(pre => Exhale(pre)())
        val joinablePred = PredicateAccess(Seq(token), joinableNames.get(m).get)()
        val inhaleJoinable = Inhale(PredicateAccessPredicate(joinablePred, FullPerm()())())()
        Seqn(exhalePres ++ Seq(havocToken, inhaleJoinable), Seq(havocVar))()
      }
      case Join(m, resVars, token) => {
        val method = input.findMethod(m)
        val joinablePred = PredicateAccess(Seq(token), joinableNames.get(m).get)()
        val exhaleJoinable = Exhale(PredicateAccessPredicate(joinablePred, FullPerm()())())()
        val havocTargets = ListBuffer[LocalVarAssign]()
        val targetHavocVars = ListBuffer[LocalVarDecl]()
        val argPlaceholders = ListBuffer[LocalVarDecl]()
        var posts = method.posts
        for (i <- 0 until resVars.length){
          val newName = "$targethavoc$" + getFreshInt()
          val decl = LocalVarDecl(newName, method.formalReturns(i).typ)()
          targetHavocVars.append(decl)
          val assign = LocalVarAssign(resVars(i), decl.localVar)()
          havocTargets.append(assign)
          posts = posts.map(post => post.replace(method.formalReturns(i).localVar, resVars(i)))
        }
        for (i <- 0 until method.formalArgs.length){
          val newName = "$argPlaceholder$" + getFreshInt()
          val decl = LocalVarDecl(newName, method.formalArgs(i).typ)()
          argPlaceholders.append(decl)
          posts = posts.map(post => post.replace(method.formalArgs(i).localVar, decl.localVar))
        }
        val inhalePosts = posts.map(post => Inhale(post)())
        Seqn(Seq(exhaleJoinable) ++ havocTargets ++ inhalePosts, targetHavocVars ++ argPlaceholders)()
      }
      //case Threadtype() => Ref
      //case Locktype() => Ref
    }, Traverse.TopDown)

    println(res)
    val productRes = SIFExtendedTransformer.transform(res, false)
    productRes
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Failure(errors) => Failure(errors.map(e => if (e.isInstanceOf[AbstractVerificationError]) e.asInstanceOf[AbstractVerificationError].transformedError() else e))
      case Success => input
    }
  }
}
