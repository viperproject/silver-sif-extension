package commutativity

import viper.silver.ast.utility.{Expressions, QuantifiedPermissions}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{And, Assert, Bool, CondExp, CurrentPerm, EqCmp, ErrTrafo, Exhale, Exp, FieldAccess, FieldAccessPredicate, Forall, FullPerm, FuncApp, Function, Implies, Inhale, Let, LocalVar, LocalVarDecl, Method, MethodCall, NoPerm, NoTrafos, NodeTrafo, Perm, PermGeCmp, PermGtCmp, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Result, Seqn, Stmt, Trafos, TrueLit, Type, WildcardPerm}
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.sif.{SIFExtendedTransformer, SIFLowEventExp}
import viper.silver.verifier._
import viper.silver.verifier.errors.PostconditionViolated

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
  override lazy val newStmtAtStart = P(fork | join | newLock | acquire | release | share)

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

  lazy val share: P[PShare] = P("share" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (lockType, (arg, value)) => PShare(lockType, arg, value)
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
  lazy val pointsToPred : P[PExp] = P(pointsToPred1 | pointsToPred2)
  lazy val pointsToPred1 : P[PSimplePointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ (anyVal | atom) ~ "]").map{
    case (fa, p, rhs) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PSimplePointsToPredicate(fa, perm, rhs)
    }
  }
  lazy val pointsToPred2 : P[PVarDefiningPointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ "?" ~ idndef ~ "&&" ~ exp ~ "]").map{
    case (fa, p, id, body) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PVarDefiningPointsToPredicate(fa, perm, PLet(fa, PLetNestedScope(PFormalArgDecl(id, PUnknown()), body)))
    }
  }

  lazy val anyVal : P[PExp] = P("_").map{case _ => PAnyVal()}
  lazy val joinable : P[PJoinable] = P(keyword("joinable") ~/ "[" ~ idnuse ~ "]" ~ parens(exp.rep(min=1, sep=","))).map{
    case (method, args) => PJoinable(method, args(0), args.tail)
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
    val lockedFuncNames = mutable.HashMap[String, String]()
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
        lockedFuncNames.update(name, "$lockedfunc$" + name)
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
    val newMethods = ListBuffer[Method]()
    val havocNames = mutable.HashMap[Type, String]()
    val joinableNames = mutable.HashMap[String, String]()
    val joinablePreds = mutable.HashMap[String, Predicate]()
    val joinableFunctions = mutable.HashMap[String, ListBuffer[Function]]()
    for (m <- input.methods) {
      val joinableName = "$joinable$" + m.name
      joinableNames.update(m.name, joinableName)
      val receiver = LocalVarDecl("$rec", Ref)()
      val joinablePred = Predicate(joinableName, Seq(receiver), None)()
      joinablePreds.update(m.name, joinablePred)
      val funcs = ListBuffer[Function]()
      joinableFunctions.update(m.name, funcs)
      val predAcc = PredicateAccess(Seq(receiver.localVar), joinableName)()
      val pred = PredicateAccessPredicate(predAcc, FullPerm()())()
      for (arg <- m.formalArgs) {
        val funcName = "$joinable$" + m.name + "$" + arg.name
        val joinableFunc = Function(funcName, Seq(receiver), arg.typ, Seq(pred), Seq(), None)()
        funcs.append(joinableFunc)
      }
      val name = "$$havoc$" + getFreshInt()
      havocNames.update(Ref, name)
      val resVar = LocalVarDecl(name + "$res", Ref)()
      val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
      newMethods.append(newMethod)
      for (arg <- m.formalReturns) {
        if (!havocNames.contains(arg.typ)){
          val name = "$$havoc$" + getFreshInt()
          havocNames.update(arg.typ, name)
          val resVar = LocalVarDecl(name + "$res", arg.typ)()
          val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
          newMethods.append(newMethod)
        }
      }
    }
    val lockPreds = lockPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedPreds = lockedPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedFuncs = lockedFuncNames.map(e => Function(e._2, Seq(LocalVarDecl("$rec", Ref)()), lockSpecs.get(e._1).get.t, Seq(PredicateAccessPredicate(PredicateAccess(Seq(LocalVar("$rec", Ref)()), lockedPredNames.get(e._1).get)(), FullPerm()())()), Seq(), None)())
    val guardPreds = actionGuardNames.map(ls => ls._2.map(a => Predicate(a._2, Seq(LocalVarDecl("$rec", Ref)()), None)())).flatten
    val bottomFuncs = bottomFuncNames.map(n => Function(n._2, Seq(), lockSpecs.get(n._1).get.t, Seq(), Seq(), None)())


    val newPredicates : Seq[Predicate] = input.predicates ++ joinablePreds.values ++ lockPreds ++ lockedPreds ++ guardPreds
    val newFunctions : Seq[Function] = input.functions ++ bottomFuncs ++ lockedFuncs ++ joinableFunctions.values.flatten

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
        val uniquenessTrafo = ErrTrafo({
          case PostconditionViolated(node, _, reason, _) => UniquenessCheckFailed(name, node, reason)
        })
        val sameVal = EqCmp(udVal1.localVar, udVal2.localVar)(l.pos, errT=uniquenessTrafo)

        val udMethod = Method("$udCheck$" + name + "$" + getFreshInt(), Seq(udLockVar, udVal1, udVal2), Seq(), Seq(perms, valDef1, valDef2), Seq(sameVal), Some(Seqn(Seq(), Seq())()))(l.pos, errT=uniquenessTrafo)
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
          val preservationTrafo = ErrTrafo({
            case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
          })
          val presPostcond = a.post.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar).replace(Result(a.retType)(), presRetVar.localVar)
          val presSecInvFinal = secInv.withArgs(Seq(presFinalVar.localVar))
          val presProof = proofs.find(p => p.proofType == "preservation" && p.actions.length == 1 && p.actions(0) == a.name)
          val presBody = presProof match {
            case None => Some(Seqn(Seq(), Seq())())
            case Some(p) => Some(p.body.replace(a.params(0).localVar, presOrigVar.localVar).replace(a.params(1).localVar, presArgVar.localVar))
          }
          val presPosts = Seq((presPostcond, a.post), (presSecInvFinal, secInv.inv)).map{case (p: Exp, po: Exp) => EqCmp(TrueLit()(), p)(a.pos, errT=Trafos(List({
            case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
          }), List(), Some(po)))}
          val presMethod = Method("$presCheck$" + getFreshInt(), Seq(presOrigVar, presArgVar, presFinalVar, presRetVar), Seq(), Seq(presSecInv, presPrecond, presFinalValEq, presRetValEq), presPosts, presBody)(a.pos, errT=preservationTrafo)
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
              val reorderingTrafo = ErrTrafo({
                case PostconditionViolated(node, _, reason, _) => ReorderingCheckFailed(a1.name, a2.name, node, reason)
              })
              val reoOpt2Pre1: Exp = a1.pre.replace(a1.params(0).localVar, reoOrigDecl.localVar).replace(a1.params(1).localVar, reoArg1Decl.localVar)
              val reoOpt2TmpDef = EqCmp(reoTmpOpt2Decl.localVar, a1.newVal.replace(a1.params(0).localVar, reoOrigDecl.localVar).replace(a1.params(1).localVar, reoArg1Decl.localVar))(a1.pos, errT=reorderingTrafo)
              val reoOpt2Pre2 = a2.pre.replace(a2.params(0).localVar, reoTmpOpt2Decl.localVar).replace(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt2Pre2Impl = Implies(reoOpt2TmpDef, reoOpt2Pre2)(a1.pos, errT=reorderingTrafo)

              val reoName = "$reoCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
              val reoParams = Seq(reoOrigDecl, reoArg1Decl, reoArg2Decl, reoTmpOpt1Decl, reoTmpOpt2Decl)
              val reoPres = Seq(reoOrigSecInv, reoOpt1Pre2, reoOpt1TmpDef, reoOpt1Pre1)
              val reoPosts = Seq((reoOpt2Pre1, a1.pre), (reoOpt2Pre2Impl, a2.pre)).map{case (p, po) => EqCmp(TrueLit()(), p)(a1.pos, errT=Trafos(List({
                case PostconditionViolated(node, _, reason, _) => ReorderingCheckFailed(a1.name, a2.name, node, reason)
              }), List(), Some(po)))}

              val reoProof = proofs.find(p => p.proofType == "reordering" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val reoBody = if (reoProof.isDefined){
                reoProof.get.body.replace(reoProof.get.params(0).localVar, reoOrigDecl.localVar).replace(reoProof.get.params(1).localVar, reoArg1Decl.localVar).replace(reoProof.get.params(2).localVar, reoArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val reoMethod = Method(reoName, reoParams, Seq(), reoPres, reoPosts, Some(reoBody))(a1.pos, errT=reorderingTrafo)
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
              val commutativityTrafo = ErrTrafo({
                case PostconditionViolated(node, _, reason, _) => CommutativityCheckFailed(a1.name, a2.name, node, reason)
              })
              val commCheckSecInv = secInv.withArgs(Seq(commFinalDecl.localVar))
              val commCheckPostA1 = a1.post.replace(a1.params(0).localVar, commOrig1Decl.localVar).replace(a1.params(1).localVar, commArg1Decl.localVar).replace(Result(a1.retType)(), commRet1Decl.localVar)
              val commCheckPostA2 = a2.post.replace(a2.params(0).localVar, commOrig2Decl.localVar).replace(a2.params(1).localVar, commArg2Decl.localVar).replace(Result(a2.retType)(), commRet2Decl.localVar)


              val commName = "$commCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
              val commParams = Seq(commOrigDecl, commFinalDecl, commChoiceDecl, commOrig1Decl, commOrig2Decl, commArg1Decl, commArg2Decl, commRes1Decl, commRes2Decl, commRet1Decl, commRet2Decl)
              val commPres = Seq(commPreA1, commPreA2, commOrigSecInv, commResA1, commResA2, commRetA1, commRetA2, commOptions)
              val commPosts = Seq((commCheckSecInv, secInv.inv), (commCheckPostA1, a1.post), (commCheckPostA2, a2.post)).map{case (p, po) => EqCmp(TrueLit()(), p)(a1.pos, errT=Trafos(List({
                case PostconditionViolated(node, _, reason, _) => CommutativityCheckFailed(a1.name, a2.name, node, reason)
              }), List(), Some(po)))}

              val commProof = proofs.find(p => p.proofType == "commutativity" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val commBody = if (commProof.isDefined){
                commProof.get.body.replace(commProof.get.params(0).localVar, commOrigDecl.localVar).replace(commProof.get.params(1).localVar, commArg1Decl.localVar).replace(commProof.get.params(2).localVar, commArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val commMethod = Method(commName, commParams, Seq(), commPres, commPosts, Some(commBody))(a1.pos, errT=commutativityTrafo)
              newMethods.append(commMethod)
            }
          }
        }
      }
    }

    val withAdded = input.copy(extensions = Seq(), predicates = newPredicates, functions = newFunctions, methods = newMethods)(input.pos, input.info, input.errT)

    val res = withAdded.transform({
      case pt@PointsToPredicate(fa, p, None) => FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt))
      case pt@PointsToPredicate(fa, p, Some(e)) => And(FieldAccessPredicate(fa, p)(), EqCmp(fa, e)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, Some(b)) => And(FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt)), Let(v, fa, b)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, None) => FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt))
      case pt@Joinable(m, e, args) => {
        val pa = PredicateAccess(Seq(e), joinableNames.get(m).get)()
        val pap = PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT=NodeTrafo(pt))
        var res : Exp =  pap
        for (i <- 0 until args.length){
          val funcApp = EqCmp(FuncApp(joinableFunctions.get(m).get(i), Seq(e))(pt.pos, errT=NodeTrafo(pt)), args(i))(pt.pos, errT=NodeTrafo(pt))
          res = And(res, funcApp)(pt.pos, errT=NodeTrafo(pt))
        }
        res
      }
      case pt@Lock(lt, r, amount) => {
        val pa = PredicateAccess(Seq(r), lockPredNames.get(lt).get)()
        PredicateAccessPredicate(pa, amount)(pt.pos, errT=NodeTrafo(pt))
      }
      case l@Locked(lt, r, value) => {
        val pt = l
        val pa = PredicateAccess(Seq(r), lockedPredNames.get(lt).get)()
        val pap = PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT=NodeTrafo(pt))
        val funcApp = FuncApp(lockedFuncNames.get(lt).get, Seq(r))(l.pos, l.info, lockSpecs.get(lt).get.t, NoTrafos)
        val eq = EqCmp(funcApp, value)(pt.pos, errT=NodeTrafo(pt))
        And(pap, eq)(pt.pos, errT=NodeTrafo(pt))
      }
      case pt@Guard(lt, g, lock) => {
        val action = lockSpecs.get(lt).get.actions.find(a => a.name == g).get
        val pa = PredicateAccess(Seq(lock), actionGuardNames.get(lt).get.get(g).get)()
        PredicateAccessPredicate(pa, if (action.duplicable) WildcardPerm()() else FullPerm()())(pt.pos, errT=NodeTrafo(pt))
      }
      case nl@NewLock(lt, target, fields) => {
        val pt = nl
        val lockSpec = lockSpecs.get(lt).get
        val newStmt = MethodCall(havocNames.get(Ref).get, Seq(), Seq(target))(nl.pos, nl.info, NoTrafos)
        val fp = FullPerm()()
        val fieldPermInhales = ListBuffer[Inhale]()
        for (field <- fields) {
          val predAcc = FieldAccessPredicate(FieldAccess(target, field)(), fp)()
          fieldPermInhales.append(Inhale(predAcc)())
        }
        val lockPredAcc = PredicateAccess(Seq(target), lockPredNames.get(lt).get)()
        val lockPred = PredicateAccessPredicate(lockPredAcc, fp)()
        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(nl.pos, nl.info, lockSpecs.get(lt).get.t, NoTrafos)
        val lockedPredAcc = PredicateAccess(Seq(target), lockedPredNames.get(lt).get)()
        val lockedPred = PredicateAccessPredicate(lockedPredAcc, fp)(pt.pos, errT=NodeTrafo(pt))
        val lockedValue = FuncApp(lockedFuncNames.get(lt).get, Seq(target))(nl.pos, nl.info, lockSpec.t, NoTrafos)
        val lockedBottom = EqCmp(lockedValue, bottomApp)(pt.pos, errT=NodeTrafo(pt))
        val inhale = Inhale(And(lockPred, And(lockedPred, lockedBottom)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
        val guardInhales = ListBuffer[Inhale]()
        val guardNames = actionGuardNames.get(lt).get
        for (a <- lockSpec.actions){
          val pa = PredicateAccess(Seq(target), guardNames.get(a.name).get)()
          guardInhales.append(Inhale(PredicateAccessPredicate(pa, fp)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt)))
        }
        Seqn(Seq(newStmt, inhale) ++ fieldPermInhales ++ guardInhales, Seq())(pt.pos, errT=NodeTrafo(pt))
      }
      case a@Acquire(lt, lockExp) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValVarName = "$invVal$" + getFreshInt()
        val invValVarDecl = LocalVarDecl(invValVarName, lockSpec.t)()
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val lockPerm = CurrentPerm(lockPredAcc)()
        // check lock type
        val errTrafo = NodeTrafo(Lock(lt, lockExp, AnyVal(Perm)())(a.pos))
        val anyLockPerm = PermGtCmp(lockPerm, NoPerm()())(a.pos, errT=errTrafo)
        val checkSomeLockPerm = Assert(anyLockPerm)(a.pos)
        // inhale inv
        val inv = lockSpec.invariant.withArgs(Seq(lockExp, invValVarDecl.localVar))
        val inhaleInv = Inhale(inv)()
        // if full lock perm inhale secinv
        val secInv = lockSpec.secInv.withArgs(Seq(invValVarDecl.localVar))
        val hasFullLockPerm = PermGeCmp(lockPerm, FullPerm()())()
        val inhaleSecInv = Inhale(Implies(hasFullLockPerm, secInv)())()
        // inhale locked
        val lockedAccess = PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)()
        val lockedPredAcc = PredicateAccessPredicate(lockedAccess, FullPerm()())()
        val lockedValFuncApp = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(a.pos, a.info, lockSpec.t, NoTrafos)
        val inhaleLocked = Inhale(And(lockedPredAcc, EqCmp(lockedValFuncApp, invValVarDecl.localVar)())())()
        Seqn(Seq(checkSomeLockPerm, inhaleInv, inhaleSecInv, inhaleLocked), Seq(invValVarDecl))(errT=NodeTrafo(a))
      }
      case s@Share(lt, lockExp, lockVal) => {
        val lockSpec = lockSpecs.get(lt).get
        val invPerms = lockSpec.invariant.withArgs(Seq(lockExp, lockVal))
        val assertInv = Assert(invPerms)(s.pos)
        val exhaleInv = Exhale(invPerms)(s.pos)
        val lockedTrafo = NodeTrafo(Locked(lt, lockExp, AnyVal(lockSpec.t)())(s.pos))
        val fp = FullPerm()()
        val lockedPred = PredicateAccessPredicate(PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)(), fp)(s.pos, errT=lockedTrafo)
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val lockTrafo = NodeTrafo(Lock(lt, lockExp, AnyVal(Perm)())(s.pos))
        val hasLockPerm = PermGtCmp(CurrentPerm(lockPredAcc)(), NoPerm()())(s.pos, errT=lockTrafo)
        val assertLockPerm = Assert(hasLockPerm)(s.pos)
        val lockedVal = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(s.pos, s.info, lockSpec.t, NoTrafos)
        val assertLocked = Assert(lockedPred)(s.pos)
        val exhaleLocked = Exhale(lockedPred)(s.pos)

        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(s.pos, s.info, lockSpecs.get(lt).get.t, NoTrafos)
        val bottomTrafo = NodeTrafo(Locked(lt, lockExp, BottomVal(lockSpec.t)(s.pos))(s.pos))
        val assertLockedBottom = Assert(EqCmp(lockedVal, bottomApp)(s.pos, errT=bottomTrafo))(s.pos)
        val assertSecInv = Assert(lockSpec.secInv.withArgs(Seq(lockVal)))(s.pos)
        Seqn(Seq(assertInv, assertLocked, assertLockPerm, assertLockedBottom, assertSecInv, exhaleInv, exhaleLocked), Seq())(s.pos)
      }
      case r@Release(lt, lockExp, opAction) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValDummyName = "$invVal$" + getFreshInt()
        val invValDummyDecl = LocalVarDecl(invValDummyName, lockSpec.t)()
        val invPerms = lockSpec.invariant.permissionsWithArgs(Seq(lockExp, invValDummyDecl.localVar))
        val assertInvPerms = Assert(invPerms)(r.pos)
        val exhaleInvPerms = Exhale(invPerms)(r.pos)

        // either bottom or unchanged
        val fp = FullPerm()()
        val lockedTrafo = NodeTrafo(Locked(lt, lockExp, AnyVal(lockSpec.t)())(r.pos))
        val lockedPred = PredicateAccessPredicate(PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)(), fp)(r.pos, errT=lockedTrafo)
        val lockedVal = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(r.pos, r.info, lockSpec.t, NoTrafos)
        val assertLocked = Assert(lockedPred)(r.pos)
        val exhaleLocked = Exhale(lockedPred)(r.pos)
        // assert perm(lock(lockExp)) > 0
        val lockTrafo = NodeTrafo(Lock(lt, lockExp, AnyVal(Perm)())(r.pos))
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val hasLockPerm = PermGtCmp(CurrentPerm(lockPredAcc)(), NoPerm()())(r.pos, errT=lockTrafo)
        val assertLockPerm = Assert(hasLockPerm)(r.pos)
        var assertInvPure : Assert = null


        val (actionChecks: Seq[Stmt], actionDecls: Seq[LocalVarDecl]) = opAction match {
          case None => {
            assertInvPure = Assert(lockSpec.invariant.pureWithArgs(Seq(lockExp, lockedVal)))(r.pos)
            (Seq(), Seq())
          }
          case Some((actionName, actionArg)) => {
            val action = lockSpec.actions.find(a => a.name == actionName).get
            // assert LowEvent
            val checkLowEvent = Assert(SIFLowEventExp()())(r.pos)
            // assert perm(guard(action, lockExp)) >= 1
            val guardTrafo = NodeTrafo(Guard(lt, actionName, lockExp)(r.pos))
            val guardPredAcc = PredicateAccess(Seq(lockExp), actionGuardNames.get(lt).get.get(actionName).get)()
            val hasGuardPerm = if (action.duplicable) PermGtCmp(CurrentPerm(guardPredAcc)(), NoPerm()())(r.pos, errT=guardTrafo) else PermGeCmp(CurrentPerm(guardPredAcc)(), fp)(r.pos, errT=guardTrafo)
            val assertGuardPerm = Assert(hasGuardPerm)(r.pos)
            // var oldVal
            val oldValVarName = "$oldVal$" + getFreshInt()
            val oldValVarDecl = LocalVarDecl(oldValVarName, lockSpec.t)()
            val oldVarDef = Inhale(EqCmp(oldValVarDecl.localVar, lockedVal)())(r.pos)
            // exhale       actionPre(oldVal, arg)
            //              current == actionFunc(oldVal, arg) &&
            //              locked(lockExp, oldVal)
            val assertActionPre = Assert(action.pre.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg))(r.pos)
            val actionNewVal = action.newVal.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg)
            assertInvPure = Assert(lockSpec.invariant.pureWithArgs(Seq(lockExp, actionNewVal)))(r.pos)
            // inhale post(oldVal, arg, actionFunc(oldVal, arg))
            val retVal = action.returnVal.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg)
            val post = action.post.replace(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg).replace(Result(action.retType)(), retVal)
            val inhalePost = Inhale(post)(r.pos)
            val stmtSeq = Seq(checkLowEvent, assertGuardPerm, oldVarDef, assertActionPre, inhalePost)
            (stmtSeq, Seq(oldValVarDecl))
          }
        }

        Seqn(Seq(assertInvPerms, assertLocked, assertLockPerm) ++ actionChecks ++ Seq(assertInvPure, exhaleInvPerms, exhaleLocked), Seq(invValDummyDecl) ++ actionDecls)(r.pos)
      }
      case f@Fork(m, token, args) => {
        val havocToken = MethodCall(havocNames.get(Ref).get, Seq(), Seq(token))(f.pos, f.info, NoTrafos)
        val method = input.findMethod(m)
        var pres = method.pres
        for (i <- 0 until args.length){
          pres = pres.map(pre => pre.replace(method.formalArgs(i).localVar, args(i)))
        }
        val exhalePres = pres.map(pre => Exhale(pre)(f.pos))
        var joinablePred : Exp = PredicateAccessPredicate(PredicateAccess(Seq(token), joinableNames.get(m).get)(), FullPerm()())(f.pos)
        for (i <- 0 until args.length) {
          val funcApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))(f.pos)
          val eq = EqCmp(funcApp, args(i))(f.pos)
          joinablePred = And(joinablePred, eq)(f.pos)
        }
        val inhaleJoinable = Inhale(joinablePred)(f.pos)
        Seqn(exhalePres ++ Seq(havocToken, inhaleJoinable), Seq())(f.pos)
      }
      case j@Join(m, resVars, token) => {
        val method = input.findMethod(m)
        val havocTargets = ListBuffer[MethodCall]()
        var posts = method.posts
        val joinablePred = PredicateAccess(Seq(token), joinableNames.get(m).get)()
        val joinableTrafo = NodeTrafo(Joinable(m, token, method.formalArgs.map(fa => AnyVal(fa.typ)()))(j.pos))
        val assertJoinable = Assert(PredicateAccessPredicate(joinablePred, FullPerm()())(j.pos, errT=joinableTrafo))(j.pos)
        for (i <- 0 until resVars.length){
          val havocCall =  MethodCall(havocNames.get(resVars(i).typ).get, Seq(), Seq(resVars(i)))(j.pos, j.info, NoTrafos)
          havocTargets.append(havocCall)
          posts = posts.map(post => post.replace(method.formalReturns(i).localVar, resVars(i)))
        }
        for (i <- 0 until method.formalArgs.length){
          val argFuncApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))()
          posts = posts.map(post => post.replace(method.formalArgs(i).localVar, argFuncApp))
        }
        val exhaleJoinable = Exhale(PredicateAccessPredicate(joinablePred, FullPerm()())())()
        val inhalePosts = posts.map(post => Inhale(post)())
        Seqn(Seq(assertJoinable) ++ havocTargets ++ inhalePosts ++ Seq(exhaleJoinable), Seq())(j.pos)
      }
      //case Threadtype() => Ref
      //case Locktype() => Ref
    }, Traverse.TopDown)


    val productRes = SIFExtendedTransformer.transform(res, false)
    println(productRes)
    val qpTransformed = productRes.transform({
      case fa: Forall => {
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      }
    })
    qpTransformed
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Failure(errors) => Failure(errors.map(e => if (e.isInstanceOf[AbstractVerificationError]) e.asInstanceOf[AbstractVerificationError].transformedError() else e))
      case Success => input
    }
  }
}
