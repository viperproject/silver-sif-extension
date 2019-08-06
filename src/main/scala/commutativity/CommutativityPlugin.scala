package commutativity

import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{And, EqCmp, FieldAccessPredicate, FullPerm, FuncApp, Function, Inhale, Let, LocalVarDecl, Method, NewStmt, NoTrafos, NodeTrafo, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Seqn, WildcardPerm}
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractVerificationError, Failure, Success, VerificationResult}

import scala.collection.{Set, mutable}

class CommutativityPlugin extends ParserPluginTemplate with SilverPlugin {

  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  override lazy val newDeclAtEnd = P(lockSpec)
  override lazy val newExpAtStart = P(pointsToPred | joinable | low | locked | lock | guard)
  override lazy val newStmtAtStart = P(fork | join | newLock | acquire | release)

  lazy val fork : P[PFork] = P(idnuse ~ ":=" ~ "fork" ~/ idnuse ~ parens(actualArgList)).map{
    case (t, m, args) => PFork(m, t, args)
  }

  lazy val join : P[PJoin] = P((idnuse.rep(sep = ",") ~ ":=").? ~ "join" ~/ "[" ~ idnuse ~ "]" ~ exp).map{
    case (targets, m, token) => PJoin(m, if (targets.isDefined) targets.get else Seq(), token)
  }

  lazy val newLock: P[PNewLock] = P(idnuse ~ ":=" ~ "newLock" ~/ "[" ~ idnuse ~ "]" ~ parens(idnuse.rep(sep = ","))).map{
    case (target, lockType, fields) => PNewLock(lockType, target, fields)
  }

  lazy val acquire: P[PAcquire] = P("acquire" ~/ "[" ~ idnuse ~ "]" ~ exp).map{
    case (lockType, arg) => PAcquire(lockType, arg)
  }

  lazy val release: P[PRelease] = P("release" ~/ "[" ~ idnuse ~ "]" ~ exp ~ ("with" ~/ idnuse ~ parens(exp)).?).map{
    case (lockType, arg, act) => PRelease(lockType, arg, act)
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
  lazy val proof : P[PProof] = P("proof" ~/ proofType ~ parens(idnuse.rep(sep=",")) ~ parens(idndef.rep(sep=",")) ~ "{" ~  stmt ~ "}").map{
    case (ptype, actions, params, pstmt) => PProof(ptype, actions, params, pstmt)
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
  lazy val locked : P[PLocked] = P(keyword("locked") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLocked(ltype, argLock, argVal)
  }
  lazy val lock : P[PLock] = P(keyword("lock") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLock(ltype, argLock, argVal)
  }
  lazy val guard : P[PGuard] = P(keyword("guard") ~/ "[" ~ idnuse ~ "]" ~ parens(idnuse ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PGuard(ltype, argLock, argVal)
  }

  override lazy val extendedKeywords = Set("lockType", "action", "invariant", "secInvariant", "proof", "reordering", "commutativity", "preservation", "locked", "lock", "guard", "joinable", "duplicable", "unique")

  override def beforeParse(input: String, isImported: Boolean): String = {
    println("beforeparse")
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewExpAtStart(newExpAtStart)
    ParserExtension.addNewKeywords(extendedKeywords)
    ParserExtension.addNewStmtAtStart(newStmtAtStart)
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    input.transform({
      case PDomainType(name, args) if name.name == "Lock" && args.length == 0 => PLocktype()
      case PDomainType(name, args) if name.name == "Thread" && args.length == 0 => PThreadtype()
    })()
  }

  override def beforeConsistencyCheck(input: Program): Program = {
    println("beforeconscheck")

    val lockSpecs = mutable.HashMap[String, LockSpec]()
    var lockMethods : Seq[Method] = Seq()
    val lockPredNames = mutable.HashMap[String, String]()
    val lockedPredNames = mutable.HashMap[String, String]()
    val actionGuardNames = mutable.HashMap[String, mutable.HashMap[String, String]]()
    val bottomFuncNames = mutable.HashMap[String, String]()

    input.extensions.foreach{
      case l@LockSpec(name, t, inv, secInv, actions, proofs) => {
        lockSpecs.update(name, l)
        lockPredNames.update(name, "$lockpred$" + name)
        lockedPredNames.update(name, "$lockedpred$" + name)
        bottomFuncNames.update(name, "$bottomfunc$" + name)
        val guardNames = mutable.HashMap[String, String]()
        actionGuardNames.update(name, guardNames)
        for (a <- actions){
          guardNames.update(a.name, "$guard$"+name+"$"+a.name)
        }
      }
    }

    val joinableNames: Map[String, String] = input.methods.map(m=> m.name->("$joinable$" + m.name)).toMap


    val joinablePreds = joinableNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockPreds = lockPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedPreds = lockedPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)(), LocalVarDecl("$val", lockSpecs.get(n._1).get.t)()), None)())
    val guardPreds = actionGuardNames.map(ls => ls._2.map(a => Predicate(a._2, Seq(LocalVarDecl("$rec", Ref)()), None)())).flatten

    val bottomFuncs = bottomFuncNames.map(n => Function(n._2, Seq(), lockSpecs.get(n._1).get.t, Seq(), Seq(), None)())

    val res = input.transform({
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
        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq(target))(nl.pos, nl.info, lockSpecs.get(lt).get.t, NoTrafos)
        val lockedPredAcc = PredicateAccess(Seq(target, bottomApp), lockedPredNames.get(lt).get)()
        val lockedPred = PredicateAccessPredicate(lockedPredAcc, fp)()
        val inhale = Inhale(And(lockPred, lockedPred)())()
        Seqn(Seq(newStmt, inhale), Seq())()
      }
      case Threadtype() => Ref
      case Locktype() => Ref
    }, Traverse.TopDown)

    val newPredicates = input.predicates ++ joinablePreds ++ lockPreds ++ lockedPreds ++ guardPreds
    val newFunctions = input.functions ++ bottomFuncs

    val finalRes = res.copy(extensions = Seq(), predicates = newPredicates, functions = newFunctions)(input.pos, input.info, input.errT)
    println(finalRes)
    finalRes
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Failure(errors) => Failure(errors.map(e => if (e.isInstanceOf[AbstractVerificationError]) e.asInstanceOf[AbstractVerificationError].transformedError() else e))
      case Success => input
    }
  }
}
