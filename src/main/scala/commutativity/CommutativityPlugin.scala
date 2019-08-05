package commutativity

import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.collection.Set

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

  lazy val pointsToPred : P[PPointsToPredicate] = P("[" ~ fieldAcc ~ "|->" ~ pointsToRhs ~ "]").map{case (fa, rhs) => PPointsToPredicate(fa, rhs)}
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

}
