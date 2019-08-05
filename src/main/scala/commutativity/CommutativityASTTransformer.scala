package commutativity

import viper.silver.ast._
import viper.silver.sif.SIFExtendedTransformer

import scala.collection.mutable

object CommutativityASTTransformer {

  val usedNames = new mutable.HashSet[String]()

  def freshName(str: String) : String = {
    if (!usedNames.contains(str)){
      usedNames.add(str)
      str
    }else{
      var index = 0
      while (usedNames.contains(str + index)){
        index += 1
      }
      val res = str + index
      usedNames.add(res)
      res
    }
  }

  def transformStatement(s: Stmt) : Stmt = {
    s match {
      case s => s
    }
  }

  def transformExpression(e: Exp) : Exp = {
    e match {
      case e => e
    }
  }

  def transformLockspec(l: LockSpec) : (Seq[Method], Function, Seq[Predicate]) = {
    val lockRefDecl = LocalVarDecl("l$", Ref)(l.pos)
    val isLockName = freshName("lock" + l.name)
    val isLockPred = Predicate(isLockName, Seq(lockRefDecl), None)(l.pos)
    val isLockedName = freshName("locked" + l.name)
    val lockValDecl = LocalVarDecl("v$", l.t)(l.pos)
    val isLockedPred = Predicate(isLockedName, Seq(lockRefDecl, lockValDecl), None)(l.pos)

    val guardPreds = new mutable.HashMap[String, Predicate]()
    val preservationChecks = new mutable.HashMap[String, Method]()
    val commutativityChecks = new mutable.HashMap[(String, String), Method]()
    val reorderingChecks = new mutable.HashMap[(String, String), Method]()
    val preConds = new mutable.HashMap[String, (Exp, Exp)=>Exp]()
    val postConds = new mutable.HashMap[String, (Exp, Exp)=>Exp]()
    val invariants = new mutable.HashMap[String, (Exp, Exp)=>Exp]() //
    val secInvariants = new mutable.HashMap[String, (Exp, Exp)=>Exp]()

    (Seq(), null, Seq())
  }

  def transformMethod(m: Method) : Method = {
    m
  }

  def transformProgram(p: Program) : Program = {
    // initialize used Names
    // transform lock specs
    val newProgram : Program = ???

    SIFExtendedTransformer.transform(newProgram, false)
  }

  def permissionsOnly(e: Exp) : Exp = {
    e match {
      case And(e1, e2) => And(permissionsOnly(e1), permissionsOnly(e2))(e.pos)
      case Implies(lhs, rhs) => Implies(lhs, permissionsOnly(rhs))(e.pos)
      case CondExp(cond, thn, els) => CondExp(cond, permissionsOnly(thn), permissionsOnly(els))(e.pos)
      case _ : FieldAccessPredicate => e
      case _ : PredicateAccessPredicate => e
      case Forall(vars, triffers, body) => Forall(vars, triffers, permissionsOnly(body))(e.pos)
      case Exists(vars, triffers, body) => Exists(vars, triffers, permissionsOnly(body))(e.pos)
      case Let(boundVar, exp, body) => Let(boundVar, exp, permissionsOnly(body))(e.pos)
      case _ => TrueLit()(e.pos)
    }
  }

  def valueStuffOnly(e: Exp) : Exp = {
    e.transform({
      case _: FieldAccessPredicate => TrueLit()()
      case _: PredicateAccessPredicate => TrueLit()()
    })
  }

  def replaceVarIncludingLet(e: Exp, v: LocalVar, replacement: Exp) : Exp = {
    e.transform({
      case LocalVar(name, _) if name == v.name => replacement
      case Let(boundVar, boundExp, body) if boundVar.name == v.name => Let(boundVar, boundExp, And(EqCmp(replacement, boundVar.localVar)(), body)())(e.pos)
    })
  }
}
