package commutativity

import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.{ConsistencyError, VerificationResult}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps,show,text}


case class InvariantDef(params: Seq[LocalVarDecl], inv: Exp){
  def subnodes = Seq(inv) ++ params
}
case class LockAction(name: String, argType: Type, retType: Type, duplicable: Boolean, params: Seq[LocalVarDecl], newVal: Exp, returnVal: Exp, pre: Exp, post: Exp) {
  def subnodes = Seq(argType, retType, newVal, returnVal, pre, post) ++ params
}
case class Proof(proofType: String, actions: Seq[String], params: Seq[LocalVarDecl], body: Seqn) {
  def subnodes = Seq(body) ++ params
}

case class LockSpec(name: String, t: Type, invariant: InvariantDef, secInv: InvariantDef, actions: Seq[LockAction], proofs: Seq[Proof])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionMember  {
  override def extensionSubnodes: Seq[Node] = Seq(t) ++ invariant.subnodes ++ secInv.subnodes ++ (actions map (_.subnodes)).flatten ++ (proofs map (_.subnodes)).flatten
  override lazy val checkTransitively: Seq[ConsistencyError] = Seq()
  val scopedDecls : Seq[Declaration] = Seq()

  override def toString(): String = "I am lockspec " + name
}

case class PointsToPredicate(receiver: FieldAccess, perm: Exp, arg: Option[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(receiver, perm) ++ (if (arg.isDefined) Seq(arg.get) else Seq())
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class VarDefiningPointsToPredicate(receiver: FieldAccess, perm: Exp, varDecl: LocalVarDecl, conjunct: Option[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(receiver, perm, varDecl) ++ (if (conjunct.isDefined) Seq(conjunct.get) else Seq())
  def prettyPrint : PrettyPrintPrimitives#Cont = text("[") <> show(receiver) <+> (if (perm.isInstanceOf[FullPerm]) text("|->") else (text("|-[") <> show(perm) <> text("]->"))) <+> text("?") <> show(varDecl.localVar) <+> (if (conjunct.isDefined) text("&&") <+> show(conjunct.get) else text("")) <> text("]")
  override def verifyExtExp(): VerificationResult = ???
}

case class Joinable(method: String, e: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(e)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Lock(lockType: String, lockRef: Exp, amount: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, amount)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Locked(lockType: String, lockRef: Exp, value: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, value)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Guard(lockType: String, guardName: String, lock: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lock)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}


// Statements
case class NewLock(lockType: String, target: LocalVar, fields: Seq[Field])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = ???
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
}

case class Fork(m: String, tokenVar: LocalVar, args: Seq[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = ???
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
}

case class Join(m: String, resVars: Seq[LocalVar], tokenArg: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = ???
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
}

case class Release(lockType: String, lockExp: Exp, action: Option[(String, Exp)])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = ???
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
}

case class Acquire(lockType: String, lockExp: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = ???
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
}

case class Locktype() extends ExtensionType {
  override def isConcrete: Boolean = true

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = this

  override def toString() = "Lock"
}

case class Threadtype() extends ExtensionType {
  override def isConcrete: Boolean = true

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = this

  override def toString(): String = "Thread"
}