package commutativity

import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult

case class InvariantDef(params: Seq[LocalVarDecl], inv: Exp)
case class LockAction(name: String, argType: Type, retType: Type, duplicable: Boolean, params: Seq[LocalVarDecl], newVal: Exp, returnVal: Exp, pre: Exp, post: Exp)
case class Proof(proofType: String, actions: Seq[String], params: Seq[LocalVarDecl], body: Seqn)

case class LockSpec(name: String, t: Type, invariant: InvariantDef, secInv: InvariantDef, actions: Seq[LockAction], proofs: Seq[Proof])(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionMember  {
  override def extensionSubnodes: Seq[Node] = ???
  val scopedDecls : Seq[Declaration] = ???
}

case class Joinable(method: String, e: Exp)(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(e)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Lock(lockType: String, lockRef: Exp, amount: Exp)(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, amount)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Locked(lockType: String, lockRef: Exp, value: Exp)(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, value)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}

case class Guard(lockType: String, guardName: String, amount: Exp)(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(amount)
  def prettyPrint : PrettyPrintPrimitives#Cont = ???
  override def verifyExtExp(): VerificationResult = ???
}