package commutativity

import viper.silver.verifier.{AbstractVerificationError, ErrorMessage, ErrorReason}
import viper.silver.verifier.errors.ErrorNode

case class CommutativityCheckFailed(a1: String, a2: String, offendingNode: ErrorNode, reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "commutativity.check.failed"
  val text: String = "Abstract commutativity check for actions " + a1 + " and "+ a2 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    CommutativityCheckFailed(a1, a2, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = CommutativityCheckFailed(a1, a2, offendingNode, r)
}

case class ReorderingCheckFailed(a1: String, a2: String, offendingNode: ErrorNode, reason: ErrorReason,
                                 override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "reordering.check.failed"
  val text: String = "Reordering check for actions " + a1 + " and "+ a2 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    ReorderingCheckFailed(a1, a2, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = ReorderingCheckFailed(a1, a2, offendingNode, r)
}

case class PreservationCheckFailed(a1: String, offendingNode: ErrorNode, reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "preservation.check.failed"
  val text: String = "Security invariant preservation and postcondition check for action " + a1 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    PreservationCheckFailed(a1, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = PreservationCheckFailed(a1, offendingNode, r)
}

case class UniquenessCheckFailed(lt: String, offendingNode: ErrorNode, reason: ErrorReason,
                                   override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "uniqueness.check.failed"
  val text: String = "Invariant value uniqueness check for lock type " + lt + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    UniquenessCheckFailed(lt, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = UniquenessCheckFailed(lt, offendingNode, r)
}

