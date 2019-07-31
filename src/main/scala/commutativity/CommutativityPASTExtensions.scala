package commutativity

import viper.silver.parser._


case class PPointsToPredicate(receiver: PFieldAccess, arg: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PDefiningVarRef(id: PIdnDef) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PAnyVal() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PInvariantDef(arg: Seq[PIdnDef], inv: PExp) {}
case class PLockActionDecl(name: PIdnDef, argType: PType, retType: PType, duplicable: Boolean)
case class PLockActionDef(name: PIdnUse, args: Seq[PIdnDef], newVal: PExp, returnVal: PExp, pre: PExp, post: PExp)
case class PProof(proofType: String, actions: Seq[PIdnUse], params: Seq[PIdnDef], body: PStmt)

case class PLockSpec(name: PIdnDef, t: PType, invariant: PInvariantDef, secInv: PInvariantDef, actionList: Seq[PLockActionDecl], actions: Seq[PLockActionDef], proofs: Seq[PProof]) extends PExtender {
}

case class PLow(e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PJoinable(method: PIdnUse, e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PLock(lockType: PIdnUse, lockRef: PExp, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PLocked(lockType: PIdnUse, lockRef: PExp, value: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}

case class PGuard(lockType: PIdnUse, guardName: PIdnUse, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???
}