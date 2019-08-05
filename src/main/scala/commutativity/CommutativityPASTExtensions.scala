package commutativity

import viper.silver.ast._
import viper.silver.parser._
import viper.silver.sif.SIFLowExp

import scala.collection.mutable.ListBuffer


case class PPointsToPredicate(receiver: PFieldAccess, arg: PNode) extends PExtender with PExp {
  println("points to predicate")

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.checkTopTyped(receiver, None)
    println(" just type checked ")
    println(receiver.typ)
    println(receiver.rcv)
    println(receiver.idnuse.decl)
    println(receiver.rcv.asInstanceOf[PIdnUse].decl)
    arg match {
      case _:PAnyVal => None
      case n@PLetNestedScope(v, b) =>  {
        val oldNs = t.curMember
        v.typ = receiver.typ
        t.curMember = n
        t.checkInternal(b)
        t.curMember = oldNs
      }
      case _ => {
        t.checkTopTyped(arg.asInstanceOf[PExp], Some(receiver.typ))
      }
    }
    None
  }
  override def namecheck(n: NameAnalyser) = ???
  override def translateExp(t: Translator): Exp = {
    println("now translating")
    println(receiver.typ)
    println(receiver.rcv)
    println(receiver.idnuse.decl)
    println(receiver.rcv.asInstanceOf[PIdnUse].decl)
    var translatedReceiver = t.exp(receiver).asInstanceOf[FieldAccess]
    val fp = FullPerm()()
    val typ = t.ttyp(receiver.typ)
    val fieldPerm = FieldAccessPredicate(translatedReceiver, fp)()
    arg match {
      case PLetNestedScope(v, b) => And(fieldPerm, Let(LocalVarDecl(v.idndef.name, typ)(), translatedReceiver, t.exp(b))())()
      case PAnyVal() => fieldPerm
      case e => And(fieldPerm, EqCmp(translatedReceiver, t.exp(e.asInstanceOf[PExp]))())()
    }
  }

  override def subnodes: Seq[PNode] = getsubnodes()
  override def getsubnodes(): Seq[PNode] = Seq(receiver, arg)
}

case class PDefiningVarRef(id: PIdnDef) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def getsubnodes(): Seq[PNode] = Seq(id)
}

case class PAnyVal() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def getsubnodes(): Seq[PNode] = Seq()
}

case class PInvariantDef(args: Seq[PIdnDef], inv: PExp) {
  def subnodes: Seq[PNode] = args ++ Seq(inv)



  def typecheckInvariant(t: TypeChecker, na: NameAnalyser, typ: PType, locktype: String) : Unit = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(args(0).name), ref), PFormalArgDecl(PIdnDef(args(1).name), typ))
    val fakeFunc = PFunction(PIdnDef(locktype + "$inv"), params, bool, Seq(), Seq(), Some(inv))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def typecheckSecInvariant(t: TypeChecker, na: NameAnalyser, typ: PType, locktype: String) : Unit = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(args(0).name), typ))
    val fakeFunc = PFunction(PIdnDef(locktype + "$secinv"), params, bool, Seq(), Seq(), Some(inv))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def translateInvariant(t: Translator, typ: Type) : InvariantDef = {
    InvariantDef(Seq(LocalVarDecl(args(0).name, Ref)(), LocalVarDecl(args(1).name, typ)()), t.exp(inv))
  }

  def translateSecInvariant(t: Translator, typ: Type) : InvariantDef = {
    InvariantDef(Seq(LocalVarDecl(args(0).name, typ)()), t.exp(inv))
  }
}
case class PLockActionDecl(name: PIdnDef, argType: PType, retType: PType, duplicable: Boolean){
  def subnodes: Seq[PNode] = Seq(name, argType, retType)
}
case class PLockActionDef(name: PIdnUse, args: Seq[PIdnDef], newVal: PExp, returnVal: PExp, pre: PExp, post: PExp) {
  def subnodes: Seq[PNode] = args ++ Seq(name, newVal, returnVal, pre, post)
}
case class PProof(proofType: String, actions: Seq[PIdnUse], params: Seq[PIdnDef], body: PStmt) {
  def subnodes: Seq[PNode] = actions ++ params ++ Seq(body)
  def translate(t: Translator, actionDecls: Seq[LockAction], typ: Type) : Proof = {
    val types : Seq[Type] = proofType match {
      case "TODO" => Seq()
    }
    Proof(proofType, actions map (_.name), (0 until params.length) map (i => LocalVarDecl(params(i).name, types(i))()), t.stmt(body).asInstanceOf[Seqn])
  }
}

case class PLockSpec(idndef: PIdnDef, t: PType, invariant: PInvariantDef, secInv: PInvariantDef, actionList: Seq[PLockActionDecl], actions: Seq[PLockActionDef], proofs: Seq[PProof]) extends PExtender with PMember {
  override def getsubnodes: Seq[PNode] = Seq(idndef) ++ invariant.subnodes ++ secInv.subnodes ++ (actionList map (_.subnodes)).flatten ++ (actions map (_.subnodes)).flatten ++ (proofs map (_.subnodes)).flatten

  override def typecheck(tc: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO
    val allErrors = ListBuffer[String]()
    if (actionList.length != actions.length || actionList.exists(decl => !actions.exists(d => d.name.name == decl.name.name))){
      allErrors.append(idndef.name + ": Action declarations and action definitions do not match.")
    }else{
      actionList.foreach(decl => typecheckAction(tc, n, decl, actions.find(d => d.name.name == decl.name.name).get))
    }
    invariant.typecheckInvariant(tc, n, t, idndef.name)
    secInv.typecheckSecInvariant(tc, n, t, idndef.name)
    if (allErrors.isEmpty)
      None
    else
      Some(allErrors)
  }

  def typecheckAction(tc: TypeChecker, na: NameAnalyser, decl: PLockActionDecl, d: PLockActionDef) = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(d.args(0).name), t), PFormalArgDecl(PIdnDef(d.args(1).name), decl.argType))
    val newValFunc = PFunction(PIdnDef(idndef.name + "$newVal$" + decl.name.name), params, t, Seq(d.pre), Seq(), Some(d.newVal))
    val retValFunc = PFunction(PIdnDef(idndef.name + "$retVal$" + decl.name.name), params, decl.retType, Seq(), Seq(d.post), Some(d.returnVal))
    d.post.visit({case r: PResultLit => r.parent = Some(retValFunc)})
    na.namesInScope(newValFunc, None)
    na.namesInScope(retValFunc, None)
    tc.checkDeclaration(newValFunc)
    tc.checkBody(newValFunc)
    tc.checkDeclaration(retValFunc)
    tc.checkBody(retValFunc)
  }

  override def translateMemberSignature(t: Translator): Member = LockSpec(idndef.name, null, null, null, Seq(), Seq())()

  override def translateMember(t: Translator): Member = {
    val typ = t.ttyp(this.t)
    val inv = invariant.translateInvariant(t, typ)
    val secInv = this.secInv.translateSecInvariant(t, typ)
    val tActions = actionList.map(decl => translateAction(t, decl, actions.find(d => d.name.name == decl.name.name).get, typ))
    val tProofs = proofs.map(_.translate(t, tActions, typ))
    LockSpec(idndef.name, typ, inv, secInv, tActions, tProofs)()
  }

  def translateAction(t: Translator, decl: PLockActionDecl, d: PLockActionDef, typ: Type) : LockAction = {
    val params = Seq(LocalVarDecl(d.args(0).name, typ)(), LocalVarDecl(d.args(1).name, t.ttyp(decl.argType))())
    val newVal = t.exp(d.newVal)
    val retVal = t.exp(d.returnVal)
    val pre = t.exp(d.pre)
    val post = t.exp(d.post)
    LockAction(decl.name.name, t.ttyp(decl.argType), t.ttyp(decl.retType), decl.duplicable, params, newVal, retVal, pre, post)
  }
}

case class PLow(e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def getsubnodes(): Seq[PNode] = Seq(e)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    None
  }

  override def translateExp(t: Translator): Exp = {
    SIFLowExp(t.exp(e), None)()
  }
}

case class PJoinable(method: PIdnUse, e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def translateExp(t: Translator): Exp = {
    Joinable(method.name, t.exp(e))()
  }
}

case class PLock(lockType: PIdnUse, lockRef: PExp, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def translateExp(t: Translator): Exp = {
    Lock(lockType.name, t.exp(lockRef), t.exp(amount))()
  }
}

case class PLocked(lockType: PIdnUse, lockRef: PExp, value: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def translateExp(t: Translator): Exp = {
    Locked(lockType.name, t.exp(lockRef), t.exp(value))()
  }
}

case class PGuard(lockType: PIdnUse, guardName: PIdnUse, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def translateExp(t: Translator): Exp = {
    Guard(lockType.name, guardName.name, t.exp(amount))()
  }
}

case class PFork(method: PIdnUse, target: PIdnUse, args: Seq[PExp]) extends PExtender with PStmt {
  override def translateStmt(t: Translator): Stmt = {
    Fork(method.name, LocalVar(target.name, Ref)(), args map t.exp)()
  }
}

case class PJoin(method: PIdnUse, resVars: Seq[PIdnUse], token: PExp) extends PExtender with PStmt {

}

case class PNewLock(lockType: PIdnUse, target: PIdnUse, fields: Seq[PIdnUse]) extends PExtender with PStmt {

}

case class PAcquire(lockType: PIdnUse, lockExp: PExp) extends PExtender with PStmt {

}

case class PRelease(lockType: PIdnUse, lockExp: PExp, action: Option[(PIdnUse, PExp)]) extends PExtender with PStmt {

}