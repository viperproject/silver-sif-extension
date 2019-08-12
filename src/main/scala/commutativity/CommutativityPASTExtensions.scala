package commutativity

import viper.silver.ast._
import viper.silver.parser._
import viper.silver.sif.{SIFLowEventExp, SIFLowExp}

import scala.collection.mutable.ListBuffer


case class PSimplePointsToPredicate(receiver: PFieldAccess, perm: PExp, arg: PExp) extends PExtender with PExp {

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def transform(go: PNode => PNode): PExtender = {
    PSimplePointsToPredicate(go(receiver).asInstanceOf[PFieldAccess], go(perm).asInstanceOf[PExp], go(arg).asInstanceOf[PExp])
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.checkTopTyped(receiver, None)
    t.checkTopTyped(perm, Some(PPrimitiv("Perm")))
    arg match {
      case _:PAnyVal => None
      case _ => {
       t.checkTopTyped(arg.asInstanceOf[PExp], Some(receiver.typ))
      }
    }
    this.typ = PPrimitiv("Bool")
    None
  }
  override def namecheck(n: NameAnalyser) = ???
  override def translateExp(t: Translator): Exp = {
    var translatedReceiver = t.exp(receiver).asInstanceOf[FieldAccess]
    val tPerm = t.exp(perm)
    arg match {
      case PAnyVal() => PointsToPredicate(translatedReceiver, tPerm, None)(t.liftPos(this))
      case e => PointsToPredicate(translatedReceiver, tPerm, Some(t.exp(e.asInstanceOf[PExp])))(t.liftPos(this))
    }
  }

  override def subnodes: Seq[PNode] = getsubnodes()
  override def getsubnodes(): Seq[PNode] = Seq(receiver, perm, arg)
}

case class PVarDefiningPointsToPredicate(receiver: PFieldAccess, perm: PExp, var arg: PLet) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions


  override def transform(go: PNode => PNode): PExtender = {
    PVarDefiningPointsToPredicate(go(receiver).asInstanceOf[PFieldAccess], go(perm).asInstanceOf[PExp], go(arg).asInstanceOf[PLet])
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.checkTopTyped(receiver, None)
    t.checkTopTyped(perm, Some(PPrimitiv("Perm")))
    t.checkTopTyped(arg, Some(PPrimitiv("Bool")))
    this.typ = PPrimitiv("Bool")
    None
  }
  override def namecheck(n: NameAnalyser) = ???
  override def translateExp(t: Translator): Exp = {
    var translatedReceiver = t.exp(receiver).asInstanceOf[FieldAccess]
    val tPerm = t.exp(perm)
    val tLet = t.exp((arg)).asInstanceOf[Let]
    VarDefiningPointsToPredicate(translatedReceiver, tPerm, tLet.variable, Some(tLet.body))(t.liftPos(this))
  }

  override def subnodes: Seq[PNode] = getsubnodes()
  override def getsubnodes(): Seq[PNode] = Seq(receiver, perm, arg)
}

case class PAnyVal() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def getsubnodes(): Seq[PNode] = Seq()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None
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

  def transform(go: PNode => PNode): PInvariantDef = {
    PInvariantDef(args map (go(_).asInstanceOf[PIdnDef]), go(inv).asInstanceOf[PExp])
  }
}
case class PLockActionDecl(val idndef: PIdnDef, argType: PType, retType: PType, duplicable: Boolean) extends PExtender with PMember{
  override def getsubnodes: Seq[PNode] = Seq(idndef, argType, retType)

  override def transform(go: PNode => PNode): PExtender = {
    PLockActionDecl(go(idndef).asInstanceOf[PIdnDef], go(argType).asInstanceOf[PType], go(retType).asInstanceOf[PType], duplicable)
  }
}
case class PLockActionDef(name: PIdnUse, args: Seq[PIdnDef], newVal: PExp, returnVal: PExp, pre: PExp, post: PExp) extends FastPositioned {
  def subnodes: Seq[PNode] = args ++ Seq(name, newVal, returnVal, pre, post)

  def transform(go: PNode => PNode): PLockActionDef = {
    PLockActionDef(go(name).asInstanceOf[PIdnUse], args map (go(_).asInstanceOf[PIdnDef]), go(newVal).asInstanceOf[PExp], go(returnVal).asInstanceOf[PExp], go(pre).asInstanceOf[PExp], go(post).asInstanceOf[PExp])
  }
}
case class PProof(proofType: String, actions: Seq[PIdnUse], params: Seq[PIdnDef], body: PSeqn) {
  def subnodes: Seq[PNode] = actions ++ params ++ Seq(body)
  def translate(t: Translator, actionDecls: Seq[LockAction], typ: Type) : Proof = {
    val types : Seq[Type] = proofType match {
      case "preservation" => {
        val action = actionDecls.find(ad => ad.name == actions(0).name).get
        Seq(typ, action.argType)
      }
      case "commutativity" => {
        val a1 = actionDecls.find(ad => ad.name == actions(0).name).get
        val a2 = actionDecls.find(ad => ad.name == actions(1).name).get
        Seq(typ, a1.argType, a2.argType)
      }
      case "reordering" => {
        val a1 = actionDecls.find(ad => ad.name == actions(0).name).get
        val a2 = actionDecls.find(ad => ad.name == actions(1).name).get
        Seq(typ, a1.argType, a2.argType)
      }
    }
    Proof(proofType, actions map (_.name), (0 until params.length) map (i => LocalVarDecl(params(i).name, types(i))()), t.stmt(body).asInstanceOf[Seqn])
  }

  def typecheck(tc: TypeChecker, ns: NameAnalyser, actionDecls: Seq[PLockActionDecl], t: PType) : Seq[String] = {
    proofType match {
      case "preservation" => {
        if (actions.length != 1){
          return Seq("Wrong number of actions for preservation proof.")
        }else if (params.length != 2){
          return Seq("Wrong number of parameters for preservation proof.")
        }
        val actionDecl = actionDecls.find(ad => ad.idndef.name == actions(0).name)
        if (actionDecl.isEmpty){
          return Seq("Unknown action: " + actions(0).name)
        }
        val fakeParams = Seq(PFormalArgDecl(PIdnDef(params(0).name), t), PFormalArgDecl(PIdnDef(params(1).name), actionDecl.get.argType))
        val fakeMethod = PMethod(PIdnDef(actionDecl.get.idndef.name + "$proof$pres$"), fakeParams, Seq(), Seq(), Seq(), Some(body))
        ns.namesInScope(fakeMethod, None)
        tc.checkDeclaration(fakeMethod)
        tc.checkBody(fakeMethod)
        Seq()
      }
      case "commutativity" => {
        if (actions.length != 2){
          return Seq("Wrong number of actions for commutativity proof.")
        }else if (params.length != 3){
          return Seq("Wrong number of parameters for commutativity proof.")
        }
        val a1 = actionDecls.find(ad => ad.idndef.name == actions(0).name)
        if (a1.isEmpty){
          return Seq("Unknown action: " + actions(0).name)
        }
        val a2 = actionDecls.find(ad => ad.idndef.name == actions(1).name)
        if (a2.isEmpty){
          return Seq("Unknown action: " + actions(1).name)
        }
        if (actionDecls.indexOf(a1.get) > actionDecls.indexOf(a2.get)){
          return Seq("Incorrect action order in commutativity proof: " + actions(0).name + ", " + actions(1).name)
        }
        val fakeParams = Seq(PFormalArgDecl(PIdnDef(params(0).name), t), PFormalArgDecl(PIdnDef(params(1).name), a1.get.argType), PFormalArgDecl(PIdnDef(params(2).name), a2.get.argType))
        val fakeMethod = PMethod(PIdnDef("$proof$comm$" + a1.get.idndef.name + "$" + a2.get.idndef.name), fakeParams, Seq(), Seq(), Seq(), Some(body))
        ns.namesInScope(fakeMethod, None)
        tc.checkDeclaration(fakeMethod)
        tc.checkBody(fakeMethod)
        Seq()
      }
      case "reordering" => {
        if (actions.length != 2){
          return Seq("Wrong number of actions for reordering proof.")
        }else if (params.length != 3){
          return Seq("Wrong number of parameters for reordering proof.")
        }
        val a1 = actionDecls.find(ad => ad.idndef.name == actions(0).name)
        if (a1.isEmpty){
          return Seq("Unknown action: " + actions(0).name)
        }
        val a2 = actionDecls.find(ad => ad.idndef.name == actions(1).name)
        if (a2.isEmpty){
          return Seq("Unknown action: " + actions(1).name)
        }
        if (actionDecls.indexOf(a1.get) > actionDecls.indexOf(a2.get)){
          return Seq("Incorrect action order in reordering proof: " + actions(0).name + ", " + actions(1).name)
        }
        val fakeParams = Seq(PFormalArgDecl(PIdnDef(params(0).name), t), PFormalArgDecl(PIdnDef(params(1).name), a1.get.argType), PFormalArgDecl(PIdnDef(params(2).name), a2.get.argType))
        val fakeMethod = PMethod(PIdnDef("$proof$reo$" + a1.get.idndef.name + "$" + a2.get.idndef.name), fakeParams, Seq(), Seq(), Seq(), Some(body))
        ns.namesInScope(fakeMethod, None)
        tc.checkDeclaration(fakeMethod)
        tc.checkBody(fakeMethod)
        Seq()
      }
    }
  }

  def transform(go: PNode => PNode): PProof = {
    PProof(proofType, actions map (go(_).asInstanceOf[PIdnUse]), params map (go(_).asInstanceOf[PIdnDef]), go(body).asInstanceOf[PSeqn])
  }
}

case class PLockSpec(idndef: PIdnDef, t: PType, invariant: PInvariantDef, secInv: PInvariantDef, actionList: Seq[PLockActionDecl], actions: Seq[PLockActionDef], proofs: Seq[PProof]) extends PExtender with PMember {
  override def getsubnodes: Seq[PNode] = Seq(idndef) ++ invariant.subnodes ++ secInv.subnodes ++ (actionList map (_.subnodes)).flatten ++ (actions map (_.subnodes)).flatten ++ (proofs map (_.subnodes)).flatten

  override def typecheck(tc: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    val allErrors = ListBuffer[String]()
    if (actionList.length != actions.length || actionList.exists(decl => !actions.exists(d => d.name.name == decl.idndef.name))){
      allErrors.append(idndef.name + ": Action declarations and action definitions do not match.")
    }else{
      actionList.foreach(decl => typecheckAction(tc, n, decl, actions.find(d => d.name.name == decl.idndef.name).get))
    }
    invariant.typecheckInvariant(tc, n, t, idndef.name)
    secInv.typecheckSecInvariant(tc, n, t, idndef.name)
    for (proof <- proofs) {
      allErrors ++= proof.typecheck(tc, n, actionList, t)
    }
    if (allErrors.isEmpty)
      None
    else
      Some(allErrors)
  }

  def typecheckAction(tc: TypeChecker, na: NameAnalyser, decl: PLockActionDecl, d: PLockActionDef) = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(d.args(0).name), t), PFormalArgDecl(PIdnDef(d.args(1).name), decl.argType))
    val newValFunc = PFunction(PIdnDef(idndef.name + "$newVal$" + decl.idndef.name), params, t, Seq(d.pre), Seq(), Some(d.newVal))
    val retValFunc = PFunction(PIdnDef(idndef.name + "$retVal$" + decl.idndef.name), params, decl.retType, Seq(), Seq(d.post), Some(d.returnVal))
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
    val tActions = actionList.map(decl => translateAction(t, decl, actions.find(d => d.name.name == decl.idndef.name).get, typ))
    val tProofs = proofs.map(_.translate(t, tActions, typ))
    LockSpec(idndef.name, typ, inv, secInv, tActions, tProofs)(t.liftPos(this))
  }

  def translateAction(t: Translator, decl: PLockActionDecl, d: PLockActionDef, typ: Type) : LockAction = {
    val params = Seq(LocalVarDecl(d.args(0).name, typ)(), LocalVarDecl(d.args(1).name, t.ttyp(decl.argType))())
    val newVal = t.exp(d.newVal)
    val retVal = t.exp(d.returnVal)
    val pre = t.exp(d.pre)
    val post = t.exp(d.post)
    LockAction(decl.idndef.name, t.ttyp(decl.argType), t.ttyp(decl.retType), decl.duplicable, params, newVal, retVal, pre, post)(t.liftPos(d))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLockSpec(go(idndef).asInstanceOf[PIdnDef], go(t).asInstanceOf[PType], invariant.transform(go), secInv.transform(go), actionList map (go(_).asInstanceOf[PLockActionDecl]), actions map (_.transform(go)), proofs map (_.transform(go)))
  }
}

case class PLow(e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(e)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    this.typ = PPrimitiv("Bool")
    None
  }

  override def translateExp(t: Translator): Exp = {
    SIFLowExp(t.exp(e), None)(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLow(go(e).asInstanceOf[PExp])
  }
}

case class PLowEvent() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.typ = PPrimitiv("Bool")
    None
  }

  override def translateExp(t: Translator): Exp = {
    SIFLowEventExp()(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    this
  }
}

case class PJoinable(method: PIdnUse, e: PExp, arguments: Seq[PExp]) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(method, e) ++ arguments

  override def translateExp(t: Translator): Exp = {
    Joinable(method.name, t.exp(e), arguments map (t.exp(_)))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalArgs.length == arguments.length){
          for (i <- 0 until arguments.length) {
            t.checkTopTyped(arguments(i), Some(m.formalArgs(i).typ))
          }
          this.typ = PPrimitiv("Bool")
          None
        }else{
          Some(Seq("Wrong number of arguments in joinable[" + method.name + "]"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PJoinable(go(method).asInstanceOf[PIdnUse], go(e).asInstanceOf[PExp], arguments map (go(_).asInstanceOf[PExp]))
  }
}

case class PLock(lockType: PIdnUse, lockRef: PExp, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, amount)

  override def translateExp(t: Translator): Exp = {
    Lock(lockType.name, t.exp(lockRef), t.exp(amount))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))
    t.checkTopTyped(amount, Some(PPrimitiv("Perm")))
    n.definition(t.curMember)(lockType) match {
      case _: PLockSpec => {
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLock(go(lockType).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(amount).asInstanceOf[PExp])
  }
}

case class PLocked(lockType: PIdnUse, lockRef: PExp, value: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, value)

  override def translateExp(t: Translator): Exp = {
    Locked(lockType.name, t.exp(lockRef), t.exp(value))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        t.checkTopTyped(value, Some(ls.t))
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLocked(go(lockType).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(value).asInstanceOf[PExp])
  }
}

case class PGuard(lockType: PIdnUse, guardName: PIdnUse, lockRef: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef)

  override def translateExp(t: Translator): Exp = {
    Guard(lockType.name, guardName.name, t.exp(lockRef))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(_) => {
            this.typ = PPrimitiv("Bool")
            None
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PGuard(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp])
  }
}

case class PLocktype() extends PExtender with PType {

  override def getsubnodes(): Seq[PNode] = subNodes

  override def subNodes: Seq[PType] = Seq()

  override def substitute(ts: PTypeSubstitution): PType = this

  override def isValidOrUndeclared: Boolean = true

  override def transform(go: PNode => PNode): PExtender = {
    this
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def translateType(t: Translator): Type = Locktype()
}

case class PThreadtype() extends PExtender with PType {

  override def getsubnodes(): Seq[PNode] = subNodes

  override def subNodes: Seq[PType] = Seq()

  override def substitute(ts: PTypeSubstitution): PType = this

  override def isValidOrUndeclared: Boolean = true

  override def transform(go: PNode => PNode): PExtender = {
    this
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def translateType(t: Translator): Type = Threadtype()
}

case class PFork(method: PIdnUse, target: PIdnUse, args: Seq[PExp]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(method, target) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(target, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalArgs.length == args.length){
          for (i <- 0 until args.length){
            t.checkTopTyped(args(i), Some(m.formalArgs(i).typ))
          }
          None
        }else {
          Some(Seq("Incorrect number of arguments"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Fork(method.name, t.exp(target).asInstanceOf[LocalVar], args map (t.exp(_)))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PFork(go(method).asInstanceOf[PIdnUse], go(target).asInstanceOf[PIdnUse], args map (go(_).asInstanceOf[PExp]))
  }
}

case class PJoin(method: PIdnUse, resVars: Seq[PIdnUse], token: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(method, token) ++ resVars

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(token, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalReturns.length == resVars.length){
          for (i <- 0 until resVars.length){
            t.checkTopTyped(resVars(i), Some(m.formalReturns(i).typ))
          }
          var hasOld = false
          m.posts.foreach(post => post.visit({
            case _: POld => hasOld = true
          }))
          if (hasOld){
            Some(Seq("Joining methods with old expressions in postcondition is not supported."))
          }else{
            None
          }
        }else {
          Some(Seq("Incorrect number of target variables"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Join(method.name, resVars map (t.exp(_).asInstanceOf[LocalVar]), t.exp(token))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PJoin(go(method).asInstanceOf[PIdnUse], resVars map (go(_).asInstanceOf[PIdnUse]),  go(token).asInstanceOf[PExp])
  }
}

case class PNewLock(lockType: PIdnUse, target: PIdnUse, fields: Seq[PIdnUse]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, target) ++ fields

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(target, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        for (f <- fields){
          n.definition(t.curMember)(f) match {
            case fieldDef:PField => f.typ = fieldDef.typ
            case _ => return Some(Seq("Expected field: " + f.name))
          }
        }
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    NewLock(lockType.name, LocalVar(target.name, t.ttyp(target.typ))(), fields map (f => Field(f.name, t.ttyp(f.typ))()))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PNewLock(go(lockType).asInstanceOf[PIdnUse], go(target).asInstanceOf[PIdnUse], fields map (go(_).asInstanceOf[PIdnUse]))
  }
}

case class PAcquire(lockType: PIdnUse, lockExp: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => None
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Acquire(lockType.name, t.exp(lockExp))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PAcquire(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp])
  }
}

case class PRelease(lockType: PIdnUse, lockExp: PExp, action: Option[(PIdnUse, PExp)]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp) ++ (if (action.isDefined) Seq(action.get._1, action.get._2) else Seq())

  override def translateStmt(t: Translator): Stmt = {
    Release(lockType.name, t.exp(lockExp), if (action.isDefined) Some((action.get._1.name, t.exp(action.get._2))) else None)(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        if (action.isDefined){
          val actionDecl = ls.actionList.find(a => a.idndef.name == action.get._1.name)
          if (actionDecl.isDefined) {
            t.checkTopTyped(action.get._2, Some(actionDecl.get.argType))
            None
          }else{
            Some(Seq("Unknown action: " + action.get._1.name))
          }
        }else{
          None
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PRelease(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], if (action.isDefined) Some((go(action.get._1).asInstanceOf[PIdnUse], go(action.get._2).asInstanceOf[PExp])) else None)
  }
}

case class PShare(lockType: PIdnUse, lockExp: PExp, lockVal: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp, lockVal)

  override def translateStmt(t: Translator): Stmt = {
    Share(lockType.name, t.exp(lockExp), t.exp(lockVal))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        t.checkTopTyped(lockVal, Some(ls.t))
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PShare(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], go(lockVal).asInstanceOf[PExp])
  }
}