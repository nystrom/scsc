package sc.js.sc

trait ReSemantics extends sc.imp.sc.ReSemantics {
  this: sc.js.machine.Terms with States with Envs with Stores with sc.js.machine.Continuations =>

  abstract override def rebuild(s: Re): Option[State] = s match {
    case Re(e @ residual, σ, k) => k match {
      case FocusCont(Undefined())::k =>
        Some(Re(Void(e), σ, k))

      case StartLoop(loop, ρ1, σ1)::k =>
        Some(Re(loop, σ1, k))

      case EvalProto(args, ρ1)::k =>
        Some(Re(NewCall(e, args map reify), σ, k))

      case EvalArgs(op, args, ρ1)::k =>
        op match {
          case Nary.InitObject =>
            Some(Re(ObjectLit(e::args), σ, k))
          case Nary.InitArray =>
            Some(Re(ArrayLit(e::args), σ, k))
          case Nary.Call =>
            Some(Re(Call(e, args), σ, k))
          case JSNary.NewCall =>
            Some(Re(NewCall(e, args), σ, k))
          case _ =>
            super.rebuild(s)
        }

      case EvalMoreArgs(op, args, done, ρ1)::k =>
        val operands = done ++ (e::args)
        op match {
          case Nary.InitObject =>
            Some(Re(ObjectLit(operands map reify), σ, k))
          case Nary.InitArray =>
            Some(Re(ArrayLit(operands map reify), σ, k))
          case Nary.Call =>
            val fun::args = operands map reify
            Some(Re(Call(fun, args), σ, k))
          case JSNary.NewCall =>
            Some(Re(NewCall(e, args), σ, k))
          case _ =>
            super.rebuild(s)
        }

      case _ =>
        super.rebuild(s)
    }
  }
}
