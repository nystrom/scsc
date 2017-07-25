package sc.js.sc

class ResidualStep[M <: Machine](m: M) extends sc.imp.sc.ResidualStep[M](m) {
  import machine._
  import terms._
  import states._
  import continuations._

  override def step(s: Re): Option[State] = s match {
    case Re(e @ residual, σ, k) => k match {
      case FocusCont(Undefined())::k =>
        Some(Re(Void(e), σ, k))

      case StartLoop(loop, ρ1, σ1)::k =>
        Some(Re(loop, σ1, k))

      case EvalProto(args, ρ1)::k =>
        Some(Re(NewCall(e, args), σ, k))

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
            super.step(s)
        }

      case EvalMoreArgs(op, args, done, ρ1)::k =>
        val operands = done ++ (e::args)
        op match {
          case Nary.InitObject =>
            Some(Re(ObjectLit(operands), σ, k))
          case Nary.InitArray =>
            Some(Re(ArrayLit(operands), σ, k))
          case Nary.Call =>
            val fun::args = operands
            Some(Re(Call(fun, args), σ, k))
          case JSNary.NewCall =>
            Some(Re(NewCall(e, args), σ, k))
          case _ =>
            super.step(s)
        }

      case _ =>
        super.step(s)
    }
  }
}
