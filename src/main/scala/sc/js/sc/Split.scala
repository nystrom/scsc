package sc.js.sc

import sc.core.sc.Unsplit._

import sc.imp.{sc => imp}

trait Split extends imp.Split with CoSplit with EvSplit with imp.Rollback {
  this: sc.js.machine.Terms with Envs with Stores with sc.js.machine.Continuations with States =>

}

trait EvSplit extends imp.EvSplit {
  this: Split with sc.js.machine.Terms with Envs with Stores with sc.js.machine.Continuations with States with imp.Rollback =>

  abstract override def evsplit(s: Ev): Option[(List[State], Unsplitter[State])] = s match {
    case Ev(e, ρ, σ, k) =>
      e match {
        case Delete(Index(e1, e2)) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::Re(v2, σ2, Nil)::_ =>
                UnsplitOk(rebuildEv(Delete(Index(v1, v2)), ρ, σ2, k))
            }
          }

          splitArgs(e1::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Typeof(e1) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::_ =>
                UnsplitOk(rebuildEv(Typeof(v1), ρ, σ1, k))
            }
          }

          splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case NewCall(fun, args) =>
          // fun is not defined, probably an unbound variable
          // in this case, evaluate the args in sequence (since we need to pass the store)
          // If there are no args, return Nil and let handle it.
          // In other cases we'd residualize the function and move on, but we
          // need to save the function name to rebuild the call
          args match {
            case Nil =>
              None
            case arg::args =>
              val split = splitArgs(arg::args, ρ, σ)

              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                def collect(n: Int) = new {
                  def unapply(ss: List[State]): Option[(List[Exp], Store)] = {
                    val values = ss collect {
                      case Re(e, _, Nil) => e
                    }
                    if (values.length == n)
                      Some((values, ss.last.asInstanceOf[Re].σ))
                    else
                      None
                  }
                }
                val pat = collect(args.length)
                unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
                  case pat(values, σ1) =>
                    UnsplitOk(rebuildEv(NewCall(fun, values), ρ, σ1, k))
                }
              }

              Some((split.toList, unsplit _))
          }

        case _ =>
          super.evsplit(s)
      }
  }
}

trait CoSplit extends imp.CoSplit {
  this: Split with sc.js.machine.Terms with Envs with Stores with sc.js.machine.Continuations with States with imp.Rollback =>

  abstract override def cosplit(s: Co): Option[(List[State], Unsplitter[State])] = s match {
    case Co(v, σ, k) =>
      k match {
        case DoTypeof(ρ1)::k =>
          split(Ev(Typeof(v), ρ1, σ, k))

        case EvalArgs(op, args, ρ1)::k =>
          op match {
            case JSNary.NewCall =>
              split(Ev(NewCall(v, args), ρ1, σ, k))
            case _ =>
              super.cosplit(s)
          }

        case EvalMoreArgs(op, pending, done, ρ1)::k =>
          val operands: List[Exp] = pending ++ (v :: done)
          op match {
            case JSNary.NewCall =>
              val fun::args = operands
              split(Ev(NewCall(fun, args), ρ1, σ, k))
            case _ =>
              super.cosplit(s)
          }

        case k =>
          super.cosplit(s)
      }
    }
}
