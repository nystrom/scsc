package sc.js.sc

import sc.core.sc.Unsplit._

class EvSplit[M <: Machine](m: M) extends sc.imp.sc.EvSplit[M](m) {
  import machine._
  import terms._
  import states._
  import continuations._
  import envs._
  import stores._
  import states.Rollback._

  override def split(s: Ev): Option[(List[State], Unsplitter[State])] = s match {
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
          super.split(s)
      }
  }
}

class CoSplit[M <: Machine](m: M) extends sc.imp.sc.CoSplit[M](m) {
  import machine._
  import terms._
  import states._
  import continuations._
  import envs._
  import stores._

  override def split(s: Co): Option[(List[State], Unsplitter[State])] = s match {
    case Co(v, σ, k) =>
      k match {
        case DoTypeof(ρ1)::k =>
          states.split(Ev(Typeof(v), ρ1, σ, k))

        case EvalArgs(op, args, ρ1)::k =>
          op match {
            case JSNary.NewCall =>
              states.split(Ev(NewCall(v, args), ρ1, σ, k))
            case _ =>
              super.split(s)
          }

        case EvalMoreArgs(op, pending, done, ρ1)::k =>
          val operands: List[Exp] = pending ++ (v :: done)
          op match {
            case JSNary.NewCall =>
              val fun::args = operands
              states.split(Ev(NewCall(fun, args), ρ1, σ, k))
            case _ =>
              super.split(s)
          }

        case k =>
          None
      }
    }
}
