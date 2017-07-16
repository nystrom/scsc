package scsc.jssc

import scala.collection.mutable.ListBuffer

object Drive {
  import scsc.js.Trees._
  import scsc.js.TreeWalk._
  import Machine._
  import Continuations._
  import Residualization._
  import Step._

  // Supercompilation by evaluation generates bindings for each state
  // it supercompiles.
  // We do the same.

  import Subst._

  // Try to unify the states. We require that s1's continuation be longer than s2's
  def unify(s1: St, s2: St): Option[(Subst, Cont)] = (s1, s2) match {
    case (s1 @ Ev(e1, ρ1, σ1, φ1, k1), s2 @ Ev(e2, ρ2, σ2, φ2, k2)) =>
      if (ρ1 == ρ2 && k2.length >= k1.length) {
        val k2a = k2.take(k1.length)
        val k2b = k2.drop(k1.length)
        val u = new Unifier()
        u.unify(e1, e2)
        u.unify(k1, k2a)
        u.getSubst map {
          case subst => (subst, k2b)
        }
      }
      else {
        None
      }
    case _ =>
      None
  }

  // states that might lead to a loop
  def mightLoop(s: St) = s match {
    // check history when about to do a call
    case Ev(Call(_, _), _, _, _, _) => true
    case Ev(NewCall(_, _), _, _, _, _) => true
    case Ev(For(_, _, _, _, _), _, _, _, _) => true
    case Ev(ForIn(_, _, _, _), _, _, _, _) => true
    case Ev(While(_, _, _), _, _, _, _) => true
    case Ev(DoWhile(_, _, _), _, _, _, _) => true
    case _ => false
  }

  type Memo = List[(St, VarDef)]

  // This is unnecessarily complicated. Better would be to
  // maintain a frontier of states and just advance the frontier.
  // Merging (arbitrarily) when the two states
  // in the frontier have the same continuation.
  def drive(above: List[St], memo: Memo, whistle: Boolean)(initialState: St): (FinalState, Memo) = {
    import HE._

    for ((prevState, VarDef(h, lambda)) <- memo) {
      unify(prevState, initialState) match {
        case Some((subst, k)) =>
          // subst(initialState) should be the same as subst(prevState) but possibly with a longer continuation
          // return a call to the saved function, keeping the tail of the continuation.
          initialState match {
            case Ev(e1, ρ1, σ1, φ1, k1) =>
              lambda match {
                case Lambda(Nil, v: Val) =>
                  // the call maps to a value
                  return drive(above, memo, whistle) {
                    Co(v, σ1, φ1, k.subst(subst))
                  }
                case Lambda(xs, e) =>
                  // FIXME: completely unsure of the arguments part here
                  val x = scsc.util.FreshVar()
                  val args = xs map { x => Residual(x).subst(subst) }
                  return drive(above, memo, whistle) {
                    Co(Residual(x), Eval.simulateStore(e)(σ1, ρ1), φ1.extend(x::Nil, Assign(None, Residual(x), Call(Local(h), args))), k.subst(subst))
                  }
              }
            case _ =>
          }
        case None =>
      }
    }

    val hist: ListBuffer[St] = ListBuffer()

    var s = initialState

    while (true) {
      println(s"DRIVE $s")

      s match {
        case s0 @ Halt(v, σ, φ) =>
          val h = scsc.util.FreshVar()
          val r = s0.residual

          // memoize the result for the entire history
          val memo1 = hist collect {
            case s1 @ Ev(e1, ρ1, σ1, φ1, k1) =>
              val xs = (fv(r) intersect ρ1.keySet).toList
              println(s"MEMO $s1")
              println(s" --> $s0")
              println(s" --> $h = ${Lambda(xs, r)}")
              (s1, VarDef(h, Lambda(xs, r)))
          }
          return (s0, memo ++ memo1)

        case s0 @ Err(msg, s) =>
          return (s0, memo)

        case s0 @ Stuck(Co(v, σ, φ, Nil)) =>
          s = Halt(v, σ, φ)

        case s0 @ Stuck(_) =>
          // FIXME: don't discard the memo results
          def d(s: St) = {
            drive(above ++ hist.toList, memo, whistle)(s) match {
              case (s, memo1) => s
            }
          }

          s = s0.split(d _)

          if (s == s0) {
            // this happens when we're stuck unwinding
            return (s0, memo)
          }

        // If the whistle
        case s0 @ Ev(e, ρ, σ, φ, k) if whistle =>
          s = Stuck(s)

        case s0 @ Ev(e, ρ, σ, φ, k) if mightLoop(s0) =>
          for (prev <- (above ++ hist).reverse) {
            println(s"COMPARE $prev <<| $s0")
            if (s == s0) {
              if (prev <<| s0) {
                println(s"WHISTLE $prev <<| $s0")
                s = Stuck(s0)
              }
            }

            if (s == s0) {
              unify(prev, s0) match {
                case Some(_) =>
                  println(s"WHISTLE 2 $prev <<| $s0")
                  s = Stuck(s0)
                case None =>
              }
            }
          }

          if (s == s0) {
            hist += s0

            val s1 = s0.step
            s = s1
          }

        // Otherwise take a step.
        case s0 =>
          val s1 = s0.step
          s = s1
      }
    }

    return (Err("unreachable state", s), memo)
  }
}
