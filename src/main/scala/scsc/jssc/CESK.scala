package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._

// So the paper structure is:
// 1. evaluation
// 2. partial evaluation (without termination) [extend with residualization]
// 3. extending with proper splitting
// 4. extend with naive termination detection and memoization
// 5. extend with full generalization based on HE
// 6. extend with full distillation
// 7. extend with state: CESK machine
// 8. proofs
//    - residual evaluates to the same value (and state) as the original program
//    - performs fewer steps than the original program
//      - diverges exactly when the original program diverges
//    - algorithm to compute residual terminates

// Issues:
// - residualization as operations on residual values. Free variables don't work!
//   - or rather, they work when they're free in the top-level expression but not
//     when they're free elsewhere, need to ensure the let for the variable is preserved.
//     But, this doesn't happen because we're already past the point of deciding to reify the let... it's not in the cont anymore
//     So: _always_ add the rebuild-let continuation, but don't reify unless the variable
//     is free in e1 or e2.
// - termination -- detecting folding. when folded, need to residualize, which is broken
// - termination -- detecting embedding. implementing generalization
// - distillation -- detects when a LTS is embedded in another, not when a state is embedded
//                -- an LTS is the entire (infinite) evaluation of the an expression
//                -- so, is the _history_ embedded in ... what?

// Distillation: is the current history embedded in an earlier history
// Distillation works on subtrees of the LTS.

// We start with a CEK machine for the lambda calculus.
object CESK {
  import Machine._
  import Continuations._
  import Residualization._
  import Step._

  // Partial evaluation is implemented as follows:
  // We start with normal CEK-style evaluation.

  // We extend the term syntax with values for residual terms.
  // The machine must handle evaluation over residuals, which are considered values.
  // We don't need to write a function to extract the residual term, it just gets
  // computed by running the machine to the Done continuation.

  // Extending with constraints:
  // When we see Σ(Residual(e), ρ, k)
  // Lookup e as a constraint term in ρ. If we can determine its value, done!

  object Value {
    def unapply(e: Exp) = e match {
      case v if v.isValue => Some(v)
      case _ => None
    }
  }

  object ValueOrResidual {
    def unapply(e: Exp) = e match {
      case v if v.isValueOrResidual => Some(v)
      case _ => None
    }
  }

  def step(s: St): St = s.step

  // Check for termination at these nodes.
  // In SCSC, we only checked at Local nodes, but here we need to check
  // loops also since we can have non-termination evaluating any variables.
  object CheckHistory {
    def unapply(e: Exp) = e match {
      case Local(x) => Some(e)
      case While(label, test, body) => Some(e)
      case DoWhile(label, body, test) => Some(e)
      case For(label, Empty(), test, iter, body) => Some(e)
      case ForEach(label, Empty(), test, iter, body) => Some(e)
      case ForIn(label, Empty(), iter, body) => Some(e)
      case _ => None
    }
  }

  def evalProgram(e: Scope, maxSteps: Int): Scope = {
    eval(e, maxSteps) match {
      case p: Scope => p
      case e => Scope(e)
    }
  }

  // remove unused assignments and variable declarations.
  def removeDeadCode(e: Exp): Exp = {
    var used: Set[Name] = Set()
    var changed = true

    while (changed) {
      changed = false

      object CollectUsed extends Rewriter {
        override def rewrite(e: Exp) = e match {
          case e @ Local(x) =>
            if (! (used contains x)) {
              changed = true
              used += x
            }
            e
          case e @ Residual(x) =>
            if (! (used contains x)) {
              changed = true
              used += x
            }
            e
          case e @ VarDef(x, _: Lambda) =>
            // don't recurse on variable definitions
            // unless the variable is already known to be used
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ VarDef(x, _: Undefined) =>
            // don't recurse on variable definitions
            // unless the variable is already known to be used
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ Assign(None, Residual(x), Local(y)) =>
            // FIXME: extend this to all pure expressions
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ Assign(None, Residual(x), rhs) =>
            // Don't recurse on the LHS ... it's a def not a use!
            super.rewrite(rhs)
          case e =>
            super.rewrite(e)
        }
      }
      CollectUsed.rewrite(e)
    }

    object RemoveUnused extends Rewriter {
      override def rewrite(e: Exp) = super.rewrite(e) match {
        case e @ VarDef(x, _) =>
          if (used contains x) {
            e
          }
          else {
            Undefined()
          }
        case e @ Assign(None, Residual(x), Local(_)) =>
          if (used contains x) {
            e
          }
          else {
            Undefined()
          }
        case e @ Assign(None, Residual(x), rhs) =>
          if (used contains x) {
            e
          }
          else {
            rhs
          }
        case Seq(Undefined(), e) =>
          e
        case e =>
          e
      }
    }

    RemoveUnused.rewrite(e)
  }

  def alpha(e: Exp): Exp = {
    // rename residual variables in order of occurrence

    object Collector extends Rewriter {
      var map: Map[Name,Name] = Map()

      override def rewrite(e: Exp) = e match {
        case VarDef(x, _) =>
          // if (x.startsWith("_v")) {
          map += (x -> s"_v${map.size}")
          // }
          super.rewrite(e)
        case e =>
          super.rewrite(e)
      }
    }

    class Renamer(map: Map[Name, Name]) extends Rewriter {
      override def rewrite(e: Exp) = super.rewrite(e) match {
        case VarDef(x, b) =>
          map.get(x) match {
            case Some(y) => VarDef(y, b)
            case None => e
          }
        case e @ Local(x) =>
          map.get(x) match {
            case Some(y) => Local(y)
            case None => e
          }
        case e @ Residual(x) =>
          map.get(x) match {
            case Some(y) => Residual(y)
            case None => e
          }
        case e =>
          e
      }
    }

    Collector.rewrite(e)

    val e1 = new Renamer(Collector.map).rewrite(e)
    // println(s"alpha $e")
    // println(s"  --> $e1")
    e1
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
    val r = alpha(removeDeadCode(appendMemoizedFunctions(driver(e, maxSteps))))
    println("EVAL RESULT >>>")
    println(s"${scsc.js.PP.pretty(r)}")
    println("<<<")
    r
  }

  def appendMemoizedFunctions(e: Exp) = memo.foldRight(e) {
    case ((_, d), e) => Seq(d, e)
  }

  def driver(e: Exp, maxSteps: Int): Exp = {
    import scsc.js.PP

    if (maxSteps >= 0) {
      // Run for maxSteps. If we terminate, great.
      // Otherwise, _restart_ and run with termination checking enabled,
      // which might cause an earlier termination.
      drive(inject(e), Nil, Some(maxSteps)) match {
        case (s @ Halt(v, σ, φ), false) =>
          println(s"HALT FAST ${PP.pretty(s.residual)}")
          return s.residual
        case (Err(msg, s), false) =>
          println(s"FAIL $msg in $s")
          return Undefined()
        case (s, true) =>
          println(s"final state $s after timeout")
        case (s, false) =>
          println(s"final state $s without timeout (stuck?)")
      }
    }

    // clear the memo cache, otherwise we will pull in
    memo.clear

    drive(inject(e), Nil, None) match {
      case (s @ Halt(v, σ, φ), _) =>
        println(s"HALT SLOW ${PP.pretty(s.residual)}")
        return s.residual
      case (Err(msg, s), _) =>
        println(s"FAIL $msg in $s")
        return Undefined()
      case (s, _) =>
        println(s"TIMEOUT $s")
        return Undefined()
    }
  }

/*
  def generalize(ss: List[St]): Option[St] = ss match {
    case s::Nil => Some(s)
    case s1::s2::ss =>
      generalize2(s1, s2) flatMap {
        case s => generalize(s::ss)
      }
  }

  def generalize2(s1: St, s2: St): Option[St] = (s1, s2) match {
    case (Ev(e1, ρ1, σ1, φ1, k1), Ev(e2, ρ2, σ2, φ2, k2)) =>
      if (e1 == e2 && ρ1 == ρ2 && k1 == k2)
        Some(Ev(e1, ρ1, σ1.merge(σ2), φ1, k1))
      else
        None
    case (Unwinding(jump1, σ1, φ1, k1), Unwinding(jump2, σ2, φ2, k2)) =>
      if (jump1 == jump2 && k1 == k2)
        Some(Unwinding(jump1, ρ1, σ1.merge(σ2), φ1, k1))
      else
        None
    case _ =>
      None
  }

  // The given state supercompiled into a residual expression.
  // We save the residual here, abstracted over the free variables.
  // If we see a similar state, we can just generate a call
  // to the residual rather than supercompiling again.
  val memoMap: ListBuffer[(St, Name, Lambda)]

  // Note that we complete ignore the residual effect in the state
  // since this describes what happened before arriving in the given
  // state. We might consider improving HE by looking at the effect too as some
  // sort of approximation of the unknown closures in the store,
  // but it's doubtful that it's worth the bother.

  // supercompile s.
  // if we've already seen a renaming of s before, generate a call (or jump).
  // otherwise
  def memo(s: St)(body: St => FinalState): FinalState = {
    // try to generalize s1 and s2
    def tryMatch(s: St, sk: St, h: Name, lam: Lambda): Option[MSG.Subst] = (s, sk) match {
      case (s1, s2) if s1 == s2 => Some(MSG.emptySubst)
      case (Ev(e1, ρ1, σ1, _, k1), Ev(e2, ρ2, σ2, _, k2)) =>
        // if match s1 s2 returns Some renaming,
        // then s2 must be the same as renaming(s1).
        MSG.msgTerms(e1, e2)
        None
      case _ =>
        None
    }

    for ((s0, vardef) <- memoMap) {
      tryMerge(s, s0, vardef) match {
        case Some(s1) =>
          return CESK.eval(s1, S)
        case None =>
      }
    }

    body(s) match {
      case sfinal @ Halt(_, _, _) =>
        val h = FreshVar()
        memoMap += (s, VarDef(h, sfinal.residual))
        sfinal
      case sfinal =>
        sfinal
    }
  }

  // labeled effects
  val traceCache: ListBuffer[(Name, Exp)]

  sealed trait Eff
  case class RunTrace(x: Name) extends Eff
  case class If(x: Residual, pass: Eff, fail: Eff) extends Eff
  case class Seq(e1: Eff, e2: Eff) extends Eff
*/

  // Supercompilation by evaluation generates bindings for each state
  // it supercompiles.
  // We do the same.

  val memo: ListBuffer[(St, VarDef)] = ListBuffer()

  // This is unnecessarily complicated. Better would be to
  // maintain a frontier of states and just advance the frontier.
  // Merging (arbitrarily) when the two states
  // in the frontier have the same continuation.
  def drive(initialState: St, above: List[St], maxSteps: Option[Int]): (FinalState, Boolean) = {
    var t = maxSteps match {
      case None => 100
      case Some(t) => t
    }

    val whistle = maxSteps == None
    var timeout = false

    import HE._

    val hist: ListBuffer[St] = ListBuffer()

    def shouldCheckHistory(s: St) = s match {
      // check history when about to do a call
      case Ev(Call(_, _), _, _, _, _) => true
      case Ev(NewCall(_, _), _, _, _, _) => true
      case Ev(For(_, _, _, _, _), _, _, _, _) => true
      case Ev(ForIn(_, _, _, _), _, _, _, _) => true
      case Ev(While(_, _, _), _, _, _, _) => true
      case Ev(DoWhile(_, _, _), _, _, _, _) => true
      case _ => false
    }

    var s = initialState

    while (true) {
      t -= 1

      for ((prevState, VarDef(h, lambda)) <- memo) {
        import Subst._

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

        (prevState, s) match {
          case (s1 @ Ev(e1, ρ1, σ1, φ1, k1), s2 @ Ev(e2, ρ2, σ2, φ2, k2)) =>
            unify(s1, s2) match {
              case Some((subst, k)) =>
                lambda match {
                  case Lambda(Nil, v: Val) =>
                    s = Co(v, σ1.merge(σ2, ρ2), φ2, k.subst(subst))
                  case Lambda(xs, e) =>
                    val x = scsc.util.FreshVar()
                    val args = xs map { x => Residual(x).subst(subst) }
                    s = Co(Residual(x), σ1.merge(σ2, ρ2), φ2.extend(x::Nil, Assign(None, Residual(x), Call(Local(h), args))), k.subst(subst))
                }
              case None =>
            }
          case _ =>
        }
      }

      if (whistle && shouldCheckHistory(s)) {
        if (t >= 0) {
          for (prev <- above.reverse) {
            if (prev <<| s) {
              println(s"WHISTLE ABOVE $prev <<| $s")
              t = 0
            }
          }
        }

        if (t >= 0) {
          for (prev <- hist.reverse) {
            if (prev <<| s) {
              println(s"WHISTLE HERE $prev <<| $s")

              // We hit the same
              (prev, s) match {
                case (Ev(e1, ρ1, σ1, φ1, k1), Ev(e2, ρ2, σ2, φ2, k2)) if (e1 == e2 && ρ1 == ρ2) =>
                  // We hit the same loop again.
                  // Residualize the loop.. we should just jump to it in the residual.
                  // if φ1 is a prefix of φ2, just jump back.
                  // Actually we should split here!
                  s = Co(Undefined(), σ1.merge(σ2, ρ2), φ2, k2).MakeResidual(e1, ρ2, k2)
                case _ =>
                  // If not the same expression, just 0 the timer so we stop.
                  t = 0
              }
            }
          }
        }

        hist += s
      }

      println(s"DRIVE $t $s")

      // When we hit a call.

      // When we hit a loop,
      // if the loop expression is the same,
      // if the environment is the same,
      // if the TOP of the continuation is the same,
      // merge!

      s match {
        case s0 @ Halt(v, σ, φ) =>
          val h = scsc.util.FreshVar()
          val r = s0.residual
          val xs = (fv(r) -- φ.vars).toList
          println(s"MEMO $initialState")
          println(s" --> $s0")
          println(s" --> $h = ${Lambda(xs, r)}")
          memo += ((initialState, VarDef(h, Lambda(xs, r))))
          return (s0, timeout)

        case s0 @ Err(msg, s) =>
          return (s0, timeout)

        case s0 @ Stuck(v, σ, φ, Nil) =>
          s = Halt(v, σ, φ)

        case s0 @ Stuck(v, σ, φ, _) =>
          val (ss, k, tryMerge) = s0.split

          // If we get stuck, split into multiple states `ss`.
          // The split may not consume the entire continuation of the Stuck
          // state. Rather it returns `k`, which is the continuation not
          // included in the states.

          // Drive those states to completion and then try to merge them.
          // The merge may not succeed in two ways:
          // - first, it might not merge the states,
          // but rather just extend the continuation of the split states hoping
          // a merge is possible later. In this case we try again with the new
          // extended split states.
          // - second, it might fail because the states are just unmergeable
          // and there's no way to extend the continuation. In this case, we
          // return the Stuck state to the caller. Generally the caller is Stuck
          // as well and this will result in extending the caller's continuation
          // until a merge is possible.
          // Note that this is really really slow and we should memoize to avoid
          // repeating work. In the worst case we extend the continuations by
          // one frame at a time repeatedly. But we should profile
          // to see if it's really an issue. The bad case happens when we
          // have branches that complete in different ways (e.g., one returns
          // and one throws an exception). We have to merge _after_ the call
          // frame or the handler. We speed things up by just extending to the
          // next landing pad rather than extending one frame at a time.

          var kont = k
          var states = ss

          while (states.length > 1) {
            println("SPLIT")
            states foreach { println }
            println(s"kont $kont")

            val driven = states map {
              s => drive(s, above ++ hist.toList, maxSteps map { _ => t })
            }

            println("DRIVEN")
            driven foreach { case (s, _) => println(s) }

            timeout |= driven exists { case (_, timeout) => timeout }

            tryMerge(driven map (_._1), kont) match {
              case Some((ss, k)) =>
                states = ss
                kont = k
              case None =>
                // cannot merge
                return (s0, false)
            }

            println("MERGED")
            states foreach { println }
            println(s"kont $kont")
          }

          states match {
            case Nil =>
              s = Err(s"could not reconcile final states $states", s0)
            case s1::Nil =>
              s = s1
            case _ =>
              s = Err(s"could not reconcile final states $ss", s0)
          }

          println("AFTER")
          println(s"s = $s")

        // If we time out, go to the stuck state
        // case Co(v, σ, φ, k) if t <= 0 =>
        //   s = Stuck(v, σ, φ, k)

        // If we time out, residualize
        case Ev(e, ρ, σ, φ, k) if t < 0 =>
          s = Co(Undefined(), σ, φ, k).MakeResidual(e, ρ, k)
          timeout = true

        // Otherwise take a step.
        case s0 =>
          val s1 = step(s0)
          s = s1
      }
    }

    return (Err("unreachable state", s), true)
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
