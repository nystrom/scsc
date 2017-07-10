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

  def extendWithCond(test: Exp, σAfterTest: Store, ρ: Env, result: Boolean): Store = {
    test match {
      case Binary(Binary.&&, e1, e2) if result =>
        extendWithCond(e2, extendWithCond(e1, σAfterTest, ρ, true), ρ, true)
      case Binary(Binary.||, e1, e2) if ! result =>
        extendWithCond(e2, extendWithCond(e1, σAfterTest, ρ, false), ρ, false)
      case Unary(Prefix.!, e) =>
        extendWithCond(e, σAfterTest, ρ, ! result)

      case Binary(Binary.===, Local(x), Value(v)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.==, Local(x), Value(v)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.!==, Local(x), Value(v)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.!=, Local(x), Value(v)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }

      case Binary(Binary.===, Value(v), Local(x)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.==, Value(v), Local(x)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.!==, Value(v), Local(x)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }
      case Binary(Binary.!=, Value(v), Local(x)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v, ρ)
          case None => σAfterTest
        }

      case Local(x) =>
        ρ.get(x) match {
          case Some(loc) =>
            // FIXME should't do this... x is not true, it's something that can
            // be coerced to true.
            σAfterTest.assign(loc, Bool(result), ρ)
          case None =>
            σAfterTest
        }

      case Residual(x) =>
        ρ.get(x) match {
          case Some(loc) =>
            // FIXME should't do this... x is not true, it's something that can
            // be coerced to true.
            σAfterTest.assign(loc, Bool(result), ρ)
          case None =>
            σAfterTest
        }

      case _ =>
        σAfterTest
    }
  }

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

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
    var t = maxSteps * 10
    var s = inject(e)

    // TODO:
    // New termination strategy:
    // Run for maxSteps. If we terminate, great.
    // Otherwise, _restart_ and run with termination checking enabled.

    while (t > 0) {
      t -= 1
      println(s)

      // println("term " + toTerm(s).map(_.show).getOrElse("FAIL"))

      s match {
        // stop when we have a value with the empty continuation.
        case s @ Halt(v, φ) =>
          return s.residual

        case Err(message, s) =>
          println(s"FAIL $message in $s")
          return Undefined()

        case s0 =>
          s = step(s0)
      }
    }

    // Go again! Performing termination checking as we go.
    t = maxSteps
    s = inject(e)

    val hist: ListBuffer[St] = ListBuffer()
    hist += s

    while (true) {
      t -= 1
      println(s)

      println("term " + toTerm(s).map { case (e, φ, n) => s"${e.show} in $n steps" }.getOrElse("FAIL"))

      s match {
        // stop when we have a value with the empty continuation.
        case s @ Halt(v, φ) =>
          return s.residual

        case Err(message, s) =>
          println(s"FAIL $message in $s")
          return Undefined()

        case s0 =>
          val s1 = step(s0)
          s = checkHistory(hist, s1)
          hist += s

      }
    }

    throw new RuntimeException("unreachable")
  }

  def checkHistory(hist: ListBuffer[St], s: St): St = s match {
    // TODO:
    // the residual is the code that happens _before_ the current state.
    // so don't look at the residual for the HE test.

    // associate a binding with each state
    // if we reach a similar state (focus, env, store, k), generate a residual call
    // and reduce to a term.

    // the problem is the continuation.
    // with splitting, we CUT the continuation when we SC the split

    // if the current residual is embedded in an older residual, generalize
    // change the residual to a function call, then continue.
    //
    case s1 @ Ev(CheckHistory(focus1), ρ1, σ, φ, k1) =>
      import HE._

      hist.foldRight(s1) {
        case (prev, s_) if s1 == s_ =>
          // try to fold, just for debugging purposes now
          // tryFold(s1, prev) match {
          //   case Some((f, lam, app1, app2)) =>
          //     println(s"FOLD $prev")
          //     println(s"  lam = ${lam.show}")
          //     println(s"  app1 = ${app1.show}")
          //     println(s"  app2 = ${app2.show}")
          //   case None =>
          // }

          if (prev == s1 || prev <<| s1) {
            println(s"WHISTLE $prev")
            println(s"    <<| $s1")

            tryFold(s1, prev) match {
              case Some((f, lam, app1, app2)) =>
                println(s"FOLD $prev")
                println(s"  lam = ${lam.show}")
                println(s"  app1 = ${app1.show}")
                println(s"  app2 = ${app2.show}")
              case None =>
            }

            toTerm(s1) match {
              case Some((t1, φ1, _)) =>
                return Halt(t1, φ1)
              case None =>
                return Err(s"could not convert $s1 to term", s1)
            }
          }
          else {
            // keep going
            s1
          }
        case (prev, s_) =>
          s_
      }
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
