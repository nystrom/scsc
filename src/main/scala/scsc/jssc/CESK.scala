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
        case e @ Assign(None, Residual(x), _) =>
          if (used contains x) {
            e
          }
          else {
            Undefined()
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
  def eval(e: Exp, maxSteps: Int): Exp = alpha(removeDeadCode(stepper(e, maxSteps*10)))

  // def splitter(s: St): St = s match {
  //   case Co(Residual(x), σ, φ, BranchCont(_, _, _)::k) =>
  //     s
  //   case Ev(Call(fun, args), ρ, σ, φ, DoCall(_, _)::k) =>
  //     s
  // }

  def stepper(e: Exp, maxSteps: Int): Exp = {
    val absoluteMax = maxSteps * 100

    // Run for maxSteps. If we terminate, great.
    // Otherwise, _restart_ and run with termination checking enabled,
    // which might cause an earlier termination.
    var attempt = 1

    while (true) {
      var t = if (attempt == 1) maxSteps*10 else absoluteMax
      var s = inject(e)
      s = drive(s, Nil, t)

      s match {
        case s @ Halt(v, σ, φ) =>
          return s.residual
        case Err(msg, s) =>
          println(s"FAIL $msg in $s")
          return Undefined()
        case s =>
          toTerm(s) match {
            case Some((t1, φ1, _)) =>
              return Halt(t1, σ0, φ1).residual
            case None =>
              println(s"FAIL could reduce $s to term")
              return Undefined()
          }
      }
    }

    ???
  }

  // This is unnecessarily complicated. Better would be to
  // maintain a frontier of states and just advance the frontier.
  // Merging non-deterministically (arbitrarily) when the two states
  // in the frontier have the same continuation.
  // We can insert barriers to force syncing.
  // Hmmm...
  def drive(initialState: St, hist: List[St], maxSteps: Int): FinalState = {
    var t = maxSteps
    var s = initialState

    while (true) {
      t -= 1

      println(s"DRIVE $s")

      s match {
        case s0 @ Halt(v, σ, φ) =>
          return s0

        case s0 @ Err(msg, s) =>
          return s0

        case s0 @ Stuck(v, σ, φ, Nil) =>
          s = Halt(v, σ, φ)

        case s0 @ Stuck(v, σ, φ, _) =>
          val (ss, k, tryMerge) = s0.split

          var kont = k
          var states = ss

          while (states.length > 1) {
            println("SPLIT")
            states foreach { println }
            println(s"kont $kont")

            val driven = states map {
              s => drive(s, hist :+ s, t)
            }

            println("DRIVEN")
            driven foreach { println }

            tryMerge(driven, kont) match {
              case Some((ss, k)) =>
                states = ss
                kont = k
              case None =>
                // cannot merge
                return s0
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
        case Co(v, σ, φ, k) if t <= 0 =>
          s = Stuck(v, σ, φ, k)

        // Otherwise take a step.
        case s0 =>
          val s1 = step(s0)
          s = s1
      }
    }

    return Err("unreachable state", s)
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
                return Halt(t1, σ0, φ1)
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
    case s1 => s1
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
