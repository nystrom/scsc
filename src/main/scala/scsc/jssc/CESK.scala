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
    val r = alpha(removeDeadCode(driver(e, maxSteps)))
    println("EVAL RESULT >>>")
    println(s"${scsc.js.PP.pretty(r)}")
    println("<<<")
    r
  }

  def appendMemoizedFunctions(memo: Drive.Memo, e: Exp) = memo.foldRight(e) {
    case ((_, d), e) => Seq(d, e)
  }

  def driver(e: Exp, maxSteps: Int): Exp = {
    import scsc.js.PP
    import Drive.drive

    drive(Nil, Nil, false)(inject(e)) match {
      case (s @ Halt(v, σ, φ), memo) =>
        println(s"HALT SLOW ${PP.pretty(s.residual)}")
        return appendMemoizedFunctions(memo, s.residual)
      case (Err(msg, s), _) =>
        println(s"FAIL $msg in $s")
        return Undefined()
      case (s, _) =>
        println(s"STUCK $s")
        return Undefined()
    }
  }

}
