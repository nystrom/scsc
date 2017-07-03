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

  object HeapValue {
    def unapply(e: Exp) = e match {
      case v if v.isHeapValue => Some(v)
      case _ => None
    }
  }

  object ValueOrResidual {
    def unapply(e: Exp) = e match {
      case v if v.isValueOrResidual => Some(v)
      case _ => None
    }
  }

  object NormalForm {
    def unapply(e: Exp) = e match {
      case v if v.isNormalForm => Some(v)
      case _ => None
    }
  }

  // Statements evaluate to Empty or a residual
  // Expressions evaluate to a value or a residual.
  // Expressions (e.g., names and property accesses) may evaluate to a memory location.
  def step(s: St): St = s match {
    // Done!
    case s @ Σ(NormalForm(_), _, _, _, Nil) => s

    // Fail fast
    case s @ Σ(_, _, _, _, Fail(_)::k) => s

    ////////////////////////////////////////////////////////////////
    // Scopes.
    ////////////////////////////////////////////////////////////////

    case Σ(Scope(s), ρ, σ, ɸ, k) =>
      // Go through all the bindings in the block and add them to the environment
      // as `undefined`. As we go thorugh the block, we'll initialize the variables.
      object CollectBindings extends Rewriter {
        var bindings: Vector[Name] = Vector()
        override def rewrite(e: Exp) = e match {
          case VarDef(x, _) =>
            bindings = bindings :+ x
            super.rewrite(e)
          case LetDef(x, _) =>
            bindings = bindings :+ x
            super.rewrite(e)
          case ConstDef(x, _) =>
            bindings = bindings :+ x
            super.rewrite(e)
          case _: Lambda | _: FunObject | _: Residual | _: Scope =>
            // don't recurse on these
            e
          case e =>
            super.rewrite(e)
        }
      }
      CollectBindings.rewrite(s)
      val bindings = CollectBindings.bindings

      val locs = bindings map { _ => FreshLoc() }
      val ρ1 = (bindings zip locs).foldLeft(ρ) {
        case (ρ, (x, loc)) => ρ + (x -> loc)
      }
      val σ1 = (bindings zip locs).foldLeft(σ) {
        case (σ, (x, loc)) => σ.assign(loc, Undefined(), ρ1)
      }
      Σ(s, ρ1, σ1, ɸ, RebuildScope(ρ1)::k)

    case Σ(Residual(e), ρ, σ, ɸ, RebuildScope(ρ1)::k) =>
      Σ(Residual(Scope(e)), ρ, σ, ɸ, k)

    case Σ(Value(e), ρ, σ, ɸ, RebuildScope(ρ1)::k) =>
      Σ(e, ρ, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Conditionals
    // ? : and if/else are handled identically, duplicating code
    ////////////////////////////////////////////////////////////////

    // if e then s1 else s2
    case Σ(IfElse(e, s1, s2), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, BranchCont(SeqCont(s1, ρ)::Nil,
                               SeqCont(s2, ρ)::Nil,
                               RebuildIfElseTest(s1, s2, ρ)::Nil)::k)

    // e ? s1 : s2
    case Σ(Cond(e, s1, s2), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, BranchCont(SeqCont(s1, ρ)::Nil,
                               SeqCont(s2, ρ)::Nil,
                               RebuildCondTest(s1, s2, ρ)::Nil)::k)

    case Σ(v @ CvtBool(true), ρ, σ, ɸ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, ɸ, kt ++ k)

    case Σ(v @ CvtBool(false), ρ, σ, ɸ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, ɸ, kf ++ k)

    // Neither true nor false, so residualize
    case Σ(ValueOrResidual(e), ρ, σ, ɸ, BranchCont(kt, kf, kr)::k) =>
      Σ(Residual(e), ρ, σ, ɸ, kr ++ k)


    // Rebuilding ? : and if-else nodes.
    // The logic is duplicated.

    // Evaluate the test to a (residual) value.
    // Save the store and eval the true branch.
    case Σ(ValueOrResidual(test), ρ, σ0, ɸ, RebuildCondTest(s1, s2, ρ0)::k) =>
      Σ(s1, ρ0, σ0, Undefined(), RebuildCondTrue(reify(test)(σ0, ρ), s2, σ0, ɸ, ρ0)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(ValueOrResidual(s1), ρ1, σ1, ɸ1, RebuildCondTrue(test, s2, σ0, ɸ0, ρ0)::k) =>
      Σ(s2, ρ0, σ0, Undefined(), RebuildCondFalse(test, reify(s1)(σ1, ρ1), σ1, ɸ0, ɸ1, ρ0)::k)

    // Rebuild and merge the post-true and post-false stores.
    case Σ(ValueOrResidual(s2), ρ2, σ2, ɸ2, RebuildCondFalse(test, s1, σ1, ɸ0, ɸ1, ρ0)::k) =>
      val ɸ = Sequence(ɸ0, IfElse(test, ɸ1, ɸ2))
      Σ(Residual(Cond(test, s1, reify(s2)(σ2, ρ2))), ρ0, σ1.merge(σ2), ɸ, k)

    case Σ(ValueOrResidual(test), ρ, σ0, ɸ, RebuildIfElseTest(s1, s2, ρ0)::k) =>
      Σ(s1, ρ0, σ0, Undefined(), RebuildIfElseTrue(reify(test)(σ0, ρ), s2, σ0, ɸ, ρ0)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(ValueOrResidual(s1), ρ1, σ1, ɸ1, RebuildIfElseTrue(test, s2, σ0, ɸ0, ρ0)::k) =>
      Σ(s2, ρ0, σ0, Undefined(), RebuildIfElseFalse(test, reify(s1)(σ1, ρ1), σ1, ɸ0, ɸ1, ρ0)::k)

    // Rebuild and merge the post-true and post-false stores.
    case Σ(ValueOrResidual(s2), ρ2, σ2, ɸ2, RebuildIfElseFalse(test, s1, σ1, ɸ0, ɸ1, ρ0)::k) =>
      val ɸ = Sequence(ɸ0, IfElse(test, ɸ1, ɸ2))
      Σ(Undefined(), ρ0, σ1.merge(σ2), ɸ, k)

    // the problem, in general, is that the loop condition evaluates to something in the current store.
    // but the next time around the loop, the store is different.
    // the best we can do is peel the loop once

    ////////////////////////////////////////////////////////////////
    // Loops.
    // This is very much complicated by break and continue.
    // Otherwise we could just desugar everything into IfElse,
    // unrolling the loop and letting generlization handle
    // termination detection and rebuilding the loop.
    ////////////////////////////////////////////////////////////////

    case Σ(For(label, Empty(), test, iter, body), ρ, σ, ɸ, k) =>
      Σ(test, ρ, σ, ɸ, BranchCont(
                      SeqCont(body, ρ)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ)::BreakFrame(label)::Nil,
                      SeqCont(Undefined(), ρ)::Nil,
                      RebuildForTest(label, test, iter, body, ρ)::Nil)::k)

    case Σ(For(label, init, test, iter, body), ρ, σ, ɸ, k) =>
      Σ(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, ɸ, k)

    // do body while test
    case Σ(DoWhile(label, body, test), ρ, σ, ɸ, k) =>
      Σ(body, ρ, σ, ɸ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)

    // just desugar into a for loop
    case Σ(While(label, test, body), ρ, σ, ɸ, k) =>
      Σ(For(label, Empty(), test, Empty(), body), ρ, σ, ɸ, k)

    // Residualizing loops.
    // PE the test.
    // Save the store after the test.
    // PE the body.
    // Save the store after the body.
    // Merge the store after the test with the store after the body.
    // HPE approach: if the stores differ in any way (WRT the environment),
    // just erase the store.

    // We have no idea what should be the store after PE a residualized loop.
    // In this case, just empty the store.

    // The loop condition test should be a residual value.
    // the continuation stores the original (non-partially-evaluated) loop test and body
    case Σ(ValueOrResidual(test), ρ, σ, ɸ, RebuildForTest(label0, test0, iter0, body0, ρ1)::k) =>
      Σ(body0, ρ1, σ, ɸ, RebuildForBody(label0, test, test0, iter0, body0, ρ)::k)

    case Σ(ValueOrResidual(body1), ρ, σ, ɸ, RebuildForBody(label0, test1, test0, iter0, body0, ρ1)::k) =>
      Σ(iter0, ρ, σ, ɸ, RebuildForIter(label0, body1, test1, test0, iter0, body0, ρ1)::k)

    // Discard the store.
    case Σ(ValueOrResidual(iter1), ρ, σ, ɸ, RebuildForIter(label, body1, test1, test0, Empty(), body0, ρ1)::k) =>
      Σ(reify(IfElse(test1, Seq(body1, Seq(iter1, While(label, test0, body0))), Undefined()))(σ, ρ),
        ρ1, σ0, ɸ, k)

    case Σ(ValueOrResidual(iter1), ρ, σ, ɸ, RebuildForIter(label, body1, test1, test0, iter0, body0, ρ1)::k) =>
      Σ(reify(IfElse(test1, Seq(body1, Seq(iter1, For(label, Empty(), test0, iter0, body0))), Undefined()))(σ, ρ),
        ρ1, σ0, ɸ, k)

    // Break and continue.

    // // when break hits a loop cont, run the break continuation
    // case Σ(Break(None), ρ, σ, BreakFrame(_)::k) =>
    //   Σ(Undefined(), ρ, σ, k)
    //
    // case Σ(Break(Some(x)), ρ, σ, BreakFrame(Some(y))::k) if x == y =>
    //   Σ(Undefined(), ρ, σ, k)
    //
    // // when continue hits a loop cont, run the continue continuation
    // case Σ(Continue(None), ρ, σ, ContinueFrame(_)::k) =>
    //   Σ(Undefined(), ρ, σ, k)
    //
    // case Σ(Continue(Some(x)), ρ, σ, ContinueFrame(Some(y))::k) if x == y =>
    //   Σ(Undefined(), ρ, σ, k)
    //
    // case Σ(Break(optLabel), ρ, σ, _::k) =>
    //   Σ(Break(optLabel), ρ, σ, k)
    //
    // // propagate continue to the outer continuation
    // case Σ(Continue(optLabel), ρ, σ, _::k) =>
    //   Σ(Continue(optLabel), ρ, σ, k)

    case Σ(Break(label), ρ, σ, ɸ, k) =>
      Σ(Undefined(), ρ, σ, ɸ, Breaking(label)::k)
    case Σ(Continue(label), ρ, σ, ɸ, k) =>
      Σ(Undefined(), ρ, σ, ɸ, Continuing(label)::k)

    case Σ(v, ρ, σ, ɸ, Breaking(None)::BreakFrame(_)::k) =>
      Σ(v, ρ, σ, ɸ, k)
    case Σ(v, ρ, σ, ɸ, Continuing(None)::ContinueFrame(_)::k) =>
      Σ(v, ρ, σ, ɸ, k)

    case Σ(v, ρ, σ, ɸ, Breaking(Some(x))::BreakFrame(Some(y))::k) if x == y =>
      Σ(v, ρ, σ, ɸ, k)
    case Σ(v, ρ, σ, ɸ, Continuing(Some(x))::ContinueFrame(Some(y))::k) if x == y =>
      Σ(v, ρ, σ, ɸ, k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, ɸ, Breaking(label)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, ɸ, a::Breaking(label)::k)
    case Σ(v, ρ, σ, ɸ, Continuing(label)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, ɸ, a::Continuing(label)::k)

    case Σ(v, ρ, σ, ɸ, Breaking(label)::_::k) =>
      Σ(v, ρ, σ, ɸ, Breaking(label)::k)
    case Σ(v, ρ, σ, ɸ, Continuing(label)::_::k) =>
      Σ(v, ρ, σ, ɸ, Continuing(label)::k)

    // discard useless break and continue frames
    case Σ(NormalForm(v), ρ, σ, ɸ, BreakFrame(_)::k) =>
      Σ(v, ρ, σ, ɸ, k)
    case Σ(NormalForm(v), ρ, σ, ɸ, ContinueFrame(_)::k) =>
      Σ(v, ρ, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Blocks.
    // As usual, residual handling is difficult.
    ////////////////////////////////////////////////////////////////

    case Σ(Empty(), ρ, σ, ɸ, k) =>
      Σ(Undefined(), ρ, σ, ɸ, k)

    case Σ(Seq(s1, s2), ρ, σ, ɸ, k) =>
      Σ(s1, ρ, σ, ɸ, SeqCont(s2, ρ)::k)

    case Σ(Residual(s1), ρ, σ, ɸ, SeqCont(s2, ρ1)::k) =>
      Σ(s2, ρ1, σ, Seq(ɸ, s1), k)

    // Discard the value and evaluate the sequel.
    case Σ(Value(_), ρ, σ, ɸ, SeqCont(s2, ρ1)::k) =>
      Σ(s2, ρ, σ, ɸ, k)

    // case Σ(ValueOrResidual(s2), ρ, σ, ɸ, RebuildSeq(s1, ρ1)::k) =>
    //   Σ(reify(Seq(s1, s2))(σ, ρ), ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Definitions.
    ////////////////////////////////////////////////////////////////

    // Definitions eval to undefined.
    // Look up the location, which should have been added to the environment
    // when we entered the block.
    // Then run the initializer, assigning to the location.
    // The DoAssign continuation should leave the initializer in the focus,
    // but we should evaluate to undefined, so add block continuation for that.
    case Σ(VarDef(x, Lambda(xs, e)), ρ, σ, ɸ, k) =>
      // Special case lambdas because we need to set the name of the heap object.
      // var Point = function (x, y) { this.x = x; this.y = y}
      // ==
      // var Point = { __code__: fun..., prototype: { __proto__: Function.prototype } }
      ρ.get(x) match {
        case Some(loc) =>
          val name = FreshLoc()
          val prototype = FreshLoc()
          val lambdaLoc = FreshLoc()
          val p = FunObject("object", Prim("Function.prototype"), Nil, None, Nil)
          val o = FunObject("function", prototype, xs, Some(e), Property(StringLit("name"), name, None, None)::Property(StringLit("prototype"), prototype, None, None)::Nil)
          val σ1 = σ.assign(name, StringLit(x), ρ)
                    .assign(prototype, p, ρ)
                    .assign(lambdaLoc, o, ρ)
                    .assign(loc, lambdaLoc, ρ)
          Σ(lambdaLoc, ρ, σ1, ɸ,
            DoAssign(None, loc, ρ)::
            RebuildVarDef(x, ρ)::k)
        case None =>
          Σ(e, ρ, σ, ɸ, Fail(s"variable $x not found")::k)
      }

    case Σ(VarDef(x, e), ρ, σ, ɸ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, ɸ, DoAssign(None, loc, ρ)::RebuildVarDef(x, ρ)::k)
        case None =>
          Σ(e, ρ, σ, ɸ, Fail(s"variable $x not found")::k)
      }
    case Σ(LetDef(x, e), ρ, σ, ɸ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, ɸ, DoAssign(None, loc, ρ)::RebuildLetDef(x, ρ)::k)
        case None =>
          Σ(e, ρ, σ, ɸ, Fail(s"variable $x not found")::k)
      }
    case Σ(ConstDef(x, e), ρ, σ, ɸ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, ɸ, DoAssign(None, loc, ρ)::RebuildConstDef(x, ρ)::k)
        case None =>
          Σ(e, ρ, σ, ɸ, Fail(s"variable $x not found")::k)
      }

    // FIXME this is dubious
    // We should rebuild the vardefs _only_ if necessary.
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, RebuildVarDef(x, ρ1)::k) =>
      Σ(reify(VarDef(x, v))(σ, ρ), ρ1, σ, ɸ, k)
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, RebuildLetDef(x, ρ1)::k) =>
      Σ(reify(LetDef(x, v))(σ, ρ), ρ1, σ, ɸ, k)
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, RebuildConstDef(x, ρ1)::k) =>
      Σ(reify(ConstDef(x, v))(σ, ρ), ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Assignment.
    ////////////////////////////////////////////////////////////////

    // we can assign to undefined. yep, that's right.
    case Σ(Assign(op, Undefined(), rhs), ρ, σ, ɸ, k) =>
      Σ(rhs, ρ, σ, ɸ, DoAssign(op, FreshLoc(), ρ)::k)

    case Σ(Assign(op, lhs, rhs), ρ, σ, ɸ, k) =>
      Σ(lhs, ρ, σ, ɸ, EvalAssignRhs(op, rhs, ρ)::k)

    case Σ(lhs: Loc, ρ, σ, ɸ, EvalAssignRhs(op, rhs, ρ1)::k) =>
      Σ(rhs, ρ1, σ, ɸ, DoAssign(op, lhs, ρ)::k)

    case Σ(NormalForm(lhs), ρ, σ, ɸ, EvalAssignRhs(op, rhs, ρ1)::k) =>
      Σ(rhs, ρ1, σ, ɸ, RebuildAssign(op, lhs, ρ)::k)

    case Σ(ValueOrResidual(rhs), ρ, σ, ɸ, RebuildAssign(op, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      Σ(reify(Assign(op, lhs, rhs))(σ, ρ), ρ1, σ, ɸ, k)

    case Σ(ValueOrResidual(rhs), ρ, σ, ɸ, DoAssign(None, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      Σ(rhs, ρ1, σ.assign(lhs, rhs, ρ), ɸ, k)

    case Σ(ValueOrResidual(rhs), ρ, σ, ɸ, DoAssign(Some(op), lhs, ρ1)::k) =>
      val right = rhs
      σ.get(lhs) match {
        case Some(Closure(left, _)) =>
          val v = Eval.evalOp(op, left, right)
          Σ(v, ρ1, σ.assign(lhs, v, ρ), ɸ, k)
        case None =>
          // can store lookups fail?
          Σ(rhs, ρ1, σ, ɸ, Fail(s"could not find value at location $lhs")::k)
      }

    case Σ(IncDec(op, lhs), ρ, σ, ɸ, k) =>
      Σ(lhs, ρ, σ, ɸ, DoIncDec(op, ρ)::k)

    case Σ(loc: Loc, ρ, σ, ɸ, DoIncDec(op, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(oldValue, ρ2)) =>
          val binOp = op match {
            case Prefix.++ => Binary.+
            case Prefix.-- => Binary.-
            case Postfix.++ => Binary.+
            case Postfix.-- => Binary.-
            case _ => ???
          }
          val newValue = Eval.evalOp(binOp, oldValue, Num(1))
          val v = op match {
            case Prefix.++ => newValue
            case Prefix.-- => newValue
            case Postfix.++ => oldValue
            case Postfix.-- => oldValue
            case _ => ???
          }
          Σ(v, ρ2, σ.assign(loc, newValue, ρ), ɸ, k)
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(e), ρ, σ, ɸ, DoIncDec(op, ρ1)::k) =>
      Σ(reify(IncDec(op, e))(σ, ρ), ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(LocalAddr(x), ρ, σ, ɸ, k) =>
      ρ.get(x) match {
        case Some(v) =>
          Σ(v, ρ, σ, ɸ, k)
        case None =>
          // The special global name "undefined" evaluates to "undefined".
          if (x == "undefined") {
            val loc = FreshLoc()
            Σ(loc, ρ, σ.assign(loc, Undefined(), ρ), ɸ, k)
          }
          else {
            println(s"variable $x not found... residualizing")
            Σ(reify(Local(x))(σ, ρ), ρ, σ, ɸ, k)
          }
      }

    case Σ(Local(x), ρ, σ, ɸ, k) =>
      Σ(LocalAddr(x), ρ, σ, ɸ, LoadCont(ρ)::k)

    case Σ(Index(a, i), ρ, σ, ɸ, k) =>
      Σ(a, ρ, σ, ɸ, EvalPropertyNameForGet(i, ρ)::k)

    case Σ(loc: Loc, ρ, σ, ɸ, LoadCont(ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(v, ρ2)) =>
          Σ(v, ρ2, σ, ɸ, k)
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
      }

    case Σ(Undefined(), ρ, σ, ɸ, LoadCont(ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, ɸ, k)

    case Σ(ValueOrResidual(e), ρ, σ, ɸ, LoadCont(ρ1)::k) =>
      Σ(reify(e)(σ, ρ), ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Special unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Typeof(e), ρ, σ, ɸ, k) =>
      // void e just discards the value
      Σ(e, ρ, σ, ɸ, DoTypeof(ρ)::k)

    case Σ(Num(v), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("number"), ρ1, σ, ɸ, k)
    case Σ(Bool(v), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("boolean"), ρ1, σ, ɸ, k)
    case Σ(StringLit(v), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("string"), ρ1, σ, ɸ, k)
    case Σ(Undefined(), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("undefined"), ρ1, σ, ɸ, k)
    case Σ(Null(), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("object"), ρ1, σ, ɸ, k)
    case Σ(loc: Loc, ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, _, _, _, _), _)) =>
          Σ(StringLit(typeof), ρ1, σ, ɸ, k)
        case Some(Closure(v, ρ2)) =>
          Σ(v, ρ2, σ, ɸ, DoTypeof(ρ1)::k)
        case None =>
          Σ(StringLit("undefined"), ρ1, σ, ɸ, k)
      }
    case Σ(Residual(e), ρ, σ, ɸ, DoTypeof(ρ1)::k) =>
      Σ(reify(Typeof(e))(σ, ρ), ρ1, σ, ɸ, k)

    case Σ(Void(Residual(e)), ρ, σ, ɸ, k) if e.isPure =>
      // void e just discards the value
      Σ(Undefined(), ρ, σ, ɸ, k)

    case Σ(Void(Residual(e)), ρ, σ, ɸ, k) =>
      // void e just discards the value
      Σ(reify(Void(e))(σ, ρ), ρ, σ, ɸ, k)

    case Σ(Void(e), ρ, σ, ɸ, k) =>
      // void e just discards the value
      Σ(e, ρ, σ, ɸ, SeqCont(Undefined(), ρ)::k)

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Unary(op, e), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, DoUnaryOp(op, ρ)::k)

    case Σ(CvtBool(v), ρ, σ, ɸ, DoUnaryOp(Prefix.!, ρ1)::k) =>
      Σ(Bool(!v), ρ1, σ, ɸ, k)

    case Σ(CvtNum(v), ρ, σ, ɸ, DoUnaryOp(Prefix.~, ρ1)::k) =>
      Σ(Num(~v.toLong), ρ1, σ, ɸ, k)

    case Σ(CvtNum(v), ρ, σ, ɸ, DoUnaryOp(Prefix.+, ρ1)::k) =>
      Σ(Num(+v), ρ1, σ, ɸ, k)

    case Σ(CvtNum(v), ρ, σ, ɸ, DoUnaryOp(Prefix.-, ρ1)::k) =>
      Σ(Num(-v), ρ1, σ, ɸ, k)

    case Σ(ValueOrResidual(v), ρ, σ, ɸ, DoUnaryOp(op, ρ1)::k) =>
      Σ(reify(Unary(op, v))(σ, ρ), ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // Eval the left operand.
    case Σ(Binary(op, e1, e2), ρ, σ, ɸ, k) =>
      Σ(e1, ρ, σ, ɸ, EvalBinaryOpRight(op, e2, ρ)::k)

    // Short-circuit && and ||
    case Σ(v @ CvtBool(false), ρ, σ, ɸ, EvalBinaryOpRight(Binary.&&, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, ɸ, k)

    case Σ(v @ CvtBool(true), ρ, σ, ɸ, EvalBinaryOpRight(Binary.||, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, ɸ, k)

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, EvalBinaryOpRight(op, e2, ρ1)::k) =>
      Σ(e2, ρ1, σ, ɸ, DoBinaryOp(op, v, ρ1)::k)

    // Does the property i exist in loc?
    case Σ(Value(i), ρ, σ, ɸ, DoBinaryOp(Binary.IN, loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
        case _ =>
          Eval.getPropertyAddress(loc, i, σ) match {
            case Some(v) =>
              Σ(Bool(true), ρ1, σ, ɸ, k)
            case None =>
              Σ(Bool(false), ρ1, σ, ɸ, k)
          }
      }

    // We can't just desugar because otherwise the residual won't be correct.
    // x instanceof y
    // ==
    // x.__proto__ === y.prototype
    case Σ(v2: Loc, ρ, σ, ɸ, DoBinaryOp(Binary.INSTANCEOF, v1: Loc, ρ1)::k) =>
      val result = for {
        Closure(FunObject(_, v1protoLoc, _, _, _), _) <- σ.get(v1)
        Closure(v1proto, _) <- v1protoLoc match { case v1protoLoc: Loc => σ.get(v1protoLoc)
                                                  case v1Proto => Some(v1Proto) }
        v2protoLoc <- Eval.getPropertyAddress(v2, StringLit("prototype"), σ)
        Closure(v2proto, _) <- σ.get(v2protoLoc)
      } yield (v1proto, v2proto)

      result match {
        case Some((proto1, proto2)) =>
          Σ(Binary(Binary.===, proto1, proto2), ρ1, σ, ɸ, k)
        case None =>
          Σ(reify(Binary(Binary.INSTANCEOF, v1, v2))(σ, ρ), ρ1, σ, ɸ, k)
      }

    case Σ(ValueOrResidual(v2), ρ, σ, ɸ, DoBinaryOp(Binary.INSTANCEOF, v1, ρ1)::k) =>
      Σ(reify(Binary(Binary.INSTANCEOF, v1, v2))(σ, ρ), ρ1, σ, ɸ, k)

    case Σ(ValueOrResidual(v2), ρ, σ, ɸ, DoBinaryOp(op, v1, ρ1)::k) =>
      val v = Eval.evalOp(op, v1, v2)
      Σ(v, ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Calls and lambda.
    // FIXME
    // Environment handling is completely broken here.
    // See the old SCSC implementation.
    ////////////////////////////////////////////////////////////////

    // A method call "x.m()" passes "x" as "this"
    case Σ(Call(IndexAddr(e, m), args), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, EvalMethodProperty(m, args, ρ)::k)

    case Σ(NormalForm(thisValue), ρ, σ, ɸ, EvalMethodProperty(m, es, ρ1)::k) =>
      Σ(m, ρ1, σ, ɸ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)

    // A non-method call "f()" passes "window" as "this"
    case Σ(Call(fun, args), ρ, σ, ɸ, k) =>
      Σ(fun, ρ, σ, ɸ, EvalArgs(Prim("window"), args, ρ)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, ɸ, EvalArgs(thisValue, Nil, ρ1)::k) =>
      Σ(Empty(), ρ1, σ, ɸ, DoCall(fun, thisValue, Nil, ρ1)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, ɸ, EvalArgs(thisValue, arg::args, ρ1)::k) =>
      Σ(arg, ρ1, σ, ɸ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, ɸ, EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k) =>
      Σ(arg, ρ1, σ, ɸ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, ɸ, EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k) =>
      Σ(Empty(), ρ1, σ, ɸ, DoCall(fun, thisValue, done :+ v, ρ1)::k)

    // Primitives
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("eval"), _, args @ (StringLit(code)::_), ρ1)::k) =>
      val e = scsc.js.Parser.fromString(code)
      e match {
        case Some(e) =>
          Σ(e, ρ1, σ, ɸ, k)
        case None =>
          Σ(reify(Call(Prim("eval"), args))(σ, ρ), ρ1, σ0, ɸ, k)
      }
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("eval"), _, Value(v)::_, ρ1)::k) =>
      Σ(v, ρ1, σ, ɸ, k)
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("eval"), _, Nil, ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, ɸ, k)
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("isNaN"), _, CvtNum(v)::_, ρ1)::k) =>
      Σ(Bool(v.isNaN), ρ1, σ, ɸ, k)
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("isFinite"), _, CvtNum(v)::_, ρ1)::k) =>
      Σ(Bool(!v.isInfinite), ρ1, σ, ɸ, k)
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("isNaN"), _, Nil, ρ1)::k) =>
      Σ(Bool(true), ρ1, σ, ɸ, k)
    case Σ(_, ρ, σ, ɸ, DoCall(Prim("isFinite"), _, Nil, ρ1)::k) =>
      Σ(Bool(false), ρ1, σ, ɸ, k)

    case Σ(_, ρ, σ, ɸ, DoCall(FunObject(_, _, xs, Some(e), _), thisValue, args, ρ1)::k) =>
      // TODO: to ensure all non-garbage values in the heap are accessible
      // from the environment, don't shadow variables. Instead, append
      // the frame number to all variable references.

      // println("rebuilding 10 " + Let(x, arg, e).show)
      val locs = ("this"::xs) map { _ => FreshLoc() }
      val ρ2 = (("this"::xs) zip locs).foldLeft(ρ1) {
        case (ρ1, (x, loc)) =>
          ρ1 + (x -> loc)
      }
      // Pad the arguments with undefined.
      def pad(locs: List[Loc], args: List[Exp]): List[Exp] = (locs, args) match {
        case (Nil, _) => Nil
        case (_::locs, Nil) => Undefined()::pad(locs, Nil)
        case (_::locs, arg::args) => arg::pad(locs, args)
      }
      val args2 = pad(locs, thisValue::args)
      val σ1 = (locs zip args2).foldLeft(σ) {
        case (σ, (loc, v)) =>
          σ + (loc -> Closure(v, ρ1))
      }
      Σ(e, ρ2, σ1, ɸ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.

    // The function is not a lambda. Residualize the call. Clear the store since we have no idea what the function
    // will do to the store.
    case Σ(_, ρ, σ, ɸ, DoCall(fun, thisValue, args, ρ1)::k) =>
      Σ(reify(Call(fun, args))(σ, ρ), ρ1, σ0, ɸ, k)

    // Wrap v in a let.
    case Σ(NormalForm(v), ρ, σ, ɸ, RebuildLet(xs, args, ρ1)::k) =>
      val ss = (xs zip args) collect {
        case (x, e) if (fv(v) contains x) => LetDef(x, e)
      }
      if (ss.nonEmpty) {
        val block = ss.foldRight(v) {
          case (s1, s2) => Seq(s1, s2)
        }
        Σ(reify(block)(σ, ρ), ρ1, σ, ɸ, k)
      }
      else {
        Σ(v, ρ1, σ, ɸ, k)
      }

    ////////////////////////////////////////////////////////////////
    // Return. Pop the continuations until we hit the caller.
    ////////////////////////////////////////////////////////////////

    case Σ(Return(Some(e)), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, DoReturn()::k)
    case Σ(Return(None), ρ, σ, ɸ, k) =>
      Σ(Undefined(), ρ, σ, ɸ, DoReturn()::k)

    case Σ(ValueOrResidual(v), ρ, σ, ɸ, DoReturn()::k) =>
      Σ(Undefined(), ρ, σ, ɸ, Returning(v)::k)

    // Once we hit the call frame, evaluate the return value.
    // Then pop the call frame using the NormalForm rule.
    case Σ(res, ρ, σ, ɸ, Returning(v)::CallFrame(ρ1)::k) =>
      Σ(v, ρ1, σ, ɸ, k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, ɸ, Returning(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, ɸ, a::Returning(e)::k)

    case Σ(v, ρ, σ, ɸ, Returning(e)::_::k) =>
      Σ(v, ρ, σ, ɸ, Returning(e)::k)

    // If we run off the end of the function body, act like we returned normally.
    // This also runs after evaluating the return value after a return.
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, CallFrame(ρ1)::k) =>
      Σ(v, ρ1, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Throw. This is implemented similarly to Return.
    ////////////////////////////////////////////////////////////////

    case Σ(Throw(e), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, DoThrow()::k)

    case Σ(ValueOrResidual(v), ρ, σ, ɸ, DoThrow()::k) =>
      Σ(Undefined(), ρ, σ, ɸ, Throwing(v)::k)

    // If we're throwing and we hit a try block,
    // evaluate the finally block and rethrow.
    case Σ(v, ρ, σ, ɸ, Throwing(e)::FinallyFrame(fin, ρ1)::k) =>
      Σ(fin, ρ1, σ, ɸ, Throwing(e)::k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, ɸ, Throwing(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, ɸ, a::Throwing(e)::k)

    case Σ(v, ρ, σ, ɸ, Throwing(e)::_::k) =>
      Σ(v, ρ, σ, ɸ, Throwing(e)::k)

    // Run the finally block, if any. Then restore the value.
    // And pass it to k.
    case Σ(ValueOrResidual(v), ρ, σ, ɸ, FinallyFrame(fin, ρ1)::k) =>
      Σ(fin, ρ1, σ, ɸ, SeqCont(v, ρ)::k)

    case Σ(TryCatch(e, cs), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, CatchFrame(cs, ρ)::k)

    case Σ(TryFinally(e, fin), ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, FinallyFrame(fin, ρ)::k)


    ////////////////////////////////////////////////////////////////
    // Objects and arrays.
    ////////////////////////////////////////////////////////////////

    // new Point(x, y)
    // creates a new empty object
    // binds the object to this
    // sets this.__proto__ to Point.prototype
    // calls the Point function

    case Σ(NewCall(fun, args), ρ, σ, ɸ, k) =>
      val loc = FreshLoc()
      Σ(fun, ρ, σ, ɸ, InitProto(loc, ρ)::LoadCont(ρ)::EvalArgs(loc, args, ρ)::SeqCont(loc, ρ)::k)

    case Σ(fun, ρ, σ, ɸ, InitProto(loc, ρ1)::k) =>
      val v1 = FunObject("object", reify(Index(fun, StringLit("prototype")))(σ, ρ), Nil, None, Nil)
      Σ(fun, ρ, σ.assign(loc, v1, ρ1), ɸ, k)

    case Σ(Delete(IndexAddr(a, i)), ρ, σ, ɸ, k) =>
      Σ(a, ρ, σ, ɸ, EvalPropertyNameForDel(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, ɸ, EvalPropertyNameForDel(i, ρ1)::k) =>
      Σ(i, ρ1, σ, ɸ, DoDeleteProperty(a, ρ1)::k)

    case Σ(Value(i), ρ, σ, ɸ, DoDeleteProperty(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              val removed = props filter {
                case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => false
                case _ => true
              }
              Σ(loc, ρ1, σ.assign(loc, FunObject(typeof, proto, xs, body, removed), ρ2), ɸ, k)
            case None =>
              // The field isn't there anyway.
              Σ(loc, ρ1, σ, ɸ, k)
          }
        case Some(Closure(v, ρ2)) =>
          Σ(loc, ρ1, σ, ɸ, k)
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, ɸ, DoDeleteProperty(ValueOrResidual(a), ρ1)::k) =>
      Σ(reify(Delete(IndexAddr(a, i)))(σ, ρ), ρ1, σ, ɸ, k)

    case Σ(IndexAddr(a, i), ρ, σ, ɸ, k) =>
      Σ(a, ρ, σ, ɸ, EvalPropertyNameForSet(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, ɸ, EvalPropertyNameForSet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, ɸ, GetPropertyAddressOrCreate(a, ρ1)::k)

    case Σ(Value(i), ρ, σ, ɸ, GetPropertyAddressOrCreate(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              Σ(v, ρ2, σ, ɸ, k)
            case None =>
              // FIXME: maybe the property key is reified?
              // I don't think this can happen, though.

              // The field is missing.
              // Create it.
              val fieldLoc = FreshLoc()
              val σ1 = σ.assign(loc, FunObject(typeof, proto, xs, body, props :+ Property(i, fieldLoc, None, None)), ρ2)
              val σ2 = σ1.assign(fieldLoc, Undefined(), ρ2)
              Σ(fieldLoc, ρ1, σ2, ɸ, k)
          }
        case Some(Closure(v, ρ2)) =>
          Σ(Undefined(), ρ1, σ, ɸ, k)
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(a), ρ, σ, ɸ, EvalPropertyNameForGet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, ɸ, GetProperty(a, ρ1)::k)

    // restrict the property to values to ensure == during property lookup works correctly
    // otherwise, a[f()] will result in undefined rather than a reified access
    case Σ(Value(i), ρ, σ, ɸ, GetProperty(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              Σ(v, ρ2, σ, ɸ, LoadCont(ρ1)::k)
            case None =>
              // Lookup the __proto__ field.
              // If found, load the property from the prototype.
              // Otherwise, return undefined.
              proto match {
                case protoLoc: Loc =>
                  Σ(i, ρ1, σ, ɸ, GetProperty(protoLoc, ρ1)::k)
                case _ =>
                  Σ(Undefined(), ρ1, σ, ɸ, k)
              }
          }
        case Some(Closure(v, ρ2)) =>
          Σ(Undefined(), ρ1, σ, ɸ, k)
        case None =>
          Σ(loc, ρ, σ, ɸ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, ɸ, GetProperty(ValueOrResidual(a), ρ1)::k) =>
      Σ(reify(Index(a, i))(σ, ρ), ρ1, σ, ɸ, k)

    // Create an empty object
    // Initialize a non-empty object.
    case Σ(ObjectLit(ps), ρ, σ, ɸ, k) =>
      val loc = FreshLoc()
      val v = FunObject("object", Prim("Object.prototype"), Nil, None, Nil)
      val seq = ps.reverse.foldRight(loc: Exp) {
        case (Property(prop, value, _, _), rest) =>
          Seq(Assign(None, IndexAddr(loc, prop), value), rest)
        case _ => ???
      }
      Σ(seq, ρ, σ.assign(loc, v, ρ), ɸ, k)

    // Put a lambda in the heap.
    case Σ(Lambda(xs, e), ρ, σ, ɸ, k) =>
      val loc = FreshLoc()
      val v = FunObject("function", Prim("Function.prototype"), xs, Some(e), Nil)
      Σ(loc, ρ, σ.assign(loc, v, ρ), ɸ, k)

    // Array literals desugar to objects
    case Σ(ArrayLit(es), ρ, σ, ɸ, k) =>
      val loc = FreshLoc()
      val v = FunObject("object", Prim("Array.prototype"), Nil, None, Nil)
      val len = Seq(Assign(None, IndexAddr(loc, StringLit("length")), Num(es.length)), loc)
      val seq = es.reverse.zipWithIndex.foldRight(len: Exp) {
        case ((value, i), rest) =>
          Seq(Assign(None, IndexAddr(loc, StringLit(i.toLong.toString)), value), rest)
      }
      Σ(seq, ρ, σ.assign(loc, v, ρ), ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Properties
    ////////////////////////////////////////////////////////////////

/*
    // Done with all properties, put the object in the store.
    case Σ(v @ Property(ValueOrResidual(vk), ValueOrResidual(vv), _, _), ρ, σ, InitObject(loc, Nil, vs, ρ1)::k) =>
      val vs2 = vs :+ v
      // copy the properties to the heap
      val locs = vs2 map { _ => FreshLoc() }
      val zipped = locs zip vs2
      val props = zipped map {
        case (loc, Property(vk, vv, g, s)) =>
          Property(vk, loc, g, s)
        case (loc, v) =>
          v
      }
      // Add the properties to the object (which should already exist in the heap)
      val σ1 = σ.get(loc) match {
        case Some(Closure(FunObject(typeof, proto, params, body, props0), ρ2)) =>
          σ.assign(loc, FunObject(typeof, proto, params, body, props0 ++ props), ρ2)
        case Some(_) =>
          ???
        case None =>
          σ.assign(loc, FunObject("object", Prim("Object.prototype"), Nil, None, props), ρ1)
          ???
      }
      val σ2 = zipped.foldLeft(σ1) {
        case (σ, (loc, Property(_, vv, _, _))) =>
          σ.assign(loc, vv, ρ1)
      }
      Σ(loc, ρ1, σ2, k)

    // Done with a property, go to the next one.
    case Σ(v @ Property(ValueOrResidual(vk), ValueOrResidual(vv), _, _), ρ, σ, InitObject(loc, e::es, vs, ρ1)::k) =>
      Σ(e, ρ1, σ, InitObject(loc, es, vs :+ v, ρ1)::k)
*/

    // evaluate a property
    case Σ(Property(ValueOrResidual(x), e, _, _), ρ, σ, ɸ, k) if ! e.isValue =>
      Σ(e, ρ, σ, ɸ, WrapProperty(x, ρ)::k)

    case Σ(Property(ek, ev, _, _), ρ, σ, ɸ, k) =>
      Σ(ek, ρ, σ, ɸ, EvalPropertyValue(ev, ρ)::k)

    case Σ(ValueOrResidual(vv), ρ, σ, ɸ, WrapProperty(vk, ρ1)::k) =>
      Σ(Property(vk, vv, None, None), ρ1, σ, ɸ, k)

    case Σ(ValueOrResidual(vk), ρ, σ, ɸ, EvalPropertyValue(ev, ρ1)::k) =>
      Σ(ev, ρ1, σ, ɸ, WrapProperty(vk, ρ1)::k)

    ////////////////////////////////////////////////////////////////
    // Other cases.
    ////////////////////////////////////////////////////////////////

    // Don't implement with.
    case Σ(With(exp, body), ρ, σ, ɸ, k) =>
      Σ(reify(With(exp, body))(σ, ρ), ρ, σ, ɸ, k)

    ////////////////////////////////////////////////////////////////
    // Catch all.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(e, ρ, σ, ɸ, k) =>
      Σ(e, ρ, σ, ɸ, Fail(s"no step defined for $s")::k)
  }

  // Check for termination at these nodes.
  // In SCSC, we only checked at Local nodes, but here we need to check
  // loops also since we can have non-termination evaluating any variables.
  object CheckHistory {
    def unapply(e: Exp) = e match {
      case Local(x) => Some(e)
      case While(label, test, body) => Some(e)
      case DoWhile(label, body, test) => Some(e)
      case For(label, init, test, iter, body) => Some(e)
      case ForEach(label, init, test, iter, body) => Some(e)
      case ForIn(label, init, iter, body) => Some(e)
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
    import HE._

    var t = maxSteps * 100
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
        case Σ(NormalForm(v), ρ, σ, ɸ, Nil) =>
          return unreify(reify(v)(σ, ρ))

        case Σ(e, _, σ, ɸ, Fail(s)::k) =>
          println(s"FAIL $s")
          return Lambda("error"::Nil, e)

        case s0 @ Σ(e, ρ, σ, ɸ, k) =>
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
      println("term " + toTerm(s).map { case (u, n) => s"${u.show} in $n steps" }.getOrElse("FAIL"))

      s match {
        // stop when we have a value with the empty continuation.
        case Σ(NormalForm(v), ρ, σ, ɸ, Nil) =>
          return unreify(reify(v)(σ, ρ))

        case Σ(e, ρ, σ, ɸ, Fail(s)::k) =>
          println(s"FAIL $s")
          return Lambda("error"::Nil, e)

        case s0 @ Σ(focus, ρ, σ, ɸ, k) =>
          val s1 = step(s0)

          s1 match {
            case Σ(CheckHistory(focus1), ρ1, σ, ɸ, k1) =>
              s = hist.foldRight(s1) {
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
                      case Some((t1, _)) =>
                        return t1
                      case None =>
                        return Lambda("error"::Nil, focus1)
                    }
                  }
                  else {
                    // keep going
                    s1
                  }
                case (prev, s2) =>
                  s2
              }

              hist += s

            case s1 =>
              s = s1
          }
      }
    }

    throw new RuntimeException("unreachable")
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
