package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar

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
object Step {
  import Machine._
  import Continuations._
  import Residualization._
  import CESK._

  // Statements evaluate to Empty or a residual
  // Expressions evaluate to a value or a residual.
  // Expressions (e.g., names and property accesses) may evaluate to a memory location.
  def step(s: St): St = s match {
    // Done!
    case s @ Σ(ValueOrResidual(_), _, _, Nil) => s

    // Fail
    case s @ Σ(_, _, _, Fail(_)::k) => s

    // case s @ Σ(ValueOrResidual(_), _, _, k::_) => k.dispatch(s)
    // case s @ Σ(e, _, _, k::_) => e.dispatch(s)

    ////////////////////////////////////////////////////////////////
    // Scopes.
    ////////////////////////////////////////////////////////////////

    case Σ(Scope(s), ρ, σ, k) =>
      // Go through all the bindings in the block and add them to the environment
      // as `undefined`. As we go thorugh the block, we'll initialize the variables.
      object CollectBindings extends Rewriter {
        var bindings: Vector[(Name, Exp)] = Vector()
        override def rewrite(e: Exp) = e match {
          case VarDef(x, e) =>
            bindings = bindings :+ ((x, e))
            super.rewrite(e)
          case _: Lambda | _: Residual | _: Scope =>
            // don't recurse on these
            e
          case e =>
            super.rewrite(e)
        }
      }
      CollectBindings.rewrite(s)
      val bindings = CollectBindings.bindings

      val locs = bindings map { case (x, e) => Path(FreshLoc().address, Local(x)) }
      val ρ1 = (bindings zip locs).foldLeft(ρ) {
        case (ρ, ((x, _), loc)) => ρ + (x -> Loc(loc.address))
      }
      val σ1 = locs.foldLeft(σ) {
        case (σ, loc) => σ.assign(loc, Undefined(), ρ1)
      }

      // MakeTrees ensures builds the tree so that function bindings
      // are evaluated first, so we don't have to initialize them explicitly.
      // Also all bindings should be either to lambdas or to undefined.
      Σ(s, ρ1, σ1, RebuildLet(bindings.toList.map(_._1), bindings.toList.map(_._2), ρ)::RebuildScope(ρ1)::k)

    case Σ(Residual(e), ρ, σ, RebuildScope(ρ1)::k) =>
      // val vars = fv(e)
      // val e2 = vars.foldRight(e) {
      //   case (x, e) => Seq(VarDef(x, Undefined()), e)
      // }
      Σ(Residual(Scope(e)), ρ, σ, k)

    case Σ(Value(e), ρ, σ, RebuildScope(ρ1)::k) =>
      Σ(e, ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Conditionals
    // ? : and if/else are handled identically, duplicating code
    ////////////////////////////////////////////////////////////////

    // if e then s1 else s2
    case Σ(IfElse(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, BranchCont(SeqCont(s1, ρ)::Nil,
                               SeqCont(s2, ρ)::Nil,
                               RebuildIfElseTest(s1, s2, ρ)::Nil)::k)

    // e ? s1 : s2
    case Σ(Cond(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, BranchCont(SeqCont(s1, ρ)::Nil,
                               SeqCont(s2, ρ)::Nil,
                               RebuildCondTest(s1, s2, ρ)::Nil)::k)

    case Σ(v @ CvtBool(true), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, kt ++ k)

    case Σ(v @ CvtBool(false), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, kf ++ k)

    // Neither true nor false, so residualize
    case Σ(Residual(e), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(Residual(e), ρ, σ, kr ++ k)

    // this should not happen
    case Σ(Value(e), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      tryReify(e)(σ, ρ) match {
        case Some(e) =>
          Σ(e, ρ, Eval.simulateStore(e)(σ, ρ), kr ++ k)
        case None =>
          Σ(e, ρ, σ, Fail(s"could not reify $e")::k)
      }

    // Rebuilding ? : and if-else nodes.
    // The logic is duplicated.

    // Evaluate the test to a (residual) value.
    // Save the store and evaluate the true branch.
    case Σ(ValueOrResidual(test), ρ, σAfterTest, RebuildCondTest(s1, s2, ρ0)::k) =>
      val σ = extendWithCond(test, σAfterTest, ρ0, true)
      Σ(s1, ρ0, σ, RebuildCondTrue(test, s2, σAfterTest, ρ0)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(ValueOrResidual(s1), ρ1, σ1, RebuildCondTrue(test, s2, σAfterTest, ρ0)::k) =>
      tryReify(s1)(σ1, ρ1) match {
        case Some(s1) =>
          val σ = extendWithCond(test, σAfterTest, ρ0, false)
          Σ(s2, ρ0, σ, RebuildCondFalse(test, s1, σ1, ρ0)::k)
        case None =>
          Σ(s1, ρ1, σ1, Fail(s"could not reify $s1")::k)
      }

    // Rebuild and merge the post-true and post-false stores.
    case Σ(ValueOrResidual(s2), ρ2, σ2, RebuildCondFalse(test, s1, σ1, ρ0)::k) =>
      tryReify(s2)(σ2, ρ2) match {
        case Some(s2) =>
          Σ(Residual(Cond(test, s1, s2)), ρ0, σ1.merge(σ2, ρ0), k)
        case None =>
          Σ(s2, ρ2, σ2, Fail(s"could not reify $s2")::k)
      }

    case Σ(ValueOrResidual(test), ρ, σAfterTest, RebuildIfElseTest(s1, s2, ρ0)::k) =>
      Σ(s1, ρ0, σAfterTest, RebuildIfElseTrue(test, s2, σAfterTest, ρ0)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(ValueOrResidual(s1), ρ1, σ1, RebuildIfElseTrue(test, s2, σAfterTest, ρ0)::k) =>
      tryReify(s1)(σ1, ρ1) match {
        case Some(s1) =>
          Σ(s2, ρ0, σAfterTest, RebuildIfElseFalse(test, s1, σ1, ρ0)::k)
        case None =>
          Σ(s1, ρ1, σ1, Fail(s"could not reify $s1")::k)
      }

    // Rebuild and merge the post-true and post-false stores.
    case Σ(ValueOrResidual(s2), ρ2, σ2, RebuildIfElseFalse(test, s1, σ1, ρ0)::k) =>
      tryReify(s2)(σ2, ρ2) match {
        case Some(s2) =>
          Σ(Residual(IfElse(test, s1, s2)), ρ0, σ1.merge(σ2, ρ0), k)
        case None =>
          Σ(s2, ρ2, σ2, Fail(s"could not reify $s2")::k)
      }

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

    case Σ(For(label, Empty(), test, iter, body), ρ, σ, k) =>
      Σ(test, ρ, σ, BranchCont(
                      SeqCont(body, ρ)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ)::BreakFrame(label)::Nil,
                      SeqCont(Undefined(), ρ)::Nil,
                      RebuildForTest(label, test, iter, body, ρ)::Nil)::k)

    case Σ(For(label, init, test, iter, body), ρ, σ, k) =>
      Σ(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, k)

    // TODO interpreter for (x in y) { }
    // eval iter
    // eval init as lhs
    // eval iter
    // if iter is a funobject, walk through the properties
    // or do we call some function?
    // For now, just eval the body.
    case Σ(ForIn(label, init, iter, body), ρ, σ, k) =>
      Σ(body, ρ, σ, RebuildForIn(label, init, iter, ρ)::k)

    case Σ(ValueOrResidual(body), ρ, σ, RebuildForIn(label, init, iter, ρ1)::k) =>
      tryReify(ForIn(label, init, iter, body))(σ, ρ) match {
        case Some(s) =>
          Σ(s, ρ, Eval.simulateStore(s)(σ, ρ), k)
        case None =>
          Σ(body, ρ, σ, Fail(s"could not reify ${ForIn(label, init, iter, body)}")::k)
      }

    // do body while test
    case Σ(DoWhile(label, body, test), ρ, σ, k) =>
      Σ(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)

    // just desugar into a for loop
    case Σ(While(label, test, body), ρ, σ, k) =>
      Σ(For(label, Empty(), test, Empty(), body), ρ, σ, k)

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
    case Σ(ValueOrResidual(test), ρ, σ, RebuildForTest(label0, test0, iter0, body0, ρ1)::k) =>
      Σ(body0, ρ1, σ, RebuildForBody(label0, test, test0, iter0, body0, ρ)::k)

    case Σ(ValueOrResidual(body1), ρ, σ, RebuildForBody(label0, test1, test0, iter0, body0, ρ1)::k) =>
      Σ(iter0, ρ, σ, RebuildForIter(label0, body1, test1, test0, iter0, body0, ρ1)::k)

    // Discard the store.
    case Σ(ValueOrResidual(iter1), ρ, σ, RebuildForIter(label, body1, test1, test0, Empty(), body0, ρ1)::k) =>
      tryReify(IfElse(test1, Seq(body1, Seq(iter1, While(label, test0, body0))), Undefined()))(σ, ρ) match {
        case Some(s) =>
          Σ(s, ρ1, Eval.simulateStore(s)(σ, ρ1), k)
        case None =>
          Σ(iter1, ρ, σ, Fail(s"could not reify if-while")::k)
      }

    case Σ(ValueOrResidual(iter1), ρ, σ, RebuildForIter(label, body1, test1, test0, iter0, body0, ρ1)::k) =>
      tryReify(IfElse(test1, Seq(body1, Seq(iter1, For(label, Empty(), test0, iter0, body0))), Undefined()))(σ, ρ) match {
        case Some(s) =>
          Σ(s, ρ1, Eval.simulateStore(s)(σ, ρ1), k)
        case None =>
          Σ(iter1, ρ, σ, Fail(s"could not reify for")::k)
      }

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

    case Σ(Break(label), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, Breaking(label)::k)
    case Σ(Continue(label), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, Continuing(label)::k)

    case Σ(v, ρ, σ, Breaking(None)::BreakFrame(_)::k) =>
      Σ(v, ρ, σ, k)
    case Σ(v, ρ, σ, Continuing(None)::ContinueFrame(_)::k) =>
      Σ(v, ρ, σ, k)

    case Σ(v, ρ, σ, Breaking(Some(x))::BreakFrame(Some(y))::k) if x == y =>
      Σ(v, ρ, σ, k)
    case Σ(v, ρ, σ, Continuing(Some(x))::ContinueFrame(Some(y))::k) if x == y =>
      Σ(v, ρ, σ, k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, Breaking(label)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::Breaking(label)::k)
    case Σ(v, ρ, σ, Continuing(label)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::Continuing(label)::k)

    case Σ(v, ρ, σ, Breaking(label)::_::k) =>
      Σ(v, ρ, σ, Breaking(label)::k)
    case Σ(v, ρ, σ, Continuing(label)::_::k) =>
      Σ(v, ρ, σ, Continuing(label)::k)

    // discard useless break and continue frames
    case Σ(ValueOrResidual(v), ρ, σ, BreakFrame(_)::k) =>
      Σ(v, ρ, σ, k)
    case Σ(ValueOrResidual(v), ρ, σ, ContinueFrame(_)::k) =>
      Σ(v, ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Blocks.
    // As usual, residual handling is difficult.
    ////////////////////////////////////////////////////////////////

    case Σ(Empty(), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, k)

    // reassociate to reduce the size of the residual.
    case Σ(Seq(Seq(s1, s2), s3), ρ, σ, k) =>
      Σ(Seq(s1, Seq(s2, s3)), ρ, σ, k)

    case Σ(Seq(s1, s2), ρ, σ, k) =>
      Σ(s1, ρ, σ, SeqCont(s2, ρ)::k)

    case Σ(Residual(s1), ρ, σ, SeqCont(s2, ρ1)::k) =>
      Σ(s2, ρ1, σ, RebuildSeq(s1, ρ)::k)

    // Discard the value and evaluate the sequel.
    case Σ(Value(_), ρ, σ, SeqCont(s2, ρ1)::k) =>
      Σ(s2, ρ, σ, k)

    case Σ(Value(s2), ρ, σ, RebuildSeq(s1, ρ1)::k) =>
      tryReify(s2)(σ, ρ) match {
        case Some(s2) =>
          Σ(Residual(Seq(s1, s2)), ρ1, σ, k)
        case None =>
          Σ(s2, ρ, σ, Fail(s"could not reify $s2")::k)
      }

    case Σ(Residual(s2), ρ, σ, RebuildSeq(s1, ρ1)::k) =>
      Σ(Residual(Seq(s1, s2)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Definitions.
    ////////////////////////////////////////////////////////////////

    // Definitions eval to undefined.
    // Look up the location, which should have been added to the environment
    // when we entered the block.
    // Then run the initializer, assigning to the location.
    // The DoAssign continuation should leave the initializer in the focus,
    // but we should evaluate to undefined, so add block continuation for that.
    case Σ(VarDef(x, lam @ Lambda(xs, e)), ρ, σ, k) =>
      // Special case lambdas because we need to set the name of the heap object.
      // var Point = function (x, y) { this.x = x; this.y = y}
      // ==
      // var Point = { __code__: fun..., prototype: { __proto__: Function.prototype } }
      ρ.get(x) match {
        case Some(loc) =>
          val lambdaPath = Local(x)
          val lambdaLoc = Path(FreshLoc().address, lambdaPath)
          val protoPath = Index(Local(x), StringLit("prototype"))
          val protoLoc = Path(FreshLoc().address, protoPath)
          val proto = FunObject("object", Eval.getPrimAddress(Prim("Function.prototype")), Nil, None, Nil)
          val funObj = FunObject("function", Eval.getPrimAddress(Prim("Function.prototype")), xs, Some(e), Nil)
          // TODO Whenever we create a fresh location, we add a temporary to the environment
          // to ensure it's reachable in case we have to
          // residualize before making it reachable from x.
          // TODO: the store has to be robust to deletions.
          // Sanitizing the heap can delete locations from the heap.
          // But really these should map to UNKNOWN rather than to nothing.
          // The location is valid (in one heap), just not known.
          val ass = List(
            Assign(None, LocalAddr(x), lambdaLoc),
            Assign(None, IndexAddr(lambdaLoc, StringLit("name")), StringLit(x)),
            Assign(None, IndexAddr(lambdaLoc, StringLit("length")), Num(xs.length)),
            Assign(None, IndexAddr(lambdaLoc, StringLit("prototype")), protoLoc)
          )

          val s2 = ass.reverse.foldRight(Undefined(): Exp) {
            case (e, rest) => Seq(e, rest)
          }

          val σ2 = σ.assign(lambdaLoc, funObj, ρ).assign(protoLoc, proto, ρ)

          Σ(s2, ρ, σ2, k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }

    case Σ(VarDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, DoAssign(None, Path(loc.address, Local(x)), ρ)::RebuildLet(x::Nil, Undefined()::Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }
    case Σ(Residual(Assign(None, y, e)), ρ, σ, RebuildVarDef(x, ρ1)::k) if (x == y) =>
      Σ(Residual(VarDef(x, e)), ρ1, σ, k)
    case Σ(Residual(v), ρ, σ, RebuildVarDef(x, ρ1)::k) if (fv(v) contains x) =>
      Σ(Residual(VarDef(x, v)), ρ1, σ, k)
    case Σ(Residual(v), ρ, σ, RebuildVarDef(x, ρ1)::k) =>
      Σ(Residual(v), ρ1, σ, k)
    case Σ(Value(v), ρ, σ, RebuildVarDef(x, ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Assignment.
    ////////////////////////////////////////////////////////////////

    // we can assign to undefined. yep, that's right.
    case Σ(Assign(None, Undefined(), rhs), ρ, σ, k) =>
      Σ(rhs, ρ, σ, k)

    case Σ(Assign(Some(op), Undefined(), rhs), ρ, σ, k) =>
      Σ(rhs, ρ, σ, DoBinaryOp(op, Undefined(), ρ)::k)

    case Σ(Assign(op, lhs, rhs), ρ, σ, k) =>
      Σ(lhs, ρ, σ, EvalAssignRhs(op, rhs, lhs, ρ)::k)

    case Σ(lhs: Path, ρ, σ, EvalAssignRhs(op, rhs, lhsPath, ρ1)::k) =>
      Σ(rhs, ρ1, σ, DoAssign(op, lhs, ρ)::k)

    // We don't know the lhs, so we leave the assignment in the residual.
    case Σ(Value(lhs), ρ, σ, EvalAssignRhs(op, rhs, lhsPath, ρ1)::k) =>
      tryReify(lhs)(σ, ρ) match {
        case Some(lhs) =>
          Σ(rhs, ρ1, σ, RebuildAssign(op, lhs, ρ)::k)
        case None =>
          Σ(lhs, ρ, σ, Fail(s"could not reify $lhs")::k)
      }

    case Σ(Residual(lhs), ρ, σ, EvalAssignRhs(op, rhs, lhsPath, ρ1)::k) =>
      Σ(rhs, ρ1, σ, RebuildAssign(op, lhs, ρ)::k)

    case Σ(Residual(rhs), ρ, σ, RebuildAssign(op, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      // Since we don't know what we just assigned to..., we have to sanitize
      // the store.
      // Remove all locations in the store that could alias lhs.
      // That is, all locations that are not ONLY reachable from the environment.
      // If they were reachable only from the environment, the lhs would have
      // resolved.
      Σ(Residual(Assign(op, lhs, rhs)), ρ1, Eval.simulateStore(Assign(op, lhs, rhs))(σ, ρ1), k)

    case Σ(Value(rhs), ρ, σ, RebuildAssign(op, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      // Since we don't know what we just assigned to..., we have to sanitize
      // the store.
      // Remove all locations in the store that could alias lhs.
      // That is, all locations that are not ONLY reachable from the environment.
      // If they were reachable only from the environment, the lhs would have
      // resolved.
      tryReify(rhs)(σ, ρ) match {
        case Some(rhs) =>
          Σ(Residual(Assign(op, lhs, rhs)), ρ1, Eval.simulateStore(Assign(op, lhs, rhs))(σ, ρ1), k)
        case None =>
          Σ(rhs, ρ, σ, Fail(s"could not reify $rhs")::k)
      }

    case Σ(Value(rhs), ρ, σ, DoAssign(None, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      Σ(rhs, ρ1, σ.assign(lhs, rhs, ρ), k)

    case Σ(Residual(Pure(rhs)), ρ, σ, DoAssign(None, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      // If the rhs is pure, put it in the heap;
      // otherwise, generate a fresh var and put that
      // in the heap.
      Σ(Residual(rhs), ρ1, σ.assign(lhs, Residual(rhs), ρ), k)

    case Σ(Residual(rhs), ρ, σ, DoAssign(None, lhs, ρ1)::k) =>
      // residualize the assignment
      // and update the store with the residual path
      // or maybe just map the lhs to nothing forcing
      // it to get residualized as the path every time?
      Σ(Residual(Assign(None, lhs, rhs)), ρ1, σ.assign(lhs, Residual(lhs.path), ρ1), k)

    case Σ(Value(rhs), ρ, σ, DoAssign(Some(op), lhs @ Path(addr, lhsPath), ρ1)::k) =>
      val right = rhs
      σ.get(Loc(addr)) match {
          case Some(ValClosure(left)) =>
          val v = Eval.evalOp(op, left, right)
          // Update the path to a more recent path
          Σ(v, ρ1, σ.assign(lhs, v, ρ), k)
        case _ =>
          // can store lookups fail?
          Σ(Residual(Assign(Some(op), lhsPath, reify(rhs)(σ, ρ))), ρ1, σ, k)
      }

    // case Σ(Residual(Pure(rhs)), ρ, σ, DoAssign(Some(op), lhs, ρ1)::k) =>
    //   val right = Residual(rhs)
    //   σ.get(lhs) match {
    //     case Some(Closure(left, _)) =>
    //       val v = Eval.evalOp(op, left, right)
    //       Σ(v, ρ1, σ.assign(lhs, v, ρ), k)
    //     case None =>
    //       // can store lookups fail?
    //       Σ(rhs, ρ1, σ, Fail(s"could not find value at location $lhs")::k)
    //   }

    case Σ(Residual(rhs), ρ, σ, DoAssign(Some(op), lhs, ρ1)::k) =>
      // We have an impure, rhs, generate a residual assignment
      // and put the path to the lhs in the store so we don't
      // duplicate work.
      val path = lhs.path
      Σ(Residual(Assign(Some(op), path, rhs)), ρ1,
        σ.assign(lhs, Residual(path), ρ1), k)

    case Σ(IncDec(op, lhs), ρ, σ, k) =>
      Σ(lhs, ρ, σ, DoIncDec(op, ρ)::k)

    case Σ(loc @ Path(addr, path), ρ, σ, DoIncDec(op, ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(ValClosure(oldValue)) =>
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
          Σ(v, ρ1, σ.assign(loc, newValue, ρ), k)
        case _ =>
          Σ(Residual(IncDec(op, path)), ρ, σ, k)
      }

    case Σ(Value(e), ρ, σ, DoIncDec(op, ρ1)::k) =>
      tryReify(e)(σ, ρ) match {
        case Some(e) =>
          Σ(Residual(IncDec(op, e)), ρ1, Eval.simulateStore(IncDec(op, e))(σ, ρ1), k)
        case None =>
          Σ(e, ρ, σ, Fail(s"could not reify $e")::k)
      }

    case Σ(Residual(e), ρ, σ, DoIncDec(op, ρ1)::k) =>
      Σ(Residual(IncDec(op, e)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(LocalAddr(x), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(Loc(addr)) =>
          Σ(Path(addr, LocalAddr(x)), ρ, σ, k)
        case None =>
          // The special global name "undefined" evaluates to "undefined".
          if (x == "undefined") {
            val loc = Path(FreshLoc().address, Undefined())
            Σ(loc, ρ, σ.assign(loc, Undefined(), ρ), k)
          }
          else {
            println(s"variable $x not found... residualizing")
            Σ(Residual(Local(x)), ρ, σ, k)
          }
      }

    case Σ(Local(x), ρ, σ, k) =>
      Σ(LocalAddr(x), ρ, σ, LoadCont(ρ)::k)

    case Σ(Index(a, i), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForGet(i, ρ)::k)

    case Σ(loc @ Path(addr, path), ρ, σ, LoadCont(ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(LocClosure(Loc(v))) =>
          Σ(Path(v, path), ρ1, σ, k)
        case Some(ValClosure(v)) =>
          Σ(v, ρ1, σ, k)
        case Some(ObjClosure(funObject, ρ2)) =>
          Σ(Residual(path), ρ1, σ, k)
        case Some(UnknownClosure()) =>
          Σ(Residual(path), ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(Undefined(), ρ, σ, LoadCont(ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, k)

    case Σ(Residual(e), ρ, σ, LoadCont(ρ1)::k) =>
      Σ(Residual(e), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Special unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Typeof(e), ρ, σ, k) =>
      // void e just discards the value
      Σ(e, ρ, σ, DoTypeof(ρ)::k)

    case Σ(Num(v), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("number"), ρ1, σ, k)
    case Σ(Bool(v), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("boolean"), ρ1, σ, k)
    case Σ(StringLit(v), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("string"), ρ1, σ, k)
    case Σ(Undefined(), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("undefined"), ρ1, σ, k)
    case Σ(Null(), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(StringLit("object"), ρ1, σ, k)
    case Σ(loc @ Path(addr, path), ρ, σ, DoTypeof(ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(ObjClosure(FunObject(typeof, _, _, _, _), _)) =>
          Σ(StringLit(typeof), ρ1, σ, k)
        case Some(ValClosure(v)) =>
          Σ(v, ρ1, σ, DoTypeof(ρ1)::k)
        case Some(LocClosure(Loc(v))) =>
          // The address of an object
          Σ(Path(v, path), ρ1, σ, DoTypeof(ρ1)::k)
        case Some(UnknownClosure()) =>
          Σ(Residual(Typeof(path)), ρ1, σ, k)
        case None =>
          Σ(Residual(Typeof(path)), ρ1, σ, k)
      }

    case Σ(Residual(e), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(Residual(Typeof(e)), ρ1, σ, k)

    case Σ(Void(Residual(e)), ρ, σ, k) if e.isPure =>
      // void e just discards the value
      Σ(Undefined(), ρ, σ, k)

    case Σ(Void(Residual(e)), ρ, σ, k) =>
      // void e just discards the value
      Σ(Residual(Void(e)), ρ, σ, k)

    case Σ(Void(e), ρ, σ, k) =>
      // void e just discards the value
      Σ(e, ρ, σ, SeqCont(Undefined(), ρ)::k)

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Unary(op, e), ρ, σ, k) =>
      Σ(e, ρ, σ, DoUnaryOp(op, ρ)::k)

    case Σ(CvtBool(v), ρ, σ, DoUnaryOp(Prefix.!, ρ1)::k) =>
      Σ(Bool(!v), ρ1, σ, k)

    case Σ(CvtNum(v), ρ, σ, DoUnaryOp(Prefix.~, ρ1)::k) =>
      Σ(Num(~v.toLong), ρ1, σ, k)

    case Σ(CvtNum(v), ρ, σ, DoUnaryOp(Prefix.+, ρ1)::k) =>
      Σ(Num(+v), ρ1, σ, k)

    case Σ(CvtNum(v), ρ, σ, DoUnaryOp(Prefix.-, ρ1)::k) =>
      Σ(Num(-v), ρ1, σ, k)

    case Σ(Value(v), ρ, σ, DoUnaryOp(op, ρ1)::k) =>
      tryReify(v)(σ, ρ) match {
        case Some(v) =>
          Σ(Residual(Unary(op, v)), ρ1, Eval.simulateStore(Unary(op, v))(σ, ρ1), k)
        case None =>
          Σ(v, ρ, σ, Fail(s"could not reify $v")::k)
      }

    case Σ(Residual(v), ρ, σ, DoUnaryOp(op, ρ1)::k) =>
      Σ(Residual(Unary(op, v)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // Eval the left operand.
    case Σ(Binary(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, EvalBinaryOpRight(op, e2, ρ)::k)

    // Short-circuit && and ||
    case Σ(v @ CvtBool(false), ρ, σ, EvalBinaryOpRight(Binary.&&, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    case Σ(v @ CvtBool(true), ρ, σ, EvalBinaryOpRight(Binary.&&, e2, ρ1)::k) =>
      Σ(e2, ρ1, σ, k)

    case Σ(v @ CvtBool(true), ρ, σ, EvalBinaryOpRight(Binary.||, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    case Σ(v @ CvtBool(false), ρ, σ, EvalBinaryOpRight(Binary.||, e2, ρ1)::k) =>
      Σ(e2, ρ1, σ, k)

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(ValueOrResidual(v), ρ, σ, EvalBinaryOpRight(op, e2, ρ1)::k) =>
      Σ(e2, ρ1, σ, DoBinaryOp(op, v, ρ1)::k)

    // Does the property i exist in loc?
    case Σ(Value(i), ρ, σ, DoBinaryOp(Binary.IN, loc @ Path(addr, path), ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
        case _ =>
          Eval.getPropertyAddress(Loc(addr), i, σ) match {
            case Some(v) =>
              Σ(Bool(true), ρ1, σ, k)
            case None =>
              Σ(Bool(false), ρ1, σ, k)
          }
      }

    // We can't just desugar because otherwise the residual won't be correct.
    // x instanceof y
    // ==
    // x.__proto__ === y.prototype
    case Σ(v2 @ Path(addr2, path2), ρ, σ, DoBinaryOp(Binary.INSTANCEOF, Null(), ρ1)::k) =>
      Σ(Bool(false), ρ1, σ, k)

    case Σ(v2 @ Path(addr2, path2), ρ, σ, DoBinaryOp(Binary.INSTANCEOF, Undefined(), ρ1)::k) =>
      Σ(Bool(false), ρ1, σ, k)

    case Σ(v2 @ Path(addr2, path2), ρ, σ, DoBinaryOp(Binary.INSTANCEOF, v1 @ Path(addr1, path1), ρ1)::k) =>
      val result = for {
        ObjClosure(FunObject(_, v1protoLoc, _, _, _), _) <- σ.get(Loc(addr1))
        v2protoLoc <- Eval.getPropertyAddress(Loc(addr2), StringLit("prototype"), σ)
      } yield (v1protoLoc, v2protoLoc)

      result match {
        case Some((proto1, proto2)) if proto1 == proto2 =>
          Σ(Bool(true), ρ1, σ, k)
        case None =>
          tryReify(Binary(Binary.INSTANCEOF, path1, path2))(σ, ρ) match {
            case Some(v) =>
              Σ(v, ρ1, Eval.simulateStore(v)(σ, ρ1), k)
            case None =>
              Σ(v2, ρ, σ, Fail(s"could not reify $v1 instanceof $v2")::k)
          }
      }

    case Σ(ValueOrResidual(v2), ρ, σ, DoBinaryOp(Binary.INSTANCEOF, v1, ρ1)::k) =>
      tryReify(Binary(Binary.INSTANCEOF, v1, v2))(σ, ρ) match {
        case Some(v) =>
          Σ(v, ρ1, Eval.simulateStore(v)(σ, ρ1), k)
        case None =>
          Σ(v2, ρ, σ, Fail(s"could not reify $v1 instanceof $v2")::k)
      }

    case Σ(ValueOrResidual(v2), ρ, σ, DoBinaryOp(op, v1, ρ1)::k) =>
      val v = Eval.evalOp(op, v1, v2)
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Calls and lambda.
    // FIXME
    // Environment handling is completely broken here.
    // See the old SCSC implementation.
    ////////////////////////////////////////////////////////////////

    // A method call "x.m()" passes "x" as "this"
    case Σ(Call(Index(e, m), args), ρ, σ, k) =>
      Σ(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)

    case Σ(Call(IndexAddr(e, m), args), ρ, σ, k) =>
      Σ(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)

    case Σ(ValueOrResidual(thisValue), ρ, σ, EvalMethodProperty(m, es, ρ1)::k) =>
      Σ(m, ρ1, σ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)

    // A non-method call "f()" passes "window" as "this"
    case Σ(Call(fun, args), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArgs(Prim("window"), args, ρ)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgs(thisValue, Nil, ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, DoCall(fun, thisValue, Nil, Call(fun, Nil), ρ1)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgs(thisValue, arg::args, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, DoCall(fun, thisValue, done :+ v, Call(fun, done :+ v), ρ1)::k)

    case Σ(v, ρ, σ, DoCall(fun @ Path(addr, path), thisValue, args, residual, ρ1)::k) =>
      // HACK
      σ.get(Loc(addr)) match {
        case Some(ObjClosure(FunObject(_, _, xs, Some(e), _), ρ2)) =>
          // Pad the arguments with undefined.
          def pad(params: List[Name], args: List[Exp]): List[Exp] = (params, args) match {
            case (Nil, _) => Nil
            case (_::params, Nil) => Undefined()::pad(params, Nil)
            case (_::params, arg::args) => arg::pad(params, args)
          }
          val args2 = pad(xs, args)
          val seq = (xs zip args2).foldLeft(Assign(None, LocalAddr("this"), thisValue): Exp) {
            case (seq, (x, a)) => Seq(seq, Assign(None, LocalAddr(x), a))
          }
          val ρ2 = ("this"::xs).foldLeft(ρ) {
            case (ρ, x) => ρ + (x -> FreshLoc())
          }
          val k1 = RebuildLet("this"::xs, (thisValue::args2) map { a => Undefined() }, ρ2)::k
          Σ(Seq(seq, e), ρ2, σ, CallFrame(ρ1)::k1)  // use ρ1 in the call frame.. this is the env we pop to.

        case Some(ValClosure(Prim(fun))) =>
          Eval.evalPrim(fun, args) match {
            case Some(e) =>
              Σ(e, ρ1, σ, k)
            case None =>
              Σ(reify(residual)(σ, ρ1), ρ1, σ, k)
          }

        case _ =>
          Σ(reify(residual)(σ, ρ1), ρ1, σ, k)
      }

    // The function is not a lambda. Residualize the call. Clear the store since we have no idea what the function
    // will do to the store.
    case Σ(_, ρ, σ, DoCall(fun, thisValue, args, residual, ρ1)::k) =>
      Σ(reify(residual)(σ, ρ1), ρ1, σ, k)

    // Wrap v in a let.
    case Σ(Value(v), ρ, σ, RebuildLet(xs, args, ρ1)::k) =>
      val ss = (xs zip args) collect {
        case (x, e) if ! v.isInstanceOf[Path] && (fv(v) contains x) => VarDef(x, e)
      }
      if (ss.nonEmpty) {
        tryReify(v)(σ, ρ) match {
          case Some(v) =>
            val block = ss.foldRight(v) {
              case (s1, s2) => Seq(s1, s2)
            }
            Σ(Residual(block), ρ1, Eval.simulateStore(block)(σ, ρ1), k)
          case None =>
            Σ(v, ρ, σ, Fail(s"could not reify $v")::k)
        }
      }
      else {
        Σ(v, ρ1, σ, k)
      }

    case Σ(Residual(v), ρ, σ, RebuildLet(xs, args, ρ1)::k) =>
      val ss = (xs zip args) collect {
        case (x, e) if (fv(v) contains x) => VarDef(x, e)
      }
      if (ss.nonEmpty) {
        val block = ss.foldRight(v) {
          case (s1, s2) => Seq(s1, s2)
        }
        Σ(Residual(block), ρ1, Eval.simulateStore(block)(σ, ρ1), k)
      }
      else {
        Σ(Residual(v), ρ1, Eval.simulateStore(v)(σ, ρ1), k)
      }

    ////////////////////////////////////////////////////////////////
    // Return. Pop the continuations until we hit the caller.
    ////////////////////////////////////////////////////////////////

    case Σ(Return(Some(e)), ρ, σ, k) =>
      Σ(e, ρ, σ, DoReturn()::k)

    case Σ(Return(None), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, DoReturn()::k)

    case Σ(ValueOrResidual(v), ρ, σ, DoReturn()::k) =>
      Σ(Undefined(), ρ, σ, Returning(v)::k)

    // Once we hit the call frame, evaluate the return value.
    // Then pop the call frame using the ValueOrResidual rule.
    case Σ(res, ρ, σ, Returning(v)::CallFrame(ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, Returning(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::SeqCont(e, ρ)::DoReturn()::k)

    case Σ(v, ρ, σ, Returning(e)::_::k) =>
      Σ(v, ρ, σ, Returning(e)::k)

    // If we run off the end of the function body, act like we returned normally.
    // This also runs after evaluating the return value after a return.
    case Σ(ValueOrResidual(v), ρ, σ, CallFrame(ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Throw. This is implemented similarly to Return.
    ////////////////////////////////////////////////////////////////

    case Σ(Throw(e), ρ, σ, k) =>
      Σ(e, ρ, σ, DoThrow()::k)

    case Σ(ValueOrResidual(v), ρ, σ, DoThrow()::k) =>
      Σ(Undefined(), ρ, σ, Throwing(v)::k)

    // If we're throwing and we hit a try block,
    // evaluate the finally block and rethrow.
    case Σ(v, ρ, σ, Throwing(e)::FinallyFrame(fin, ρ1)::k) =>
      Σ(fin, ρ1, σ, Throwing(e)::k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, Throwing(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::Throwing(e)::k)

    case Σ(v, ρ, σ, Throwing(e)::_::k) =>
      Σ(v, ρ, σ, Throwing(e)::k)

    // Run the finally block, if any. Then restore the value.
    // And pass it to k.
    case Σ(ValueOrResidual(v), ρ, σ, FinallyFrame(fin, ρ1)::k) =>
      Σ(fin, ρ1, σ, SeqCont(v, ρ)::k)

    case Σ(TryCatch(e, cs), ρ, σ, k) =>
      Σ(e, ρ, σ, CatchFrame(cs, ρ)::k)

    case Σ(TryFinally(e, fin), ρ, σ, k) =>
      Σ(e, ρ, σ, FinallyFrame(fin, ρ)::k)


    ////////////////////////////////////////////////////////////////
    // Objects and arrays.
    ////////////////////////////////////////////////////////////////

    // new Point(x, y)
    // creates a new empty object
    // binds the object to this
    // sets this.__proto__ to Point.prototype
    // calls the Point function

    case Σ(NewCall(fun, args), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArgsForNew(args, ρ)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgsForNew(Nil, ρ1)::k) =>
      Σ(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, Nil, ρ1)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgsForNew(arg::args, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, Nil, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgsForNew(fun, arg::args, done, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, done :+ v, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgsForNew(fun, Nil, done, ρ1)::k) =>
      Σ(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, done :+ v, ρ1)::k)

    case Σ(proto, ρ, σ, InitProto(fun, args, ρ1)::k) =>
      // Put the object in the heap
      val loc = Path(FreshLoc().address, NewCall(fun, args))

      val protoLoc = proto match {
        case Path(a, p) => Some(Loc(a))
        case Prim(x) => Some(Eval.getPrimAddress(Prim(x)))
        case _ => None
      }

      protoLoc match {
        case Some(protoLoc) =>
          val obj = FunObject("object", protoLoc, Nil, None, Nil)

          // create a fresh variable for the new object
          // and introduce a residual NewCall
          val x = FreshVar()
          val xloc = FreshLoc()
          val ρ2 = ρ1 + (x -> xloc)

          Σ(Undefined(), ρ2, σ.assign(xloc, loc, ρ2).assign(loc, obj, ρ2), DoCall(fun, Local(x), args, Local(x), ρ2)::SeqCont(Local(x), ρ2)::RebuildLet(x::Nil, reify(loc)(σ, ρ)::Nil, ρ)::k)

        case None =>
          Σ(reify(loc)(σ, ρ), ρ, σ, k)
      }

    case Σ(Delete(IndexAddr(a, i)), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForDel(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForDel(i, ρ1)::k) =>
      Σ(i, ρ1, σ, DoDeleteProperty(a, ρ1)::k)

    case Σ(i @ CvtString(istr), ρ, σ, DoDeleteProperty(loc @ Path(addr, p), ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              val removed = props filter {
                case (k, w: Loc) if v == w => false
                case _ => true
              }
              Σ(loc, ρ1, σ.assign(loc, FunObject(typeof, proto, xs, body, removed), ρ2), k)
            case None =>
              // The field isn't there anyway.
              Σ(loc, ρ1, σ, k)
          }
        case Some(_) =>
          Σ(loc, ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, DoDeleteProperty(ValueOrResidual(a), ρ1)::k) =>
      tryReify(Delete(IndexAddr(a, i)))(σ, ρ) match {
        case Some(v) =>
          Σ(v, ρ1, Eval.simulateStore(v)(σ, ρ1), k)
        case None =>
          Σ(i, ρ, σ, Fail(s"could not reify ${Delete(IndexAddr(a, i))}")::k)
      }

    case Σ(IndexAddr(a, i), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForSet(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForSet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, GetPropertyAddressOrCreate(a, ρ1)::k)

    case Σ(i @ CvtString(istr), ρ, σ, GetPropertyAddressOrCreate(loc @ Path(addr, path), ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              Σ(Path(v.address, Index(path, i)), ρ2, σ, k)
            case None =>
              // FIXME: maybe the property key is reified?
              // I don't think this can happen, though.

              // The field is missing.
              // Create it.
              val fieldLoc = Path(FreshLoc().address, Index(path, i))
              val σ1 = σ.assign(loc, FunObject(typeof, proto, xs, body, props :+ (istr, Loc(fieldLoc.address))), ρ2)
              val σ2 = σ1.assign(fieldLoc, Undefined(), ρ2)
              Σ(fieldLoc, ρ1, σ2, k)
          }
        case Some(_) =>
          Σ(Undefined(), ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, GetPropertyAddressOrCreate(a, ρ1)::k) =>
      tryReify(IndexAddr(a, i))(σ, ρ) match {
        case Some(v) =>
          Σ(v, ρ1, Eval.simulateStore(v)(σ, ρ1), k)
        case None =>
          Σ(i, ρ, σ, Fail(s"could not reify ${IndexAddr(a, i)}")::k)
      }

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForGet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, GetProperty(a, ρ1)::k)

    // restrict the property to values to ensure == during property lookup works correctly
    // otherwise, a[f()] will result in undefined rather than a reified access
    case Σ(Value(i), ρ, σ, GetProperty(loc @ Path(addr, path), ρ1)::k) =>
      σ.get(Loc(addr)) match {
        case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
          println(s"looking for $i in $props")
          val propAddr = props collectFirst {
            case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
          }
          println(s"looking for $i in $props: found $propAddr")
          propAddr match {
            case Some(propAddr) =>
              println(s"looking for $i in $props: loading $propAddr")
              Σ(Path(propAddr.address, Index(path, i)), ρ2, σ, LoadCont(ρ1)::k)
            case None =>
              if (body != None && Eval.evalOp(Binary.==, StringLit("length"), i) == Bool(true)) {
                Σ(Num(xs.length), ρ1, σ, k)
              }
              else {
                // Try the prototype.
                // If not found, return undefined.
                Σ(i, ρ1, σ, GetProperty(Path(proto.address, path), ρ1)::k)
              }
          }
        case Some(closure) =>
          Σ(Undefined(), ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, GetProperty(ValueOrResidual(a), ρ1)::k) =>
      tryReify(Index(a, i))(σ, ρ) match {
        case Some(v) =>
          Σ(v, ρ1, Eval.simulateStore(v)(σ, ρ1), k)
        case None =>
          Σ(i, ρ, σ, Fail(s"could not reify ${Index(a, i)}")::k)
      }

    // Create an empty object
    // Initialize a non-empty object.
    case Σ(ObjectLit(Nil), ρ, σ, k) =>
      val loc = Path(FreshLoc().address, ObjectLit(Nil))
      val v = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
      Σ(loc, ρ, σ.assign(loc, v, ρ), k)

    case Σ(ObjectLit(p::ps), ρ, σ, k) =>
      val x = FreshVar()
      val seq = ps.foldLeft(Assign(None, LocalAddr(x), ObjectLit(Nil)): Exp) {
        case (seq, Property(prop, value, _, _)) =>
          Seq(seq, Assign(None, IndexAddr(Local(x), prop), value))
        case _ => ???
      }
      Σ(Seq(seq, Local(x)), ρ + (x -> FreshLoc()), σ, k)

    // Put a lambda in the heap.
    case Σ(lam @ Lambda(xs, e), ρ, σ, k) =>
      // x = v
      // x.proto = v2
      val x = FreshVar()
      val loc = Path(FreshLoc().address, Local(x))
      val v = FunObject("function", Eval.getPrimAddress(Prim("Function.prototype")), xs, Some(e), Nil)
      val xloc = Path(FreshLoc().address, Local(x))
      val protoLoc = Path(FreshLoc().address, Index(Local(x), StringLit("prototype")))
      val v2 = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
      val ρ2 = ρ + (x -> Loc(xloc.address))
      Σ(loc, ρ2, σ.assign(xloc, loc, ρ2).assign(loc, v, ρ2).assign(protoLoc, v2, ρ2), RebuildLet(x::Nil, Undefined()::Nil, ρ2)::k)

    // Array literals desugar to objects
    case Σ(ArrayLit(es), ρ, σ, k) =>
      val loc = Path(FreshLoc().address, NewCall(Prim("Array"), Num(es.length)::Nil))
      val v = FunObject("object", Eval.getPrimAddress(Prim("Array.prototype")), Nil, None, Nil)
      val x = FreshVar()
      val seq = es.zipWithIndex.foldLeft(Assign(None, LocalAddr(x), loc): Exp) {
        case (seq, (value, i)) =>
          Seq(seq, Assign(None, IndexAddr(Local(x), StringLit(i.toInt.toString)), value))
      }
      Σ(Seq(seq, Seq(Assign(None, IndexAddr(Local(x), StringLit("length")), Num(es.length)), Local(x))), ρ, σ.assign(loc, v, ρ), k)

    ////////////////////////////////////////////////////////////////
    // Other cases.
    ////////////////////////////////////////////////////////////////

    // Don't implement with.
    case Σ(With(exp, body), ρ, σ, k) =>
      tryReify(With(exp, body))(σ, ρ) match {
        case Some(v) =>
          Σ(v, ρ, Eval.simulateStore(v)(σ, ρ), k)
        case None =>
          Σ(With(exp, body), ρ, σ, Fail(s"could not reify ${With(exp, body)}")::k)
      }

    ////////////////////////////////////////////////////////////////
    // Catch all.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s")::k)
  }
}
