package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._


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
    case s @ Σ(NormalForm(_), _, _, Nil) => s

    // Fail fast
    case s @ Σ(_, _, _, Fail(_)::k) => s

    ////////////////////////////////////////////////////////////////
    // Programs.
    ////////////////////////////////////////////////////////////////

    case Σ(Program(s), ρ, σ, k) =>
      Σ(s, ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Conditionals
    // ? : and if/else are handled identically, duplicating code
    ////////////////////////////////////////////////////////////////

    // if e then s1 else s2
    case Σ(IfElse(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, BranchCont(BlockCont(s1::Nil, Nil, ρ)::Nil,
                            BlockCont(s2::Nil, Nil, ρ)::Nil,
                            RebuildIfElseTest(s1, s2, ρ)::Nil)::k)

    // e ? s1 : s2
    case Σ(Cond(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, BranchCont(BlockCont(s1::Nil, Nil, ρ)::Nil,
                            BlockCont(s2::Nil, Nil, ρ)::Nil,
                            RebuildCondTest(s1, s2, ρ)::Nil)::k)

    case Σ(v @ CvtBool(true), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, kt ++ k)

    case Σ(v @ CvtBool(false), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(v, ρ, σ, kf ++ k)

    // Neither true nor false, so residualize
    case Σ(ValueOrResidual(e), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(Residual(e), ρ, σ, kr ++ k)


    // Rebuilding ? : and if-else nodes.
    // The logic is duplicated.

    // Evaluate the test to a (residual) value.
    // Save the store and eval the true branch.
    case Σ(ValueOrResidual(test), ρ, σ, RebuildCondTest(s1, s2, ρ1)::k) =>
      Σ(s1, ρ1, σ, RebuildCondTrue(test, s2, σ, ρ)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(ValueOrResidual(s1), ρ, σ, RebuildCondTrue(test, s2, σ1, ρ1)::k) =>
      Σ(s2, ρ1, σ1, RebuildCondFalse(test, s1, σ, ρ)::k)

    // Rebuild and merge the post-true and post-false stores.
    case Σ(ValueOrResidual(s2), ρ, σ, RebuildCondFalse(test, s1, σ1, ρ1)::k) =>
      Σ(reify(Cond(test, s1, s2))(σ, ρ), ρ1, mergeStores(σ1, σ), k)

    case Σ(ValueOrResidual(test), ρ, σ, RebuildIfElseTest(s1, s2, ρ1)::k) =>
      Σ(s1, ρ1, σ, RebuildIfElseTrue(test, s2, σ, ρ)::k)

    case Σ(ValueOrResidual(s1), ρ, σ, RebuildIfElseTrue(test, s2, σ1, ρ1)::k) =>
      Σ(s2, ρ1, σ1, RebuildIfElseFalse(test, s1, σ, ρ)::k)

    case Σ(ValueOrResidual(s2), ρ, σ, RebuildIfElseFalse(test, s1, σ1, ρ1)::k) =>
      Σ(reify(IfElse(test, s1, s2))(σ, ρ), ρ1, mergeStores(σ1, σ), k)

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
                      BlockCont(body::Nil, Nil, ρ)::ContinueFrame(label)::BlockCont(iter::For(label, Empty(), test, iter, body)::Nil, Nil, ρ)::BreakFrame(label)::Nil,
                      BlockCont(Undefined()::Nil, Nil, ρ)::Nil,
                      RebuildForTest(label, test, iter, body, ρ)::Nil)::k)

    case Σ(For(label, init, test, iter, body), ρ, σ, k) =>
      Σ(Block(init::For(label, Empty(), test, iter, body)::Nil), ρ, σ, k)

    // do body while test
    case Σ(DoWhile(label, body, test), ρ, σ, k) =>
      Σ(body, ρ, σ, ContinueFrame(label)::BlockCont(While(label, test, body)::Nil, Nil, ρ)::BreakFrame(label)::k)

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
      Σ(reify(IfElse(test1, Block(body1::iter1::While(label, test0, body0)::Nil), Undefined()))(σ, ρ),
        ρ1, σ0, k)

    case Σ(ValueOrResidual(iter1), ρ, σ, RebuildForIter(label, body1, test1, test0, iter0, body0, ρ1)::k) =>
      Σ(reify(IfElse(test1, Block(body1::iter1::For(label, Empty(), test0, iter0, body0)::Nil), Undefined()))(σ, ρ),
        ρ1, σ0, k)

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
    case Σ(NormalForm(v), ρ, σ, BreakFrame(_)::k) =>
      Σ(v, ρ, σ, k)
    case Σ(NormalForm(v), ρ, σ, ContinueFrame(_)::k) =>
      Σ(v, ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Blocks.
    // As usual, residual handling is difficult.
    ////////////////////////////////////////////////////////////////

    case Σ(Empty(), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, k)

    case Σ(Block(Nil), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, k)

    case Σ(Block(s::ss), ρ, σ, k) =>
      // Go through all the bindings in the block and add them to the environment
      // as `undefined`. As we go thorugh the block, we'll initialize the variables.
      val bindings = (s::ss) collect {
        case VarDef(x, e) =>
          (x, e)
        case LetDef(x, e) =>
          (x, e)
        case ConstDef(x, e) =>
          (x, e)
      }
      val locs = bindings map { _ => FreshLoc() }
      val ρ1 = (bindings zip locs).foldLeft(ρ) {
        case (ρ, ((x, e), loc)) => ρ + (x -> loc)
      }
      val σ1 = (bindings zip locs).foldLeft(σ) {
        case (σ, ((x, e), loc)) => σ.assign(loc, Undefined(), ρ1)
      }
      Σ(s, ρ1, σ1, BlockCont(ss, Nil, ρ1)::k)

    // If we don't have to save any residual for the block, just eval to the value.
    case Σ(NormalForm(v), ρ, σ, BlockCont(Nil, Nil, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    // If we have to save the block, append the value to the residual.
    case Σ(NormalForm(v), ρ, σ, BlockCont(Nil, done, ρ1)::k) =>
      Σ(reify(Block(done :+ v))(σ, ρ), ρ1, σ, k)

    // Append non-value residuals to block residual.
    case Σ(Residual(e), ρ, σ, BlockCont(s::ss, done, ρ1)::k) if ! e.isPure =>
      Σ(s, ρ1, σ, BlockCont(ss, done :+ e, ρ1)::k)

    // Ignore non-residual values if there's more to do in the block.
    case Σ(NormalForm(v), ρ, σ, BlockCont(s::ss, done, ρ1)::k) =>
      Σ(s, ρ1, σ, BlockCont(ss, done, ρ1)::k)

    ////////////////////////////////////////////////////////////////
    // Definitions.
    ////////////////////////////////////////////////////////////////

    // Definitions eval to undefined.
    // Look up the location, which should have been added to the environment
    // when we entered the block.
    // Then run the initializer, assigning to the location.
    // The DoAssign continuation should leave the initializer in the focus,
    // but we should evaluate to undefined, so add block continuation for that.
    case Σ(VarDef(x, Lambda(xs, e)), ρ, σ, k) =>
      // Special case lambdas because we need to set the name of the heap object.
      // var Point = function (x, y) { this.x = x; this.y = y}
      // ==
      // var Point = { __code__: fun..., prototype: { __proto__: Function.prototype } }
      ρ.get(x) match {
        case Some(loc) =>
          val __proto__ = FreshLoc()
          val name = FreshLoc()
          val prototype = FreshLoc()
          val lambdaLoc = FreshLoc()
          val p = FunObject("object", Nil, None, Property(StringLit("__proto__"), __proto__, None, None)::Nil)
          val o = FunObject("function", xs, Some(e), Property(StringLit("name"), name, None, None)::Property(StringLit("prototype"), prototype, None, None)::Nil)
          val σ1 = σ.assign(name, StringLit(x), ρ)
                    .assign(__proto__, Prim("Function.prototype"), ρ)
                    .assign(prototype, p, ρ)
                    .assign(lambdaLoc, o, ρ)
                    .assign(loc, lambdaLoc, ρ)
          Σ(lambdaLoc, ρ, σ1,
            DoAssign(None, loc, ρ)::
            RebuildVarDef(x, ρ)::
            BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }

    case Σ(VarDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, DoAssign(None, loc, ρ)::RebuildVarDef(x, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }
    case Σ(LetDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, DoAssign(None, loc, ρ)::RebuildLetDef(x, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }
    case Σ(ConstDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, DoAssign(None, loc, ρ)::RebuildConstDef(x, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }

    case Σ(ValueOrResidual(v), ρ, σ, RebuildVarDef(x, ρ1)::k) =>
      Σ(reify(VarDef(x, v))(σ, ρ), ρ1, σ, k)
    case Σ(ValueOrResidual(v), ρ, σ, RebuildLetDef(x, ρ1)::k) =>
      Σ(reify(LetDef(x, v))(σ, ρ), ρ1, σ, k)
    case Σ(ValueOrResidual(v), ρ, σ, RebuildConstDef(x, ρ1)::k) =>
      Σ(reify(ConstDef(x, v))(σ, ρ), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Assignment.
    ////////////////////////////////////////////////////////////////

    // we can assign to undefined. yep, that's right.
    case Σ(Assign(op, Undefined(), rhs), ρ, σ, k) =>
      Σ(rhs, ρ, σ, DoAssign(op, FreshLoc(), ρ)::k)

    case Σ(Assign(op, lhs, rhs), ρ, σ, k) =>
      Σ(lhs, ρ, σ, EvalAssignRhs(op, rhs, ρ)::k)

    case Σ(lhs: Loc, ρ, σ, EvalAssignRhs(op, rhs, ρ1)::k) =>
      Σ(rhs, ρ1, σ, DoAssign(op, lhs, ρ)::k)

    case Σ(NormalForm(lhs), ρ, σ, EvalAssignRhs(op, rhs, ρ1)::k) =>
      Σ(rhs, ρ1, σ, RebuildAssign(op, lhs, ρ)::k)

    case Σ(ValueOrResidual(rhs), ρ, σ, RebuildAssign(op, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      Σ(reify(Assign(op, lhs, rhs))(σ, ρ), ρ1, σ, k)

    case Σ(ValueOrResidual(rhs), ρ, σ, DoAssign(None, lhs, ρ1)::k) =>
      // Normal assignment... the result is the rhs value
      Σ(rhs, ρ1, σ.assign(lhs, rhs, ρ), k)

    case Σ(ValueOrResidual(rhs), ρ, σ, DoAssign(Some(op), lhs, ρ1)::k) =>
      val right = rhs
      σ.get(lhs) match {
        case Some(Closure(left, _)) =>
          val v = Eval.evalOp(op, left, right)
          Σ(v, ρ1, σ.assign(lhs, v, ρ), k)
        case None =>
          // can store lookups fail?
          Σ(rhs, ρ1, σ, Fail(s"could not find value at location $lhs")::k)
      }

    case Σ(IncDec(op, lhs), ρ, σ, k) =>
      Σ(lhs, ρ, σ, DoIncDec(op, ρ)::k)

    case Σ(loc: Loc, ρ, σ, DoIncDec(op, ρ1)::k) =>
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
          Σ(v, ρ2, σ.assign(loc, newValue, ρ), k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(e), ρ, σ, DoIncDec(op, ρ1)::k) =>
      Σ(reify(IncDec(op, e))(σ, ρ), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(LocalAddr(x), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(v) =>
          Σ(v, ρ, σ, k)
        case None =>
          // The special global name "undefined" evaluates to "undefined".
          if (x == "undefined") {
            val loc = FreshLoc()
            Σ(loc, ρ, σ.assign(loc, Undefined(), ρ), k)
          }
          else {
            println(s"variable $x not found... residualizing")
            Σ(reify(Local(x))(σ, ρ), ρ, σ, k)
          }
      }

    case Σ(Local(x), ρ, σ, k) =>
      Σ(LocalAddr(x), ρ, σ, LoadCont(ρ)::k)

    case Σ(Index(a, i), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForGet(i, ρ)::k)

    case Σ(loc: Loc, ρ, σ, LoadCont(ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(v, ρ2)) =>
          Σ(v, ρ2, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(Undefined(), ρ, σ, LoadCont(ρ1)::k) =>
      Σ(Undefined(), ρ1, σ, k)

    case Σ(ValueOrResidual(e), ρ, σ, LoadCont(ρ1)::k) =>
      Σ(reify(e)(σ, ρ), ρ1, σ, k)

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
    case Σ(loc: Loc, ρ, σ, DoTypeof(ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, _, _, _), _)) =>
          Σ(StringLit(typeof), ρ1, σ, k)
        case Some(Closure(v, ρ2)) =>
          Σ(v, ρ2, σ, DoTypeof(ρ1)::k)
        case None =>
          Σ(StringLit("undefined"), ρ1, σ, k)
      }
    case Σ(Residual(e), ρ, σ, DoTypeof(ρ1)::k) =>
      Σ(reify(Typeof(e))(σ, ρ), ρ1, σ, k)

    case Σ(Void(Residual(e)), ρ, σ, k) if e.isPure =>
      // void e just discards the value
      Σ(Undefined(), ρ, σ, k)

    case Σ(Void(Residual(e)), ρ, σ, k) =>
      // void e just discards the value
      Σ(reify(Void(e))(σ, ρ), ρ, σ, k)

    case Σ(Void(e), ρ, σ, k) =>
      // void e just discards the value
      Σ(e, ρ, σ, BlockCont(Undefined()::Nil, Nil, ρ)::k)

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

    case Σ(ValueOrResidual(v), ρ, σ, DoUnaryOp(op, ρ1)::k) =>
      Σ(reify(Unary(op, v))(σ, ρ), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // Eval the left operand.
    case Σ(Binary(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, EvalBinaryOpRight(op, e2, ρ)::k)

    // Short-circuit && and ||
    case Σ(v @ CvtBool(false), ρ, σ, EvalBinaryOpRight(Binary.&&, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    case Σ(v @ CvtBool(true), ρ, σ, EvalBinaryOpRight(Binary.||, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(ValueOrResidual(v), ρ, σ, EvalBinaryOpRight(op, e2, ρ1)::k) =>
      Σ(e2, ρ1, σ, DoBinaryOp(op, v, ρ1)::k)

    // Does the property i exist in loc?
    case Σ(Value(i), ρ, σ, DoBinaryOp(Binary.IN, loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
        case _ =>
          Eval.getPropertyAddress(loc, i, σ) match {
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
    case Σ(v2: Loc, ρ, σ, DoBinaryOp(Binary.INSTANCEOF, v1: Loc, ρ1)::k) =>
      val result = for {
        v1protoLoc <- Eval.getPropertyAddress(v1, StringLit("__proto__"), σ)
        Closure(v1proto, _) <- σ.get(v1protoLoc)
        v2protoLoc <- Eval.getPropertyAddress(v2, StringLit("prototype"), σ)
        Closure(v2proto, _) <- σ.get(v2protoLoc)
      } yield (v1proto, v2proto)

      result match {
        case Some((proto1, proto2)) =>
          Σ(Binary(Binary.===, proto1, proto2), ρ1, σ, k)
        case None =>
          Σ(reify(Binary(Binary.INSTANCEOF, v1, v2))(σ, ρ), ρ1, σ, k)
      }

    case Σ(ValueOrResidual(v2), ρ, σ, DoBinaryOp(Binary.INSTANCEOF, v1, ρ1)::k) =>
      Σ(reify(Binary(Binary.INSTANCEOF, v1, v2))(σ, ρ), ρ1, σ, k)

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
    case Σ(Call(IndexAddr(e, m), args), ρ, σ, k) =>
      Σ(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)

    case Σ(NormalForm(thisValue), ρ, σ, EvalMethodProperty(m, es, ρ1)::k) =>
      Σ(m, ρ1, σ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)

    // A non-method call "f()" passes "window" as "this"
    case Σ(Call(fun, args), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArgs(Prim("window"), args, ρ)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgs(thisValue, Nil, ρ1)::k) =>
      Σ(Empty(), ρ1, σ, DoCall(fun, thisValue, Nil, ρ1)::k)

    case Σ(ValueOrResidual(fun), ρ, σ, EvalArgs(thisValue, arg::args, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k) =>
      Σ(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)

    case Σ(ValueOrResidual(v), ρ, σ, EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k) =>
      Σ(Empty(), ρ1, σ, DoCall(fun, thisValue, done :+ v, ρ1)::k)

    case Σ(_, ρ, σ, DoCall(Prim("eval"), _, args @ (StringLit(code)::Nil), ρ1)::k) =>
      val e = scsc.js.Parser.fromString(code)
      e match {
        case Some(Program(e)) =>
          Σ(e, ρ1, σ, k)
        case None =>
          Σ(reify(Call(Prim("eval"), args))(σ, ρ), ρ1, σ0, k)
      }

    case Σ(_, ρ, σ, DoCall(FunObject(_, xs, Some(e), _), thisValue, args, ρ1)::k) =>
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
      Σ(e, ρ2, σ1, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.

    // The function is not a lambda. Residualize the call. Clear the store since we have no idea what the function
    // will do to the store.
    case Σ(_, ρ, σ, DoCall(fun, thisValue, args, ρ1)::k) =>
      Σ(reify(Call(fun, args))(σ, ρ), ρ1, σ0, k)

    // Wrap v in a let.
    case Σ(NormalForm(v), ρ, σ, RebuildLet(xs, args, ρ1)::k) =>
      val ss = (xs zip args) collect {
        case (x, e) if (fv(v) contains x) => LetDef(x, e)
      }
      if (ss.nonEmpty) {
        Σ(reify(Block(ss :+ v))(σ, ρ), ρ1, σ, k)
      }
      else {
        Σ(v, ρ1, σ, k)
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
    // Then pop the call frame using the NormalForm rule.
    case Σ(res, ρ, σ, Returning(v)::CallFrame(ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, Returning(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::Returning(e)::k)

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
    case Σ(v, ρ, σ, Throwing(e)::FinallyFrame(f, ρ1)::k) =>
      Σ(f, ρ1, σ, Throwing(e)::k)

    // If we hit a rebuild continuation, we must run it, passing in v
    // (which is either undefined or a residual) to the rebuild continuation
    case Σ(v, ρ, σ, Throwing(e)::(a: RebuildCont)::k) =>
      Σ(v, ρ, σ, a::Throwing(e)::k)

    case Σ(v, ρ, σ, Throwing(e)::_::k) =>
      Σ(v, ρ, σ, Throwing(e)::k)

    // Run the finally block, if any. Then restore the value.
    // And pass it to k.
    case Σ(ValueOrResidual(v), ρ, σ, FinallyFrame(f, ρ1)::k) =>
      Σ(f, ρ1, σ, BlockCont(v::Nil, Nil, ρ)::k)

    case Σ(TryCatch(e, cs), ρ, σ, k) =>
      Σ(e, ρ, σ, CatchFrame(cs, ρ)::k)

    case Σ(TryFinally(e, f), ρ, σ, k) =>
      Σ(e, ρ, σ, FinallyFrame(f, ρ)::k)


    ////////////////////////////////////////////////////////////////
    // Objects and arrays.
    ////////////////////////////////////////////////////////////////

    // new Point(x, y)
    // creates a new empty object
    // binds the object to this
    // sets this.__proto__ to Point.prototype
    // calls the Point function

    case Σ(NewCall(f, args), ρ, σ, k) =>
      val loc = FreshLoc()
      Σ(f, ρ, σ, InitProto(loc, ρ)::LoadCont(ρ)::EvalArgs(loc, args, ρ)::BlockCont(loc::Nil, Nil, ρ)::k)

    case Σ(f, ρ, σ, InitProto(loc, ρ1)::k) =>
      val v1 =
        FunObject("object", Nil, None,
          Property(StringLit("__proto__"), reify(Index(f, StringLit("prototype")))(σ, ρ), None, None)::Nil)
      Σ(f, ρ, σ.assign(loc, v1, ρ1), k)

    case Σ(Delete(IndexAddr(a, i)), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForDel(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForDel(i, ρ1)::k) =>
      Σ(i, ρ1, σ, DoDeleteProperty(a, ρ1)::k)

    case Σ(Value(i), ρ, σ, DoDeleteProperty(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              val removed = props filter {
                case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => false
                case _ => true
              }
              Σ(loc, ρ1, σ.assign(loc, FunObject(typeof, xs, body, removed), ρ2), k)
            case None =>
              // The field isn't there anyway.
              Σ(loc, ρ1, σ, k)
          }
        case Some(Closure(v, ρ2)) =>
          Σ(loc, ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, DoDeleteProperty(ValueOrResidual(a), ρ1)::k) =>
      Σ(reify(Delete(IndexAddr(a, i)))(σ, ρ), ρ1, σ, k)

    case Σ(IndexAddr(a, i), ρ, σ, k) =>
      Σ(a, ρ, σ, EvalPropertyNameForSet(i, ρ)::k)

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForSet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, GetPropertyAddressOrCreate(a, ρ1)::k)

    case Σ(Value(i), ρ, σ, GetPropertyAddressOrCreate(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              Σ(v, ρ2, σ, k)
            case None =>
              // FIXME: maybe the property key is reified?
              // I don't think this can happen, though.

              // The field is missing.
              // Create it.
              val fieldLoc = FreshLoc()
              val σ1 = σ.assign(loc, FunObject(typeof, xs, body, props :+ Property(i, fieldLoc, None, None)), ρ2)
              val σ2 = σ1.assign(fieldLoc, Undefined(), ρ2)
              Σ(fieldLoc, ρ1, σ2, k)
          }
        case Some(Closure(v, ρ2)) =>
          Σ(Undefined(), ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(a), ρ, σ, EvalPropertyNameForGet(i, ρ1)::k) =>
      Σ(i, ρ1, σ, GetProperty(a, ρ1)::k)

    // restrict the property to values to ensure == during property lookup works correctly
    // otherwise, a[f()] will result in undefined rather than a reified access
    case Σ(Value(i), ρ, σ, GetProperty(loc: Loc, ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(FunObject(typeof, xs, body, props), ρ2)) =>
          val v = props collectFirst {
            case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, i) == Bool(true) => v
          }
          v match {
            case Some(v) =>
              Σ(v, ρ2, σ, LoadCont(ρ1)::k)
            case None =>
              // Lookup the __proto__ field.
              // If found, load the property from the prototype.
              // Otherwise, return undefined.
              val proto = props collectFirst {
                case Property(k, v: Loc, g, s) if Eval.evalOp(Binary.==, k, StringLit("__proto__")) == Bool(true) => v
              }
              proto match {
                case Some(protoLoc) =>
                  Σ(i, ρ1, σ, GetProperty(protoLoc, ρ1)::k)
                case None =>
                  Σ(Undefined(), ρ1, σ, k)
              }
          }
        case Some(Closure(v, ρ2)) =>
          Σ(Undefined(), ρ1, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(ValueOrResidual(i), ρ, σ, GetProperty(ValueOrResidual(a), ρ1)::k) =>
      Σ(reify(Index(a, i))(σ, ρ), ρ1, σ, k)

    // Create an empty object
    // Initialize a non-empty object.
    case Σ(ObjectLit(ps), ρ, σ, k) =>
      val loc = FreshLoc()
      val v = FunObject("object", Nil, None, Nil)
      Σ(Property(StringLit("__proto__"), Prim("Object.prototype"), None, None), ρ, σ.assign(loc, v, ρ), InitObject(loc, ps, Nil, ρ)::k)

    // Put a lambda in the heap.
    case Σ(Lambda(xs, e), ρ, σ, k) =>
      val loc = FreshLoc()
      val v = FunObject("function", xs, Some(e), Nil)
      Σ(Property(StringLit("__proto__"), Prim("Function.prototype"), None, None), ρ, σ.assign(loc, v, ρ), InitObject(loc, Nil, Nil, ρ)::k)

    // Array literals desugar to objects
    case Σ(ArrayLit(es), ρ, σ, k) =>
      val loc = FreshLoc()
      val v = FunObject("object", Nil, None, Nil)
      val ps = es.zipWithIndex.map {
        case (e, i) => Property(StringLit(i.toString), e, None, None)
      }
      val ps2 = Property(StringLit("length"), Num(es.length), None, None)::ps
      Σ(Property(StringLit("__proto__"), Prim("Array.prototype"), None, None), ρ, σ.assign(loc, v, ρ), InitObject(loc, ps2, Nil, ρ)::k)

    ////////////////////////////////////////////////////////////////
    // Properties
    ////////////////////////////////////////////////////////////////

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
        case Some(Closure(FunObject(typeof, params, body, props0), ρ2)) =>
          σ.assign(loc, FunObject(typeof, params, body, props0 ++ props), ρ2)
        case Some(_) =>
          ???
        case None =>
          σ.assign(loc, FunObject("object", Nil, None, props), ρ1)
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

    // evaluate a property
    case Σ(Property(ValueOrResidual(x), e, _, _), ρ, σ, k) if ! e.isValue =>
      Σ(e, ρ, σ, WrapProperty(x, ρ)::k)

    case Σ(Property(ek, ev, _, _), ρ, σ, k) =>
      Σ(ek, ρ, σ, EvalPropertyValue(ev, ρ)::k)

    case Σ(ValueOrResidual(vv), ρ, σ, WrapProperty(vk, ρ1)::k) =>
      Σ(Property(vk, vv, None, None), ρ1, σ, k)

    case Σ(ValueOrResidual(vk), ρ, σ, EvalPropertyValue(ev, ρ1)::k) =>
      Σ(ev, ρ1, σ, WrapProperty(vk, ρ1)::k)

    ////////////////////////////////////////////////////////////////
    // Other cases.
    ////////////////////////////////////////////////////////////////

    // Don't implement with.
    case Σ(With(exp, body), ρ, σ, k) =>
      Σ(reify(With(exp, body))(σ, ρ), ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Catch all.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s")::k)
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

  def evalProgram(e: Program, maxSteps: Int): Program = {
    eval(e, maxSteps) match {
      case p: Program => p
      case e: Block => Program(e)
      case e => Program(Block(e::Nil))
    }
    // import scsc.js.TreeWalk._
    // object PE extends Rewriter {
    //   override def rewrite(e: Exp) = e match {
    //     case VarDef(x, Lambda(xs, e)) =>
    //       val e1 = eval(e, maxSteps)
    //       VarDef(x, Lambda(xs, e1))
    //     case VarDef(x, e) =>
    //       val e1 = eval(e, maxSteps)
    //       VarDef(x, e1)
    //     case e =>
    //       super.rewrite(e)
    //   }
    // }
    //
    // val e1 = PE.rewrite(e)
    //
    // e1 match {
    //   case p: Program => p
    //   case _ => ???
    // }
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
        case Σ(NormalForm(v), _, σ, Nil) =>
          return v

        case Σ(e, _, σ, Fail(s)::k) =>
          println(s"FAIL $s")
          return Lambda("error"::Nil, e)

        case s0 @ Σ(e, ρ, σ, k) =>
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
        case Σ(NormalForm(v), _, σ, Nil) =>
          return v

        case Σ(e, _, σ, Fail(s)::k) =>
          println(s"FAIL $s")
          return Lambda("error"::Nil, e)

        case s0 @ Σ(focus, ρ, σ, k) =>
          val s1 = step(s0)

          s1 match {
            case Σ(CheckHistory(focus1), ρ1, σ, k1) =>
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
