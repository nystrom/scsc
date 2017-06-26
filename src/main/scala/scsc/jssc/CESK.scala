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


  def step(s: St): St = s match {
    ////////////////////////////////////////////////////////////////
    // Programs and Eval.
    ////////////////////////////////////////////////////////////////

    case Σ(Program(s), ρ, σ, k) =>
      Σ(s, ρ, σ, Load(ρ)::k)

    ////////////////////////////////////////////////////////////////
    // Conditionals
    // ? : and if/else are handled identically, duplicating code
    ////////////////////////////////////////////////////////////////

    // if e then s1 else s2
    case Σ(IfElse(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, Load(ρ)::
                 BranchCont(BlockCont(s1::Nil, Nil, ρ)::Nil,
                            BlockCont(s2::Nil, Nil, ρ)::Nil,
                            RebuildIfElseTest(s1, s2, ρ)::Nil)::k)

    // e ? s1 : s2
    case Σ(Cond(e, s1, s2), ρ, σ, k) =>
      Σ(e, ρ, σ, Load(ρ)::
                 BranchCont(BlockCont(s1::Nil, Nil, ρ)::Nil,
                            BlockCont(s2::Nil, Nil, ρ)::Nil,
                            RebuildCondTest(s1, s2, ρ)::Nil)::k)

    case Σ(v, ρ, σ, BranchCont(kt, kf, kr)::k) if v.isTrue =>
      Σ(v, ρ, σ, kt ++ k)

    case Σ(v, ρ, σ, BranchCont(kt, kf, kr)::k) if v.isFalse =>
      Σ(v, ρ, σ, kf ++ k)

    case Σ(Residual(e), ρ, σ, BranchCont(kt, kf, kr)::k) =>
      Σ(Residual(e), ρ, σ, kr ++ k)

    // Rebuilding ? : and if-else nodes.
    // The logic is duplicated.

    // Evaluate the test to a (residual) value.
    // Save the store and eval the true branch.
    case Σ(test, ρ, σ, RebuildCondTest(s1, s2, ρ1)::k) if test.isValue =>
      Σ(s1, ρ1, σ, Load(ρ1)::RebuildCondTrue(test, s2, σ, ρ)::k)

    // Save the evaluated true branch and the store after the true branch.
    // Restore the post-test store and evaluate the false branch.
    case Σ(s1, ρ, σ, RebuildCondTrue(test, s2, σ1, ρ1)::k) if s1.isValue =>
      Σ(s2, ρ1, σ1, Load(ρ1)::RebuildCondFalse(test, s1, σ, ρ)::k)

    // Rebuild and merge the post-true and post-false stores.
    case Σ(s2, ρ, σ, RebuildCondFalse(test, s1, σ1, ρ1)::k) if s2.isValue =>
      Σ(reify(Cond(test, s1, s2)), ρ1, mergeStores(σ1, σ), k)

    case Σ(test, ρ, σ, RebuildIfElseTest(s1, s2, ρ1)::k) if test.isValue =>
      Σ(s1, ρ1, σ, Load(ρ1)::RebuildIfElseTrue(test, s2, σ, ρ)::k)

    case Σ(s1, ρ, σ, RebuildIfElseTrue(test, s2, σ1, ρ1)::k) if s1.isValue =>
      Σ(s2, ρ1, σ1, Load(ρ1)::RebuildIfElseFalse(test, s1, σ, ρ)::k)

    case Σ(s2, ρ, σ, RebuildIfElseFalse(test, s1, σ1, ρ1)::k) if s2.isValue =>
      Σ(reify(IfElse(test, s1, s2)), ρ1, mergeStores(σ1, σ), k)

    // the problem, in general, is that the loop condition evaluates to something in the current store.
    // but the next time around the loop, the store is different.
    // the best we can do is peel the loop once

    ////////////////////////////////////////////////////////////////
    // Loops.
    // This is very much complicated by break and continue.
    // Otherwise we could just desugar everything into IfElse and While.
    ////////////////////////////////////////////////////////////////

    // do body while test
    case Σ(Label(x, DoWhile(body, test)), ρ, σ, k) =>
      val loop = LoopCont(Some(x), BlockCont(While(test, body)::Nil, Nil, ρ)::Nil)
      Σ(body, ρ, σ, Load(ρ)::loop::k)

    case Σ(DoWhile(body, test), ρ, σ, k) =>
      val loop = LoopCont(None, BlockCont(While(test, body)::Nil, Nil, ρ)::Nil)
      Σ(body, ρ, σ, Load(ρ)::loop::k)

    // while test body
    case Σ(Label(x, While(test, body)), ρ, σ, k) =>
      val loop = LoopCont(Some(x), BlockCont(While(test, body)::Nil, Nil, ρ)::Nil)
      Σ(test, ρ, σ, Load(ρ)::BranchCont(BlockCont(body::Nil, Nil, ρ)::loop::Nil,
                               BlockCont(Undefined()::Nil, Nil, ρ)::Nil,
                               RebuildWhileTest(test, body, ρ)::Nil)::k)

    case Σ(While(test, body), ρ, σ, k) =>
      val loop = LoopCont(None, BlockCont(While(test, body)::Nil, Nil, ρ)::Nil)
      Σ(test, ρ, σ, Load(ρ)::BranchCont(BlockCont(body::Nil, Nil, ρ)::loop::Nil,
                               BlockCont(Undefined()::Nil, Nil, ρ)::Nil,
                               RebuildWhileTest(test, body, ρ)::Nil)::k)

    // for (; test; init) body
    case Σ(Label(x, For(Empty(), test, iter, body)), ρ, σ, k) =>
      val loop = LoopCont(Some(x), BlockCont(iter::For(Empty(), test, iter, body)::Nil, Nil, ρ)::Nil)
      Σ(test, ρ, σ, Load(ρ)::BranchCont(BlockCont(body::Nil, Nil, ρ)::loop::Nil,
                               BlockCont(Undefined()::Nil, Nil, ρ)::Nil,
                               RebuildForTest(test, iter, body, ρ)::Nil)::k)

    case Σ(For(Empty(), test, iter, body), ρ, σ, k) =>
      val loop = LoopCont(None, BlockCont(iter::For(Empty(), test, iter, body)::Nil, Nil, ρ)::Nil)
      Σ(test, ρ, σ, Load(ρ)::BranchCont(BlockCont(body::Nil, Nil, ρ)::loop::Nil,
                               BlockCont(Undefined()::Nil, Nil, ρ)::Nil,
                               RebuildForTest(test, iter, body, ρ)::Nil)::k)

    // for (init; test; init) body
    case Σ(Label(x, For(init, test, iter, body)), ρ, σ, k) =>
      Σ(init, ρ, σ, Load(ρ)::BlockCont(Label(x, For(Empty(), test, iter, body))::Nil, Nil, ρ)::k)

    case Σ(For(init, test, iter, body), ρ, σ, k) =>
      Σ(init, ρ, σ, Load(ρ)::BlockCont(For(Empty(), test, iter, body)::Nil, Nil, ρ)::k)

    // if we're done evaluating the loop body, run the continue continuation
    case Σ(v, ρ, σ, LoopCont(_, kc)::k) if v.isValue =>
      Σ(v, ρ, σ, kc)

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
    case Σ(test, ρ, σ, RebuildWhileTest(test0, body0, ρ1)::k) if test.isValue =>
      Σ(body0, ρ1, σ, Load(ρ)::RebuildWhileBody(test, test0, body0, ρ)::k)

    // Discard the store.
    case Σ(body1, ρ, σ, RebuildWhileBody(test1, test0, body0, ρ1)::k) if body1.isValue =>
      Σ(reify(IfElse(test1, Block(body1::While(test0, body0)::Nil), Undefined())),
        ρ1, σ0, k)

    case Σ(test, ρ, σ, RebuildForTest(test0, iter0, body0, ρ1)::k) if test.isValue =>
      Σ(body0, ρ1, σ, Load(ρ)::RebuildForBody(test, test0, iter0, body0, ρ)::k)

    case Σ(body1, ρ, σ, RebuildForBody(test1, test0, iter0, body0, ρ1)::k) if body1.isValue =>
      Σ(iter0, ρ, σ, Load(ρ)::RebuildForIter(body1, test1, test0, iter0, body0, ρ1)::k)

    // Discard the store.
    case Σ(iter1, ρ, σ, RebuildForIter(body1, test1, test0, iter0, body0, ρ1)::k) if iter1.isValue =>
      Σ(reify(IfElse(test1, Block(body1::iter1::For(Empty(), test0, iter0, body0)::Nil), Undefined())),
        ρ1, σ0, k)

    // Break and continue.

    // when break hits a loop cont, run the break continuation
    case Σ(Break(None), ρ, σ, LoopCont(label, kc)::k) =>
      Σ(Undefined(), ρ, σ, k)

    case Σ(Break(Some(x)), ρ, σ, LoopCont(Some(y), kc)::k) if x == y =>
      Σ(Undefined(), ρ, σ, k)

    // when continue hits a loop cont, run the continue continuation
    case Σ(Continue(None), ρ, σ, LoopCont(label, kc)::k) =>
      Σ(Undefined(), ρ, σ, kc ++ k)

    case Σ(Continue(Some(x)), ρ, σ, LoopCont(Some(y), kc)::k) if x == y =>
      Σ(Undefined(), ρ, σ, kc ++ k)

    // propagate break to the outer continuation
    case Σ(Break(optLabel), ρ, σ, _::k) =>
      Σ(Break(optLabel), ρ, σ, k)

    // propagate continue to the outer continuation
    case Σ(Continue(optLabel), ρ, σ, _::k) =>
      Σ(Continue(optLabel), ρ, σ, k)


    ////////////////////////////////////////////////////////////////
    // Exceptions.
    ////////////////////////////////////////////////////////////////

    // case Σ(Try(e, cs, None), ρ, σ, k) =>
    //   Σ(e, ρ1, σ, CatchCont(cs, ρ)::k)
    //
    // case Σ(Try(e, Nil, Some(fin)), ρ, σ, k) =>
    //   Σ(e, ρ1, σ, FinallyCont(fin, ρ)::k)
    //
    // case Σ(Try(e, cs, Some(fin)), ρ, σ, k) =>
    //   Σ(e, ρ1, σ, CatchCont(cs, ρ, FinallyCont(fin, ρ)::k))
    //
    // case Σ(Throw(e), ρ, σ, k) =>
    //   Σ(e, ρ, σ, ThrowCont(ρ)::k)
    //
    // case Σ(v, ρ, σ, ThrowCont(_, CatchCont(cs, ρ1)::k)) if v.isValue =>
    //   Σ(v, ρ1, σ, ThrowCont(ρ1, k.next))
    //
    // case Σ(v, ρ, σ, ThrowCont(_, FinallyCont(fin, ρ1)::k)) if v.isValue =>
    //   Σ(fin, ρ1, σ, BlockCont(v::Nil, ThrowCont(ρ1)::k))
    //
    // case Σ(v, ρ, σ, ThrowCont(ρ1)::k) if v.isValue =>
    //   Σ(v, ρ1, σ, ThrowCont(ρ1, k.next))
    //
    // // not throwing an exception ... so skip the catches
    // case Σ(v, ρ, σ, CatchCont(cs, ρ1)::k) if v.isValue =>
    //   Σ(v, ρ1, σ, k)
    //
    // case Σ(v, ρ, σ, FinallyCont(fin, ρ1)::k) if v.isValue =>
    //   Σ(fin, ρ1, σ, BlockCont(v::Nil, ρ1)::k)

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
        case (σ, ((x, e), loc)) => σ + (loc -> Closure(Undefined(), ρ1))
      }
      Σ(s, ρ1, σ1, Load(ρ1)::BlockCont(ss, Nil, ρ1)::k)

    // If we don't have to save any residual for the block, just eval to the value.
    case Σ(v, ρ, σ, BlockCont(Nil, Nil, ρ1)::k) if v.isValue =>
      Σ(v, ρ1, σ, k)

    // If we have to save the block, append the value to the residual.
    case Σ(v, ρ, σ, BlockCont(Nil, done, ρ1)::k) if v.isValue =>
      Σ(reify(Block(done :+ v)), ρ1, σ, k)

    // Append non-value residuals to block residual.
    case Σ(Residual(e), ρ, σ, BlockCont(s::ss, done, ρ1)::k) if ! e.isPure =>
      Σ(s, ρ1, σ, Load(ρ)::BlockCont(ss, done :+ e, ρ1)::k)

    // Ignore non-residual values if there's more to do in the block.
    case Σ(v, ρ, σ, BlockCont(s::ss, done, ρ1)::k) if v.isValue =>
      Σ(s, ρ1, σ, Load(ρ)::BlockCont(ss, done, ρ1)::k)

    ////////////////////////////////////////////////////////////////
    // Definitions.
    ////////////////////////////////////////////////////////////////

    // Definitions eval to undefined.
    // Look up the location, which should have been added to the environment
    // when we entered the block.
    // Then run the initializer, assigning to the location.
    // The DoAssign continuation should leave the initializer in the focus,
    // but we should evaluate to undefined, so add block continuation for that.
    case Σ(VarDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, Load(ρ)::DoAssign(None, loc, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }
    case Σ(LetDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, Load(ρ)::DoAssign(None, loc, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }
    case Σ(ConstDef(x, e), ρ, σ, k) =>
      ρ.get(x) match {
        case Some(loc) =>
          Σ(e, ρ, σ, Load(ρ)::DoAssign(None, loc, ρ)::BlockCont(Undefined()::Nil, Nil, ρ)::k)
        case None =>
          Σ(e, ρ, σ, Fail(s"variable $x not found")::k)
      }

    ////////////////////////////////////////////////////////////////
    // Assignment.
    ////////////////////////////////////////////////////////////////

    case Σ(Assign(op, lhs, rhs), ρ, σ, k) =>
      Σ(lhs, ρ, σ, EvalAssignRhs(op, rhs, ρ)::k)

    case Σ(lhs: Loc, ρ, σ, EvalAssignRhs(op, rhs, ρ1)::k) if lhs.isValue =>
      Σ(rhs, ρ1, σ, Load(ρ1)::DoAssign(op, lhs, ρ)::k)

    case Σ(lhs: Loc, ρ, σ, EvalAssignRhs(op, rhs, ρ1)::k) if lhs.isValue =>
      Σ(rhs, ρ1, σ, Load(ρ1)::DoAssign(op, lhs, ρ)::k)

    case Σ(rhs, ρ, σ, DoAssign(None, lhs, ρ1)::k) if rhs.isValue =>
      // Normal assignment... the result is the rhs value
      Σ(rhs, ρ1, σ.assign(lhs, rhs, ρ), k)

    case Σ(rhs, ρ, σ, DoAssign(Some(op), lhs, ρ1)::k) if rhs.isValue =>
      val right = rhs
      σ.get(lhs) match {
        case Some(Closure(left, _)) =>
          evalOp(op, left, right) match {
            case Left((v, s)) => Σ(v, ρ1, σ, Fail(s)::k)
            case Right(v) => Σ(v, ρ1, σ.assign(lhs, v, ρ), k)
          }
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
          evalOp(binOp, oldValue, Num(1)) match {
            case Left((v, s)) =>
              Σ(v, ρ1, σ, Fail(s)::k)
            case Right(newValue) =>
              val v = op match {
                case Prefix.++ => newValue
                case Prefix.-- => newValue
                case Postfix.++ => oldValue
                case Postfix.-- => oldValue
                case _ => ???
              }
              Σ(v, ρ2, σ.assign(loc, newValue, ρ), k)
          }
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    ////////////////////////////////////////////////////////////////
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(Ident(x), ρ, σ, k) => ρ.get(x) match {
      case Some(v) =>
        Σ(v, ρ, σ, Load(ρ)::k)
      case None =>
        println(s"variable $x not found... residualizing")
        Σ(reify(Ident(x)), ρ, σ, k)
    }

    case Σ(loc: Loc, ρ, σ, Load(ρ1)::k) =>
      σ.get(loc) match {
        case Some(Closure(v, ρ2)) =>
          Σ(v, ρ2, σ, k)
        case None =>
          Σ(loc, ρ, σ, Fail(s"could not load location $loc")::k)
      }

    case Σ(v, ρ, σ, Load(ρ1)::k) if v.isValue =>
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Unary(op, e), ρ, σ, k) =>
      Σ(e, ρ, σ, Load(ρ)::DoUnaryOp(op, ρ)::k)

    case Σ(Bool(v), ρ, σ, DoUnaryOp(Prefix.!, ρ1)::k) =>
      Σ(Bool(!v), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, DoUnaryOp(Prefix.~, ρ1)::k) =>
      Σ(Num(~v.toLong), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, DoUnaryOp(Prefix.+, ρ1)::k) =>
      Σ(Num(+v), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, DoUnaryOp(Prefix.-, ρ1)::k) =>
      Σ(Num(-v), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // For other binary operations, evaluate the first argument,
    // with a continuation that evaluates the second argument.
    case Σ(Binary(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, Load(ρ)::EvalBinaryOpRight(op, e2, ρ)::k)

    // Short-circuit && and ||
    // FIXME: coercions
    case Σ(v @ Bool(false), ρ, σ, EvalBinaryOpRight(Binary.&&, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    case Σ(v @ Bool(true), ρ, σ, EvalBinaryOpRight(Binary.||, e2, ρ1)::k) =>
      Σ(v, ρ1, σ, k)

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(v, ρ, σ, EvalBinaryOpRight(op, e2, ρ1)::k) if v.isValue =>
      Σ(e2, ρ1, σ, Load(ρ1)::DoBinaryOp(op, v, ρ1)::k)

    case Σ(v2, ρ, σ, DoBinaryOp(op, v1, ρ1)::k) if v2.isValue =>
      evalOp(op, v1, v2) match {
        case Left((v, s)) => Σ(v, ρ1, σ, Fail(s)::k)
        case Right(v) => Σ(v, ρ1, σ, k)
      }

    ////////////////////////////////////////////////////////////////
    // Calls and lambda.
    // FIXME
    // Environment handling is completely broken here.
    // See the old SCSC implementation.
    ////////////////////////////////////////////////////////////////

    case Σ(Call(fun, args), ρ, σ, k) =>
      Σ(fun, ρ, σ, Load(ρ)::EvalArgs(args, ρ)::k)

    case Σ(fun, ρ, σ, EvalArgs(Nil, ρ1)::k) if fun.isValue =>
      Σ(Empty(), ρ1, σ, DoCall(fun, Nil, ρ1)::k)

    case Σ(fun, ρ, σ, EvalArgs(arg::args, ρ1)::k) if fun.isValue =>
      Σ(arg, ρ1, σ, Load(ρ1)::EvalMoreArgs(fun, args, Nil, ρ1)::k)

    case Σ(v, ρ, σ, EvalMoreArgs(fun, arg::args, done, ρ1)::k) if v.isValue =>
      Σ(arg, ρ1, σ, Load(ρ1)::EvalMoreArgs(fun, args, done :+ v, ρ1)::k)

    case Σ(v, ρ, σ, EvalMoreArgs(fun, Nil, done, ρ1)::k) if v.isValue =>
      Σ(Empty(), ρ1, σ, DoCall(fun, done :+ v, ρ1)::k)

    // Eliminate sharing of the argument by building a let for the argument.
    case Σ(_, ρ, σ, DoCall(Lambda(xs, e), args, ρ1)::k) =>
      // println("rebuilding 10 " + Let(x, arg, e).show)
      val locs = xs map { _ => FreshLoc() }
      val ρ2 = (xs zip locs).foldLeft(ρ1) {
        case (ρ1, (x, loc)) =>
          ρ1 + (x -> loc)
      }
      def pad(locs: List[Loc], args: List[Exp]): List[Exp] = (locs, args) match {
        case (Nil, _) => Nil
        case (_::locs, Nil) => Undefined()::pad(locs, Nil)
        case (_::locs, arg::args) => arg::pad(locs, args)
      }
      val args2 = pad(locs, args)
      val σ1 = (locs zip args2).foldLeft(σ) {
        case (σ, (loc, v)) =>
          σ + (loc -> Closure(v, ρ1))
      }
      Σ(e, ρ2, σ1, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.

    // The function is not a lambda. Residualize the call. Clear the store. This is too conservative!
    case Σ(_, ρ, σ, DoCall(fun, args, ρ1)::k) =>
      Σ(reify(Call(fun, args)), ρ1, σ0, k)

    // Wrap v in a let.
    case Σ(v, ρ, σ, RebuildLet(xs, args, ρ1)::k) if v.isValue =>
      val ss = (xs zip args) collect {
        case (x, e) if (fv(v) contains x) => VarDef(x, e)
      }
      if (ss.nonEmpty) {
        Σ(reify(Block(ss :+ v)), ρ1, σ, k)
      }
      else {
        Σ(v, ρ1, σ, k)
      }

    ////////////////////////////////////////////////////////////////
    // Return. Pop the continuations until we hit the caller.
    ////////////////////////////////////////////////////////////////
    case Σ(v, ρ, σ, ReturnFrame()::CallFrame(ρ1)::k) if v.isValue =>
       Σ(v, ρ1, σ, k)

    case Σ(v, ρ, σ, ReturnFrame()::_::k) if v.isValue =>
       Σ(v, ρ, σ, k)

    case Σ(Return(Some(e)), ρ, σ, k) =>
      Σ(e, ρ, σ, ReturnFrame()::k)

    case Σ(Return(None), ρ, σ, k) =>
      Σ(Undefined(), ρ, σ, ReturnFrame()::k)

    // If we run off the end of the function body, act like we returned normally.
    case Σ(v, ρ, σ, CallFrame(ρ1)::k) if v.isValue =>
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Infrastructure cases.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(_, _, σ, Nil) => s
    case s @ Σ(_, _, σ, Fail(_)::k) => s

    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s")::k)
  }

  def evalOp(op: Operator, v1: Exp, v2: Exp): Either[(Exp, String), Exp] = (op, v1, v2) match {
    // Perform some simple algebraic simplifications
    case (Binary.+, Num(0), v) => Right(v)
    case (Binary.+, v, Num(0)) => Right(v)
    case (Binary.-, v, Num(0)) => Right(v)
    case (Binary.*, Num(1), v) => Right(v)
    case (Binary.*, v, Num(1)) => Right(v)
    case (Binary./, v, Num(1)) => Right(v)

    case (Binary.+, Num(n1), Num(n2)) => Right(Num(n1 + n2))
    case (Binary.-, Num(n1), Num(n2)) => Right(Num(n1 - n2))
    case (Binary.*, Num(n1), Num(n2)) => Right(Num(n1 * n2))
    case (Binary./, Num(n1), Num(0)) => Left((v2, s"div by 0"))
    case (Binary.%, Num(n1), Num(0)) => Left((v2, s"mod by 0"))
    case (Binary./, Num(n1), Num(n2)) => Right(Num(n1 / n2))
    case (Binary.%, Num(n1), Num(n2)) => Right(Num(n1 % n2))

    case (Binary.&, Num(n1), Num(n2)) => Right(Num(n1.toLong & n2.toLong))
    case (Binary.|, Num(n1), Num(n2)) => Right(Num(n1.toLong | n2.toLong))
    case (Binary.^, Num(n1), Num(n2)) => Right(Num(n1.toLong ^ n2.toLong))
    case (Binary.>>, Num(n1), Num(n2)) => Right(Num(n1.toLong >> n2.toLong))
    case (Binary.<<, Num(n1), Num(n2)) => Right(Num(n1.toLong << n2.toLong))
    case (Binary.>>>, Num(n1), Num(n2)) => Right(Num(n1.toLong >>> n2.toLong))

    case (Binary.<, Num(n1), Num(n2)) => Right(Bool(n1 < n2))
    case (Binary.<=, Num(n1), Num(n2)) => Right(Bool(n1 <= n2))
    case (Binary.>=, Num(n1), Num(n2)) => Right(Bool(n1 >= n2))
    case (Binary.>, Num(n1), Num(n2)) => Right(Bool(n1 > n2))

    case (Binary.&&, Bool(n1), Bool(n2)) => Right(Bool(n1 && n2))
    case (Binary.||, Bool(n1), Bool(n2)) => Right(Bool(n1 || n2))

    case (Binary.BIND, v1, v2) => Left((Undefined(), "unimplemented"))
    case (Binary.COMMALEFT, v1, v2) => Left((Undefined(), "unimplemented"))
    case (Binary.COMMARIGHT, v1, v2) => Left((Undefined(), "unimplemented"))
    case (Binary.IN, v1, v2) => Left((Undefined(), "unimplemented"))
    case (Binary.INSTANCEOF, v1, v2) => Left((Undefined(), "unimplemented"))

    case (op, v1 @ Residual(e1), v2 @ Residual(e2)) => Right(reify(Binary(op, v1, v2)))
    case (op, v1, v2 @ Residual(e2)) => Right(reify(Binary(op, v1, v2)))
    case (op, v1 @ Residual(e1), v2) => Right(reify(Binary(op, v1, v2)))

    // Equality operators should not work on residuals.
    // So match after the above.
    case (Binary.==, v1, v2) => Right(Bool(v1 == v2))
    case (Binary.!=, v1, v2) => Right(Bool(v1 != v2))
    case (Binary.===, v1, v2) => Right(Bool(v1 == v2))
    case (Binary.!==, v1, v2) => Right(Bool(v1 != v2))

    // Failure
    case (op, v1: Exp, v2: Exp) =>
      Left((reify(Binary(op, v1, v2)), s"cannot apply operator $op"))
  }

  // Check for termination at these nodes.
  // In SCSC, we only checked at Ident nodes, but here we need to check
  // loops also since we can have non-termination evaluating any variables.
  object CheckHistory {
    def unapply(e: Exp) = e match {
      case Ident(x) => Some(e)
      case While(test, body) => Some(e)
      case DoWhile(body, test) => Some(e)
      case For(init, test, iter, body) => Some(e)
      case ForEach(init, test, iter, body) => Some(e)
      case ForIn(init, iter, body) => Some(e)
      case _ => None
    }
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Node, maxSteps: Int): Node = {
    import HE._

    var t = maxSteps
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
        case Σ(v, _, σ, Nil) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)::k) if v.isValue =>
          return Lambda("error"::Nil, v)

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
        case Σ(v, _, σ, Nil) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)::k) if v.isValue =>
          return Lambda("error"::Nil, v)

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
