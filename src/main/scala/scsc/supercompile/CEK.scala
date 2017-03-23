package scsc.supercompile

import scala.collection.mutable.ListBuffer
import scsc.syntax.LambdaSyntax._
import scsc.syntax.Trees._
import scsc.syntax.FreeVars._


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
object CEK {
  import Machine._
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
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(Var(x), ρ, σ, k) => ρ.get(x) match {
      case Some(Closure(e1, ρ1)) =>
        Σ(e1, ρ1, σ, k)
      case None =>
        println(s"variable $x not found... residualizing")
        Σ(reify(Var(x)), ρ, σ, k)
    }

    ////////////////////////////////////////////////////////////////
    // Let.
    ////////////////////////////////////////////////////////////////

    case Σ(Let(x, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, LetCont(x, e2, ρ, k))

    // Always create a continuation to rebiild the let.
    // This ensures that a let will be created if there are any residualized
    // expressions containing the variable that are created before evaluating
    // the continuation.
    case Σ(v, ρ, σ, LetCont(x, e2, ρ1, k)) if v.isValue && ! v.costZero =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.add(x, reify(Var(x)), ρ)
      // println("rebuilding 1 " + Let(x, v, e2).show)
      Σ(e2, ρ2, σ, RebuildLet(x, v, ρ1, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetCont(x, e2, ρ1, k)) if v.isValue =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.add(x, v, ρ1)
      // println("rebuilding 2 " + Let(x, v, e2).show)
      Σ(e2, ρ2, σ, RebuildLet(x, v, ρ1, k))

    case Σ(Letrec(x, e1, e2), ρ, σ, k) =>
      lazy val ρ1: Env = ρ.addrec(x, e1)
      Σ(e1, ρ1, σ, LetrecCont(x, e2, ρ, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetrecCont(x, e2, ρ1, k)) if v.isValue && ! v.costZero =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.addrec(x, reify(Var(x)))
      Σ(e2, ρ2, σ, RebuildLetrec(x, v, ρ1, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetrecCont(x, e2, ρ1, k)) if v.isValue =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.addrec(x, v)
      Σ(e2, ρ2, σ, RebuildLetrec(x, v, ρ1, k))

    // OPTIMIZATION
    // "Split" rules for `let`. Push the residualization of `let` into the context.
    // This has the effect of floating the `let` outward, but also allowing
    // evaluation under the `let`.
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, Call(fun, ρ2, k))) if v.isValue && ! (fv(fun) contains x) =>
      Σ(v, ρ, σ, Call(fun, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, EvalArg(arg, ρ2, k))) if v.isValue && ! (fv(arg) contains x) =>
      Σ(v, ρ, σ, EvalArg(arg, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, EvalAlts(alts, ρ2, k))) if v.isValue && ! (fv(Case(Num(0), alts)) contains x) =>
      Σ(v, ρ, σ, EvalAlts(alts, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, OpRight(op, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) =>
      Σ(v, ρ, σ, OpRight(op, e2, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, EvalOp(op, v1, ρ2, k))) if v.isValue && ! (fv(v1) contains x) =>
      Σ(v, ρ, σ, EvalOp(op, v1, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, LetCont(y, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) && x != y =>
      Σ(v, ρ, σ, LetCont(y, e2, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, LetrecCont(y, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) && x != y =>
      Σ(v, ρ, σ, LetrecCont(y, e2, ρ2, RebuildLet(x, e1, ρ1, k)))

    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, Call(fun, ρ2, k))) if v.isValue && ! (fv(fun) contains x) =>
      Σ(v, ρ, σ, Call(fun, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, EvalArg(arg, ρ2, k))) if v.isValue && ! (fv(arg) contains x) =>
      Σ(v, ρ, σ, EvalArg(arg, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, EvalAlts(alts, ρ2, k))) if v.isValue && ! (fv(Case(Num(0), alts)) contains x) =>
      Σ(v, ρ, σ, EvalAlts(alts, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, OpRight(op, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) =>
      Σ(v, ρ, σ, OpRight(op, e2, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, EvalOp(op, v1, ρ2, k))) if v.isValue && ! (fv(v1) contains x) =>
      Σ(v, ρ, σ, EvalOp(op, v1, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, LetCont(y, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) && x != y =>
      Σ(v, ρ, σ, LetCont(y, e2, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, LetrecCont(y, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) && x != y =>
      Σ(v, ρ, σ, LetrecCont(y, e2, ρ2, RebuildLetrec(x, e1, ρ1, k)))


    // Reify the let only if needed.
    // In particular, don't generate let x = x in e and don't generate let x = e1 in e2 if x is not free in e2
    // These are harmless except the first prevents use from easily copying and pasting the output into Haskell
    // (because Haskell's let is really letrec and let x = x is a black hole),
    // and the latter makes termination detection more difficult.
    case Σ(v, ρ, σ, RebuildLet(x, Let(y, e1, e2), ρ1, k)) if v.isValue =>
      Σ(v, ρ, σ, RebuildLet(x, e2, ρ1, RebuildLet(y, e1, ρ1, k)))

    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, k)) if v.isValue && (fv(v) contains x) && unreify(e1) != Var(x) =>
      Σ(reify(Let(x, e1, v)), ρ1, σ, k)
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, k)) if v.isValue =>
      Σ(v, ρ1, σ, k)

    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, k)) if v.isValue && (fv(v) contains x) =>
      Σ(reify(Letrec(x, e1, v)), ρ1, σ, k)
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, k)) if v.isValue =>
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Case.
    ////////////////////////////////////////////////////////////////
    case Σ(Case(e1, alts), ρ, σ, k) =>
      Σ(e1, ρ, σ, EvalAlts(alts, ρ, k))

    // Quasi-splitting... still need to push the cont down into the alts.
    // To make true splitting. Need to add a residualize continuation
    // (case x of 1 -> x)+2
    // Σ(<x>,Map(),EvalCase(List((\1 -> x)),Map(),OpRight(+,2,Map(),Done)))
    // Rather than residualize the whole case, do each alt with the same continuation,
    // then replace k with Done. (or push upto a certain depth or push until free variable capture?)
    // this is what supercompilation by evaluation does.

    // This is the rule where we have options.
    // We want to try all the alts (in order, to be like Haskell if needed).
    // Pushing the stack into each alt.
    // But we add a barrier (optionally).
    // If more than one alt succeeds, we use the barrier to merge the states.
    // Typically the barrier is just after the case expression... it's Barrier(k) itself.
    // But it could be pushed arbitarily far into k resulting in code explosion as we duplicate
    // the continuation after the case expression.

    // Reify Ctors correctly. Otherwise EvalAlts won't rebuild the case.
    // case Σ(v @ Ctor(n, es), ρ, σ, k) if v.isValue && es.exists { case Residual(_) => true; case _ => false } =>
    //   Σ(reify(Ctor(n, es)), ρ, σ, k)

    // We have two cases. If the scrutinee is a residual, we rebuild the case expression.
    // Otherwise, we evaluate the alts, one of which should match since we have a value.
    // We have to be careful to split here because EvalAlts will not work correctly
    // if given a Residual. FIXME: make it more robust to this. Should really combine
    // EvalAlts and RebuildCase.
    case Σ(Residual(e), ρ, σ, EvalAlts(alts, ρ1, k)) =>
      Σ(reify(e), ρ1, σ, RebuildCase(alts, Nil, ρ1, None, k))

    case Σ(v, ρ, σ, EvalAlts(Alt(p, e)::alts, ρ1, k)) if v.isValue =>
      matchPat(v, p, ρ1, k) match {
        case Some((ρ2, k2)) =>
          // Match was successful, evaluate the body of the alt.
          // FIXME: need to restore the ρ in k.
          Σ(e, ρ2, σ, k2)
        case None =>
          // Match failed, go to the next alt with the same scrutinee.
          Σ(v, ρ1, σ, EvalAlts(alts, ρ1, k))
      }
    // NOTE: there is no case for EvalAlts(Nil, k) -- it should just fail

    case Σ(v, ρ, σ, RebuildCase(Alt(p, e)::alts, altsPrime, ρ1, σOpt1, k)) if v.isValue =>
      println("matching " + v + " vs " + p)
      matchPat(v, p, ρ1, k) match {
        case Some((ρ2, k2)) =>
          println("  --> " + ρ2)
          // Match was successful, evaluate the body of the alt.
          // FIXME: need to restore the ρ in k.
          Σ(e, ρ1, σ, RebuildAlt(v, p, alts, altsPrime, ρ1, k2))
        case None =>
          println("  --> failed")
          // Match failed, go to the next alt with the same scrutinee.
          Σ(v, ρ1, σ, RebuildCase(alts, altsPrime, ρ1, Some(σOpt1.map(mergeStores(σ, _)).getOrElse(σ)), k))
      }

    case Σ(v, ρ, σ, RebuildCase(Nil, altsPrime, ρ1, σOpt1, k)) if v.isValue =>
      Σ(reify(Case(v, altsPrime.reverse)), ρ1, σOpt1.getOrElse(σ), k)

    case Σ(v, ρ, σ, RebuildAlt(scrutinee, p, alts, altsPrime, ρ1, k)) if v.isValue =>
      Σ(scrutinee, ρ1, σ, RebuildCase(alts, Alt(p, v)::altsPrime, ρ1, Some(σ), k))

      // TODO: a Barrier can be inserted arbitarily deep into k.
      // If immediately before k, we simulate partial evaluation
      // If immediately before the Done at the very bottom of k, we
      // simulate supercompilation.
      // Barriers merge different non-failing continuations.
      // FIXME: confusion between Barrier and Try. If we have Try do we need Barrier?
      // Both are just there to run try all the continuations and then merge the
      // non failing results. I think we still need the barrier to know
      // when to merge the results to get the residual program.

      // Need a new continuation that merges the different alts and rebuilds.
      // Need to record the pattern matching test too so we can recreate the alt.
      // This is getting complicated!!!
      // Better would be to just have some sort of Try and Catch continuations.
      // Try evaluates all possibilities to values.
      // Need to record the pattern match if definitely matches.
      // If _might_ match, need to residualize the matching.
      // Catch takes the results of all the Tries and merges them.
      // Need to handle state too when we extend to CESK.
      // Maybe we should drop the patterns in lambdas as unnecessarily complex,
      // but then again we get residualized lambdas too if we leave it.

      // case Σ(v, ρ, MergeAlts(v1, alts, k) => Σ(Residual(Case(v1, alts), ρ, k)
      // val b = MergeAlts(v, Nil, k)

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    // Desugar !e into (case e of True -> False | False -> True)
    case Σ(Not(e), ρ, σ, k) =>
      Σ(If(e, False, True), ρ, σ, k)

    // Desugar -e into (0-e)
    case Σ(Neg(e), ρ, σ, k) =>
      Σ(Sub(Num(0), e), ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // Just desugar && and || into a case (implementing an if).
    case Σ(Bin(OpAnd, e1, e2), ρ, σ, k) =>
      Σ(If(e1, e2, False), ρ, σ, k)

    case Σ(Bin(OpOr, e1, e2), ρ, σ, k) =>
      Σ(If(e1, True, e2), ρ, σ, k)

    // For other binary operations, evaluate the first argument,
    // with a continuation that evaluates the second argument.
    case Σ(Bin(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, OpRight(op, e2, ρ, k))

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(v, ρ, σ, OpRight(op, e2, ρ1, k)) if v.isValue =>
      Σ(e2, ρ1, σ, EvalOp(op, v, ρ1, k))

    case Σ(v2, ρ, σ, EvalOp(op, v1, ρ1, k)) if v2.isValue =>
      (op, v1, v2) match {
        // Perform some simple algebraic simplifications
        case (OpAdd, Num(0), v) =>
          Σ(v, ρ1, σ, k)
        case (OpAdd, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (OpSub, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (OpMul, Num(1), v) =>
          Σ(v, ρ1, σ, k)
        case (OpMul, v, Num(1)) =>
          Σ(v, ρ1, σ, k)
        case (OpDiv, v, Num(1)) =>
          Σ(v, ρ1, σ, k)

        case (OpAdd, Num(n1), Num(n2)) => Σ(Num(n1 + n2), ρ1, σ, k)
        case (OpSub, Num(n1), Num(n2)) => Σ(Num(n1 - n2), ρ1, σ, k)
        case (OpMul, Num(n1), Num(n2)) => Σ(Num(n1 * n2), ρ1, σ, k)
        case (OpDiv, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"div by 0"))
        case (OpMod, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"mod by 0"))
        case (OpDiv, Num(n1), Num(n2)) => Σ(Num(n1 / n2), ρ1, σ, k)
        case (OpMod, Num(n1), Num(n2)) => Σ(Num(n1 % n2), ρ1, σ, k)

        case (OpLt, Num(n1), Num(n2)) if n1 < n2 => Σ(True, ρ1, σ, k)
        case (OpLe, Num(n1), Num(n2)) if n1 <= n2 => Σ(True, ρ1, σ, k)
        case (OpGe, Num(n1), Num(n2)) if n1 >= n2 => Σ(True, ρ1, σ, k)
        case (OpGt, Num(n1), Num(n2)) if n1 > n2 => Σ(True, ρ1, σ, k)
        case (OpLt, Num(n1), Num(n2)) => Σ(False, ρ1, σ, k)
        case (OpLe, Num(n1), Num(n2)) => Σ(False, ρ1, σ, k)
        case (OpGe, Num(n1), Num(n2)) => Σ(False, ρ1, σ, k)
        case (OpGt, Num(n1), Num(n2)) => Σ(False, ρ1, σ, k)

        // EXTENSION
        // FIXME: sharing! The let rules seem broken.
        // We want to evaluate under a lambda, but this seems to fail.

        // case (op, Residual(e1), Residual(e2)) if ! e1.costZero && ! e2.costZero =>
        //   val x1 = FreshVar()
        //   val x2 = FreshVar()
        //   Σ(reify(Let(x1, e1, Let(x2, e2, Bin(op, Var(x1), Var(x2))))), ρ1, σ, k)
        // case (op, v1, Residual(e2)) if ! e2.costZero =>
        //   val x2 = FreshVar()
        //   Σ(reify(Let(x2, e2, Bin(op, v1, Var(x2)))), ρ1, σ, k)
        // case (op, Residual(e1), v2) if ! e1.costZero =>
        //   val x1 = FreshVar()
        //   Σ(reify(Let(x1, e1, Bin(op, Var(x1), v2))), ρ1, σ, k)

        case (op, v1 @ Residual(e1), v2 @ Residual(e2)) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)
        case (op, v1, v2 @ Residual(e2)) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)
        case (op, v1 @ Residual(e1), v2) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)

        // Equality operators should not work on residuals.
        // So match after the above.
        case (OpEq, v1, v2) if v1 == v2 => Σ(True, ρ1, σ, k)
        case (OpNe, v1, v2) if v1 != v2 => Σ(True, ρ1, σ, k)
        case (OpEq, v1, v2) => Σ(False, ρ1, σ, k)
        case (OpNe, v1, v2) => Σ(False, ρ1, σ, k)

        // Failure
        case _ =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, Fail(s"cannot apply operator $op"))
      }

    ////////////////////////////////////////////////////////////////
    // Constructors. TODO: generalize to App.
    ////////////////////////////////////////////////////////////////

    case Σ(Ctor(n, e::es), ρ, σ, k) if ! (e::es).forall(_.isValue) =>
      Σ(e, ρ, σ, EvalCtorArgs(n, es, Nil, ρ, k))

    case Σ(v, ρ, σ, EvalCtorArgs(n, e::es, vs, ρ1, k)) if v.isValue =>
      Σ(e, ρ1, σ, EvalCtorArgs(n, es, v::vs, ρ, k))

    case Σ(v, _, σ, EvalCtorArgs(n, Nil, vs, ρ, k)) if v.isValue =>
      Σ(Ctor(n, (v::vs).reverse), ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // App and lambda.
    ////////////////////////////////////////////////////////////////

    case Σ(App(fun, arg), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArg(arg, ρ, k))

    case Σ(fun, ρ, σ, EvalArg(arg, ρ1, k)) =>
      Σ(arg, ρ1, σ, Call(fun, ρ, k))

    // Eliminate sharing of the argument by building a let for the argument.
    // CBV only
    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue && ! arg.costZero =>
      // println("rebuilding 9 " + Let(x, arg, e).show)
      Σ(e, ρ1.add(x, reify(Var(x)), ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue && (fv(e) contains x) =>
      // println("rebuilding 10 " + Let(x, arg, e).show)
      Σ(e, ρ1.add(x, arg, ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue =>
      Σ(e, ρ1.add(x, arg, ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, Call(fun, ρ1, k)) if arg.isValue =>
      Σ(reify(App(fun, arg)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Infrastructure cases.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(_, _, σ, Done) => s
    case s @ Σ(_, _, σ, Fail(_)) => s
    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s"))
  }

  // TODO: push the scrutinee into the alt. If the pattern is a Cons, then we know
  // the scrutinee is a Cons. So:
  //   case ys of Nil -> e1 | Cons x xs -> e2
  //   ==>
  //   case [[ys]] of Nil -> let ys = Nil in e1
  //                | Cons x xs -> let ys = Cons x xs in e2

  // Pattern matching, extended with residual values.
  def matchPat(v: Exp, p: Pat, ρ: Env, k: Cont): Option[(Env, Cont)] = (v, p) match {
    case (v, PVar(x)) => Some(ρ.add(x, v, ρ), RebuildLet(x, v, ρ, k))
    case (Num(n1), PNum(n2)) if n1 != n2 => None
    case (Num(n1), PNum(n2)) => Some((ρ, k))
    case (Ctor(n1, _), PCtor(n2, _)) if n1 != n2 => None
    case (Ctor(n1, Nil), PCtor(n2, Nil)) => Some((ρ, k))
    case (Ctor(n1, a::as), PCtor(n2, q::qs)) =>
      for {
        (ρ1, k1) <- matchPat(a, q, ρ, k)
        (ρ2, k2) <- matchPat(Ctor(n1, as), PCtor(n2, qs), ρ1, k1)
      } yield (ρ2, k2)
    case (Residual(Ctor(n1, _)), PCtor(n2, _)) if n1 != n2 => None
    case (Residual(Ctor(n1, Nil)), PCtor(n2, Nil)) => Some((ρ, k))
    case (Residual(Ctor(n1, a::as)), PCtor(n2, q::qs)) =>
      for {
        (ρ1, k1) <- matchPat(reify(a), q, ρ, k)
        (ρ2, k2) <- matchPat(Residual(Ctor(n1, as)), PCtor(n2, qs), ρ1, k1)
      } yield (ρ2, k2)
    // Any residual value _might_ match the pattern.
    // TODO: check the type and other constraints.
    // Just return the original environment without binding the variables
    // in the pattern.
    case (Residual(e), p) => Some((ρ, k))
    case _ => None
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
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
        case Σ(v, _, σ, Done) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)) if v.isValue =>
          return Lam("error", v)

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
        case Σ(v, _, σ, Done) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)) if v.isValue =>
          return Lam("error", v)

        // case s0 @ Σ(e, ρ, σ, k) if t == 0 =>
        //   val s1 = step(s0)
        //
        //   println(s"aborting after $maxSteps...")
        //
        //   toTerm(s1) match {
        //     case Some((t1, _)) =>
        //       return t1
        //     case None =>
        //       return Lam("nontermination", e)
        //   }

        case s0 @ Σ(focus, ρ, σ, k) =>
          val s1 = step(s0)

          s1 match {
            case Σ(focus1 @ Var(_), ρ1, σ, k1) =>
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
                        return Lam("error", focus1)
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
