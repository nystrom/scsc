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
    case Σ(Ident(x), ρ, σ, k) => ρ.get(x) match {
      case Some(Closure(e1, ρ1)) =>
        Σ(e1, ρ1, σ, k)
      case None =>
        println(s"variable $x not found... residualizing")
        Σ(reify(Ident(x)), ρ, σ, k)
    }

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    case Σ(Unary(op, e), ρ, σ, k) =>
      Σ(e, ρ, σ, UnaryCont(op, ρ, k))

    case Σ(Bool(v), ρ, σ, UnaryCont(Prefix.!, ρ1, k)) =>
      Σ(Bool(!v), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, UnaryCont(Prefix.~, ρ1, k)) =>
      Σ(Num(~v.toLong), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, UnaryCont(Prefix.+, ρ1, k)) =>
      Σ(Num(+v), ρ1, σ, k)

    case Σ(Num(v), ρ, σ, UnaryCont(Prefix.-, ρ1, k)) =>
      Σ(Num(-v), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // For other binary operations, evaluate the first argument,
    // with a continuation that evaluates the second argument.
    case Σ(Binary(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, OpRight(op, e2, ρ, k))

    // Short-circuit && and ||
    // FIXME: coercions
    case Σ(v @ Bool(false), ρ, σ, OpRight(Binary.&&, e2, ρ1, k)) =>
      Σ(v, ρ1, σ, k)

    case Σ(v @ Bool(true), ρ, σ, OpRight(Binary.||, e2, ρ1, k)) =>
      Σ(v, ρ1, σ, k)

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(v, ρ, σ, OpRight(op, e2, ρ1, k)) if v.isValue =>
      Σ(e2, ρ1, σ, EvalOp(op, v, ρ1, k))

    case Σ(v2, ρ, σ, EvalOp(op, v1, ρ1, k)) if v2.isValue =>
      (op, v1, v2) match {
        // Perform some simple algebraic simplifications
        case (Binary.+, Num(0), v) =>
          Σ(v, ρ1, σ, k)
        case (Binary.+, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (Binary.-, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (Binary.*, Num(1), v) =>
          Σ(v, ρ1, σ, k)
        case (Binary.*, v, Num(1)) =>
          Σ(v, ρ1, σ, k)
        case (Binary./, v, Num(1)) =>
          Σ(v, ρ1, σ, k)

        case (Binary.+, Num(n1), Num(n2)) => Σ(Num(n1 + n2), ρ1, σ, k)
        case (Binary.-, Num(n1), Num(n2)) => Σ(Num(n1 - n2), ρ1, σ, k)
        case (Binary.*, Num(n1), Num(n2)) => Σ(Num(n1 * n2), ρ1, σ, k)
        case (Binary./, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"div by 0"))
        case (Binary.%, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"mod by 0"))
        case (Binary./, Num(n1), Num(n2)) => Σ(Num(n1 / n2), ρ1, σ, k)
        case (Binary.%, Num(n1), Num(n2)) => Σ(Num(n1 % n2), ρ1, σ, k)

        case (Binary.&, Num(n1), Num(n2)) => Σ(Num(n1.toLong & n2.toLong), ρ1, σ, k)
        case (Binary.|, Num(n1), Num(n2)) => Σ(Num(n1.toLong | n2.toLong), ρ1, σ, k)
        case (Binary.^, Num(n1), Num(n2)) => Σ(Num(n1.toLong ^ n2.toLong), ρ1, σ, k)
        case (Binary.>>, Num(n1), Num(n2)) => Σ(Num(n1.toLong >> n2.toLong), ρ1, σ, k)
        case (Binary.<<, Num(n1), Num(n2)) => Σ(Num(n1.toLong << n2.toLong), ρ1, σ, k)
        case (Binary.>>>, Num(n1), Num(n2)) => Σ(Num(n1.toLong >>> n2.toLong), ρ1, σ, k)

        case (Binary.<, Num(n1), Num(n2)) => Σ(Bool(n1 < n2), ρ1, σ, k)
        case (Binary.<=, Num(n1), Num(n2)) => Σ(Bool(n1 < n2), ρ1, σ, k)
        case (Binary.>=, Num(n1), Num(n2)) => Σ(Bool(n1 < n2), ρ1, σ, k)
        case (Binary.>, Num(n1), Num(n2)) => Σ(Bool(n1 < n2), ρ1, σ, k)

        case (Binary.&&, Bool(n1), Bool(n2)) => Σ(Bool(n1 && n2), ρ1, σ, k)
        case (Binary.||, Bool(n1), Bool(n2)) => Σ(Bool(n1 || n2), ρ1, σ, k)

        case (Binary.BIND, v1, v2) => Σ(Undefined(), ρ1, σ, k)
        case (Binary.COMMALEFT, v1, v2) => Σ(Undefined(), ρ1, σ, k)
        case (Binary.COMMARIGHT, v1, v2) => Σ(Undefined(), ρ1, σ, k)
        case (Binary.IN, v1, v2) => Σ(Undefined(), ρ1, σ, k)
        case (Binary.INSTANCEOF, v1, v2) => Σ(Undefined(), ρ1, σ, k)

        case (op, v1 @ Residual(e1), v2 @ Residual(e2)) =>
          Σ(reify(Binary(op, v1, v2)), ρ1, σ, k)
        case (op, v1, v2 @ Residual(e2)) =>
          Σ(reify(Binary(op, v1, v2)), ρ1, σ, k)
        case (op, v1 @ Residual(e1), v2) =>
          Σ(reify(Binary(op, v1, v2)), ρ1, σ, k)

        // Equality operators should not work on residuals.
        // So match after the above.
        case (Binary.==, v1, v2) if v1 == v2 => Σ(Bool(v1 == v2), ρ1, σ, k)
        case (Binary.!=, v1, v2) if v1 != v2 => Σ(Bool(v1 != v2), ρ1, σ, k)
        case (Binary.===, v1, v2) if v1 == v2 => Σ(Bool(v1 == v2), ρ1, σ, k)
        case (Binary.!==, v1, v2) if v1 != v2 => Σ(Bool(v1 != v2), ρ1, σ, k)

        // Failure
        case (op, v1: Exp, v2: Exp) =>
          Σ(reify(Binary(op, v1, v2)), ρ1, σ, Fail(s"cannot apply operator $op"))
      }

    ////////////////////////////////////////////////////////////////
    // App and lambda.
    ////////////////////////////////////////////////////////////////

    case Σ(Call(fun, arg::Nil), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArg(arg, ρ, k))

    case Σ(fun, ρ, σ, EvalArg(arg, ρ1, k)) =>
      Σ(arg, ρ1, σ, DoCall(fun, ρ, k))

    // Eliminate sharing of the argument by building a let for the argument.
    // CBV only
    case Σ(arg, ρ, σ, DoCall(Lambda(x::Nil, e), ρ1, k)) if arg.isValue && ! arg.costZero =>
      // println("rebuilding 9 " + Let(x, arg, e).show)
      Σ(e, ρ1.add(x, reify(Ident(x)), ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, DoCall(Lambda(x::Nil, e), ρ1, k)) if arg.isValue && (fv(e) contains x) =>
      // println("rebuilding 10 " + Let(x, arg, e).show)
      Σ(e, ρ1.add(x, arg, ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, DoCall(Lambda(x::Nil, e), ρ1, k)) if arg.isValue =>
      Σ(e, ρ1.add(x, arg, ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, DoCall(fun, ρ1, k)) if arg.isValue =>
      Σ(reify(Call(fun, arg::Nil)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Infrastructure cases.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(_, _, σ, Done) => s
    case s @ Σ(_, _, σ, Fail(_)) => s

    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s"))
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
        case Σ(v, _, σ, Done) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)) if v.isValue =>
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
        case Σ(v, _, σ, Done) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)) if v.isValue =>
          return Lambda("error"::Nil, v)

        // case s0 @ Σ(e, ρ, σ, k) if t == 0 =>
        //   val s1 = step(s0)
        //
        //   println(s"aborting after $maxSteps...")
        //
        //   toTerm(s1) match {
        //     case Some((t1, _)) =>
        //       return t1
        //     case None =>
        //       return Lambda("nontermination", e)
        //   }

        case s0 @ Σ(focus, ρ, σ, k) =>
          val s1 = step(s0)

          s1 match {
            case Σ(focus1 @ Ident(_), ρ1, σ, k1) =>
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