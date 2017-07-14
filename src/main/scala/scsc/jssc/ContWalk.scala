package scsc.jssc

import scsc.js.Trees._
import scsc.js.TreeWalk._

object ContWalk {
  import Machine._
  import Continuations._

  trait ContRewriter {
    def treeRewriter: Rewriter

    def rv(e: Val): Val = treeRewriter.rewrite(e).asInstanceOf[Val]
    def re(e: Exp): Exp = treeRewriter.rewrite(e)
    def rvs(es: List[Val]): List[Val] = es map { e => rv(e) }
    def res(es: List[Exp]): List[Exp] = es map { e => re(e) }

    def rewrite(k: Cont): Cont = k map { f => rewrite(f) }

    def rewrite(k: ContFrame): ContFrame = k match {
      case EvalMoreArgs(fun, thisValue, todo, done, ρ) =>
        EvalMoreArgs(rv(fun), rv(thisValue), res(todo), rvs(done), ρ)
      case EvalMoreArgsForResidual(fun, todo, done, ρ) =>
        EvalMoreArgsForResidual(re(fun), res(todo), rvs(done), ρ)
      case EvalArgs(thisValue, todo, ρ) =>
        EvalArgs(rv(thisValue), res(todo), ρ)
      case EvalMoreArgsForNew(fun, todo, done, ρ) =>
        EvalMoreArgsForNew(rv(fun), res(todo), rvs(done), ρ)
      case EvalMoreArgsForNewResidual(fun, todo, done, ρ) =>
        EvalMoreArgsForNewResidual(re(fun), res(todo), rvs(done), ρ)
      case EvalArgsForNew(todo, ρ) =>
        EvalArgsForNew(res(todo), ρ)
      case InitProto(fun, args, ρ) =>
        InitProto(rv(fun), rvs(args), ρ)
      case EvalMethodProperty(methodProp, args, ρ) =>
        EvalMethodProperty(re(methodProp), res(args), ρ)

      case CallFrame(ρ) =>
        CallFrame(ρ)
      case CatchFrame(cs, ρ) =>
        CatchFrame(res(cs), ρ)
      case FinallyFrame(fin, ρ) =>
        FinallyFrame(re(fin), ρ)

      // Unary operators
      case DoUnaryOp(op, ρ) =>
        DoUnaryOp(op, ρ)

      // Binary operators.
      case EvalBinaryOpRight(op, e2, ρ) =>
        EvalBinaryOpRight(op, re(e2), ρ)
      case DoBinaryOp(op, v1, ρ) =>
        DoBinaryOp(op, rv(v1), ρ)

      case SeqCont(e2, ρ) =>
        SeqCont(re(e2), ρ)
      case FocusCont(v2) =>
        FocusCont(rv(v2))
      case BranchCont(ifTrue: Cont, ifFalse: Cont, ρ) =>
        BranchCont(rewrite(ifTrue), rewrite(ifFalse), ρ)
      case BreakFrame(label) =>
        BreakFrame(label)
      case ContinueFrame(label) =>
        ContinueFrame(label)

      case DoReturn() =>
        DoReturn()
      case DoThrow() =>
        DoThrow()

      // Assignment.
      case EvalAssignRhs(op, rhs, ρ) =>
        EvalAssignRhs(op, re(rhs), ρ)
      case DoAssign(op, lhs, ρ) =>
        DoAssign(op, rv(lhs), ρ)

      // ++, --, etc.
      case DoIncDec(op, ρ) =>
        DoIncDec(op, ρ)

      // typeof
      case DoTypeof(ρ) =>
        DoTypeof(ρ)

      // delete a[i]
      case EvalPropertyNameForDel(i, ρ) =>
        EvalPropertyNameForDel(re(i), ρ)
      case DoDeleteProperty(a, ρ) =>
        DoDeleteProperty(rv(a), ρ)

      // a[i]
      case EvalPropertyNameForGet(i, ρ) =>
        EvalPropertyNameForGet(re(i), ρ)
      case GetProperty(a, ρ) =>
        GetProperty(rv(a), ρ)

      // a[i] = v
      case EvalPropertyNameForSet(i, ρ) =>
        EvalPropertyNameForSet(re(i), ρ)
      case GetPropertyAddressOrCreate(a, ρ) =>
        GetPropertyAddressOrCreate(rv(a), ρ)
    }
  }
}
