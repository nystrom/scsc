package scsc.jssc

import scsc.js.Trees._

object Continuations {
  import Machine._

  ////////////////////////////////////////////////////////////////
  // CONTINUATIONS
  ////////////////////////////////////////////////////////////////

  // Here are the standard CEK continuations + a failure continuation
  type Cont = List[ContFrame]

  sealed trait ContFrame

  case class EvalMoreArgs(fun: Exp, thisValue: Exp, todo: List[Exp], done: List[Exp], ρ: Env) extends ContFrame {
    override def toString = (done, todo) match {
      case (Nil, Nil) => s"${fun.show}(☐)"
      case (done, Nil) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐)"
      case (Nil, todo) => s"${fun.show}(☐, ${todo.map(_.show).mkString(", ")})"
      case (done, todo) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐, ${todo.map(_.show).mkString(", ")})"
    }
  }
  case class EvalArgs(thisValue: Exp, todo: List[Exp], ρ: Env) extends ContFrame {
    override def toString = s"☐(${todo.map(_.show).mkString(", ")})"
  }
  case class EvalMoreArgsForNew(fun: Exp, todo: List[Exp], done: List[Exp], ρ: Env) extends ContFrame {
    override def toString = (done, todo) match {
      case (Nil, Nil) => s"${fun.show}(☐)"
      case (done, Nil) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐)"
      case (Nil, todo) => s"${fun.show}(☐, ${todo.map(_.show).mkString(", ")})"
      case (done, todo) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐, ${todo.map(_.show).mkString(", ")})"
    }
  }
  case class EvalArgsForNew(todo: List[Exp], ρ: Env) extends ContFrame {
    override def toString = s"☐(${todo.map(_.show).mkString(", ")})"
  }
  case class DoCall(fun: Exp, thisValue: Exp, args: List[Exp], residual: Exp, ρ: Env) extends ContFrame {
    override def toString = s"${fun.show}(${args.map(_.show).mkString(", ")})"
  }

  case class InitProto(fun: Exp, args: List[Exp], ρ: Env) extends ContFrame
  case class EvalMethodProperty(methodProp: Exp, args: List[Exp], ρ: Env) extends ContFrame

  case class CallFrame(ρ: Env) extends ContFrame
  case class ReturnFrame() extends ContFrame
  case class ThrowFrame() extends ContFrame
  case class CatchFrame(cs: List[Exp], ρ: Env) extends ContFrame
  case class FinallyFrame(fin: Exp, ρ: Env) extends ContFrame

  case class Reset(test: Exp, σ2: Store, φ0: Effect, ρ0: Env, kf: Cont) extends ContFrame
  case class Merge(v1: Exp, σ1: Store, φ1: Effect, test: Exp, φ0: Effect, ρ0: Env) extends ContFrame

  // Residualization:
  // For each reduction continuation, i.e., the ones that "Do" something,
  // we need to handle residual values, outputing another residual.
  //
  // But, then there's the control-flow continuations too.
  // These we _don't_ handle, instead residualization is done during folding.

  // Extensions:

  case class LoadCont(ρ: Env) extends ContFrame {
    override def toString = s"LOAD ☐"
  }

  // Unary operators
  case class DoUnaryOp(op: Operator, ρ: Env) extends ContFrame {
    override def toString = s"$op ☐"
  }

  // Binary operators.
  case class EvalBinaryOpRight(op: Operator, e2: Exp, ρ: Env) extends ContFrame {
    override def toString = s"☐ $op ${e2.show}"
  }
  case class DoBinaryOp(op: Operator, v1: Exp, ρ: Env) extends ContFrame {
    override def toString = s"${v1.show} $op ☐"
  }

  case class SeqCont(e2: Exp, ρ: Env) extends ContFrame // Ev(e2) next
  case class FocusCont(v2: Exp) extends ContFrame  // Co(v2) next
  case class BranchCont(ifTrue: Cont, ifFalse: Cont, ρ: Env) extends ContFrame {
    override def toString = s"if (☐) { $ifTrue } else { $ifFalse }"
  }
  case class BreakFrame(label: Option[Name]) extends ContFrame
  case class ContinueFrame(label: Option[Name]) extends ContFrame

  case class Breaking(label: Option[Name]) extends ContFrame
  case class Continuing(label: Option[Name]) extends ContFrame
  case class Returning(v: Exp) extends ContFrame
  case class Throwing(v: Exp) extends ContFrame
  case class DoReturn() extends ContFrame
  case class DoThrow() extends ContFrame

  // Assignment.
  case class EvalAssignRhs(op: Option[Operator], rhs: Exp, lhsPath: Exp, ρ: Env) extends ContFrame
  case class DoAssign(op: Option[Operator], lhs: Exp, ρ: Env) extends ContFrame

  // ++, --, etc.
  case class DoIncDec(op: Operator, ρ: Env) extends ContFrame

  // typeof
  case class DoTypeof(ρ: Env) extends ContFrame

  case class InitObject(loc: Loc, todo: List[Exp], done: List[Exp], ρ: Env) extends ContFrame
  case class WrapProperty(k: Exp, ρ: Env) extends ContFrame
  case class EvalPropertyValue(v: Exp, ρ: Env) extends ContFrame

  // delete a[i]
  case class EvalPropertyNameForDel(i: Exp, ρ: Env) extends ContFrame
  case class DoDeleteProperty(a: Exp, ρ: Env) extends ContFrame

  // a[i]
  case class EvalPropertyNameForGet(i: Exp, ρ: Env) extends ContFrame
  case class GetProperty(a: Exp, ρ: Env) extends ContFrame

  // a[i] = v
  case class EvalPropertyNameForSet(i: Exp, ρ: Env) extends ContFrame
  case class GetPropertyAddressOrCreate(a: Exp, ρ: Env) extends ContFrame
}
