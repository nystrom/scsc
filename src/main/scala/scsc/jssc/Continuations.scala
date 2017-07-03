package scsc.jssc

import scsc.js.Trees._

object Continuations {
  import Machine._

  ////////////////////////////////////////////////////////////////
  // CONTINUATIONS
  ////////////////////////////////////////////////////////////////

  // Here are the standard CEK continuations + a failure continuation
  type Cont = List[ContAction]

  sealed trait ContAction

  case class EvalMoreArgs(fun: Exp, thisValue: Exp, todo: List[Exp], done: List[Exp], ρ: Env) extends ContAction {
    override def toString = (done, todo) match {
      case (Nil, Nil) => s"${fun.show}(☐)"
      case (done, Nil) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐)"
      case (Nil, todo) => s"${fun.show}(☐, ${todo.map(_.show).mkString(", ")})"
      case (done, todo) => s"${fun.show}(${done.map(_.show).mkString(", ")}, ☐, ${todo.map(_.show).mkString(", ")})"
    }
  }
  case class EvalArgs(thisValue: Exp, todo: List[Exp], ρ: Env) extends ContAction {
    override def toString = s"☐(${todo.map(_.show).mkString(", ")})"
  }
  case class DoCall(fun: Exp, thisValue: Exp, args: List[Exp], ρ: Env) extends ContAction {
    override def toString = s"${fun.show}(${args.map(_.show).mkString(", ")}) ☐"
  }
  case class Fail(s: String) extends ContAction {
    override def toString = s"FAIL($s)"
  }

  case class InitProto(loc: Loc, ρ: Env) extends ContAction
  case class EvalMethodProperty(methodProp: Exp, args: List[Exp], ρ: Env) extends ContAction

  case class CallFrame(ρ: Env) extends ContAction
  case class ReturnFrame() extends ContAction
  case class ThrowFrame() extends ContAction
  case class CatchFrame(cs: List[Exp], ρ: Env) extends ContAction
  case class FinallyFrame(fin: Exp, ρ: Env) extends ContAction

  // Residualization:
  // For each reduction continuation, i.e., the ones that "Do" something,
  // we need to handle residual values, outputing another residual.
  //
  // But, then there's the control-flow continuations too.
  // These we _don't_ handle, instead residualization is done during folding.

  // Extensions:

  case class LoadCont(ρ: Env) extends ContAction {
    override def toString = s"LOAD ☐"
  }

  // Unary operators
  case class DoUnaryOp(op: Operator, ρ: Env) extends ContAction {
    override def toString = s"$op ☐"
  }

  // Binary operators.
  case class EvalBinaryOpRight(op: Operator, e2: Exp, ρ: Env) extends ContAction {
    override def toString = s"☐ $op ${e2.show}"
  }
  case class DoBinaryOp(op: Operator, v1: Exp, ρ: Env) extends ContAction {
    override def toString = s"${v1.show} $op ☐"
  }

  case class RebuildSeq(e1: Exp, ρ: Env) extends RebuildCont
  case class SeqCont(e2: Exp, ρ: Env) extends ContAction
  case class BranchCont(ifTrue: Cont, ifFalse: Cont, ifResidual: Cont) extends ContAction {
    override def toString = s"if (☐) { $ifTrue } else { $ifFalse } [$ifResidual]"
  }
  case class LoopContXXX(label: Option[Name], cont: Cont) extends ContAction {
    override def toString = label match {
      case Some(label) => s"$label: loop { $cont }"
      case None => s"loop { $cont }"
    }
  }
  case class BreakFrame(label: Option[Name]) extends ContAction
  case class ContinueFrame(label: Option[Name]) extends ContAction

  case class Breaking(label: Option[Name]) extends ContAction
  case class Continuing(label: Option[Name]) extends ContAction
  case class Returning(v: Exp) extends ContAction
  case class Throwing(v: Exp) extends ContAction
  case class DoReturn() extends ContAction
  case class DoThrow() extends ContAction

  // Assignment.
  case class EvalAssignRhs(op: Option[Operator], rhs: Exp, ρ: Env) extends ContAction
  case class DoAssign(op: Option[Operator], lhs: Loc, ρ: Env) extends ContAction
  case class RebuildAssign(op: Option[Operator], lhs: Exp, ρ: Env) extends ContAction

  // ++, --, etc.
  case class DoIncDec(op: Operator, ρ: Env) extends ContAction

  // typeof
  case class DoTypeof(ρ: Env) extends ContAction

  // new
  case class DoNewXXX(ρ: Env) extends ContAction

  // actions on residuals
  sealed trait RebuildCont extends ContAction

  case class RebuildLet(xs: List[Name], vs: List[Exp], ρ: Env) extends RebuildCont {
    override def toString = s"[[ let $xs = $vs in ☐ ]]"
  }

  case class RebuildScope(ρ: Env) extends RebuildCont

  case class RebuildVarDef(x: Name, ρ: Env) extends RebuildCont
  case class RebuildLetDef(x: Name, ρ: Env) extends RebuildCont
  case class RebuildConstDef(x: Name, ρ: Env) extends RebuildCont

  case class RebuildCondTest(s1: Exp, s2: Exp, ρBeforeTest: Env) extends RebuildCont
  case class RebuildCondTrue(test: Exp, s2: Exp, σAfterTest: Store, ɸAfterTest: Effect, ρBeforeTest: Env) extends RebuildCont
  case class RebuildCondFalse(test: Exp, s1: Exp, σAfterS1: Store, ɸAfterTest: Effect, ɸAfterS1: Effect, ρBeforeTest: Env) extends RebuildCont
  case class RebuildIfElseTest(s1: Exp, s2: Exp, ρBeforeTest: Env) extends RebuildCont
  case class RebuildIfElseTrue(test: Exp, s2: Exp, σAfterTest: Store, ɸAfterTest: Effect, ρBeforeTest: Env) extends RebuildCont
  case class RebuildIfElseFalse(test: Exp, s1: Exp, σAfterS1: Store, ɸAfterTest: Effect, ɸAfterS1: Effect, ρBeforeTest: Env) extends RebuildCont

  case class RebuildForTest(label: Option[Name], test: Exp, iter: Exp, body: Exp, ρ: Env) extends RebuildCont
  case class RebuildForBody(label: Option[Name], test1: Exp, test: Exp, iter: Exp, body: Exp, ρ: Env) extends RebuildCont
  case class RebuildForIter(label: Option[Name], body1: Exp, test1: Exp, test: Exp, iter: Exp, body: Exp, ρ: Env) extends RebuildCont

  case class InitObject(loc: Loc, todo: List[Exp], done: List[Exp], ρ: Env) extends ContAction
  case class WrapProperty(k: Exp, ρ: Env) extends ContAction
  case class EvalPropertyValue(v: Exp, ρ: Env) extends ContAction

  // delete a[i]
  case class EvalPropertyNameForDel(i: Exp, ρ: Env) extends ContAction
  case class DoDeleteProperty(a: Exp, ρ: Env) extends ContAction

  // a[i]
  case class EvalPropertyNameForGet(i: Exp, ρ: Env) extends ContAction
  case class GetProperty(a: Exp, ρ: Env) extends ContAction

  // a[i] = v
  case class EvalPropertyNameForSet(i: Exp, ρ: Env) extends ContAction
  case class GetPropertyAddressOrCreate(a: Exp, ρ: Env) extends ContAction
}
