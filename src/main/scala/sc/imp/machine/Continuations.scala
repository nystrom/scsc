package sc.imp.machine

import sc.core.machine

trait Continuations extends sc.core.machine.Continuations {
  this: Terms with Envs with Stores =>

  trait Frame

  // A landing frame is the target of unwinding jump.
  // In normal execution, it's just popped.
  trait LandingFrame extends Frame

  ////////////////////////////////////////////////////////////////
  // Exceptions
  ////////////////////////////////////////////////////////////////

  // try catch finally
  case class CatchFrame(cs: List[Exp], ρ: Env) extends LandingFrame
  case class FinallyFrame(fin: Exp, ρ: Env) extends Frame

  // throw
  case class DoThrow() extends Frame

  ////////////////////////////////////////////////////////////////
  // CallStack
  ////////////////////////////////////////////////////////////////

  case class CallFrame(ρ: Env) extends LandingFrame
  case class DoReturn() extends Frame

  ////////////////////////////////////////////////////////////////
  // Breaks
  ////////////////////////////////////////////////////////////////

  case class BreakFrame(label: Option[Name]) extends LandingFrame
  case class ContinueFrame(label: Option[Name]) extends LandingFrame

  ////////////////////////////////////////////////////////////////
  // UnaryOps
  ////////////////////////////////////////////////////////////////

  case class DoUnaryOp(op: Operator, ρ: Env) extends Frame

  ////////////////////////////////////////////////////////////////
  // BinaryOps
  ///////////////////////////////////////////////////////////////

  case class EvalBinaryOpRight(op: Operator, e2: Exp, ρ: Env) extends Frame
  case class DoBinaryOp(op: Operator, v1: Value, ρ: Env) extends Frame

  ////////////////////////////////////////////////////////////////
  // NaryOps
  ////////////////////////////////////////////////////////////////

  // Used for call, new, array literals, etc.
  // For simple calls, we treat the function as an argument.
  // For method calls, the receiver and the function are arguments.
  case class EvalMoreArgs(op: Operator, pending: List[Exp], done: List[Value], ρ: Env) extends Frame

  // Used as the continuation of a function (method selector) value.
  case class EvalArgs(op: Operator, pending: List[Exp], ρ: Env) extends Frame

  ////////////////////////////////////////////////////////////////
  // Sequences
  ////////////////////////////////////////////////////////////////

  // Ev(e) next
  case class SeqCont(e: Exp, ρ: Env) extends Frame

  // Co(value) next
  case class FocusCont(value: Value) extends Frame

  // Unwinding(j) next
  case class JumpCont(j: Jump) extends Frame

  ////////////////////////////////////////////////////////////////
  // Branches
  ////////////////////////////////////////////////////////////////

  trait AbsBranchCont extends Frame {
    def pass: Exp
    def fail: Exp
    def ρ: Env
  }

  case class BranchCont(pass: Exp, fail: Exp, ρ: Env) extends AbsBranchCont
  case class CondBranchCont(pass: Exp, fail: Exp, ρ: Env) extends AbsBranchCont

  ////////////////////////////////////////////////////////////////
  // Loops
  ////////////////////////////////////////////////////////////////

  case class StartLoop(loop: Exp, ρ1: Env, σ1: Store) extends Frame

  ////////////////////////////////////////////////////////////////
  // Assigns
  ////////////////////////////////////////////////////////////////

  // Assignment.
  case class EvalAssignRhs(op: Option[Operator], rhs: Exp, ρ: Env) extends Frame
  case class DoAssign(op: Option[Operator], lhs: Var, ρ: Env) extends Frame

  // ++, --, etc.
  case class DoIncDec(op: Operator, ρ: Env) extends Frame

  ////////////////////////////////////////////////////////////////
  // Arrays
  ////////////////////////////////////////////////////////////////

  case class EvalIndex(op: Operator, index: Exp, ρ: Env) extends Frame
  case class DoArrayOp(op: Operator, array: Value, ρ: Env) extends Frame

  ////////////////////////////////////////////////////////////////
  // Scopes
  ////////////////////////////////////////////////////////////////

  // If we got here with a value, just throw out the defs.
  // FIXME: careful: the value might be a location and we
  // might have to residualize the path. I don't think this can
  // happen though across a Scope boundary.
  case class PopScope(defs: List[Exp]) extends Frame
}
