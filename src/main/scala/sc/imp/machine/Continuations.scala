package sc.imp.machine

import sc.core.machine

trait Continuations extends machine.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import states._

  trait Frame {
    def step(s: Co): Option[State] = None

    // The default implementation of unwinding is to pop the frame
    def unwind(s: Unwinding): Option[State] = s match {
      case Unwinding(jump, σ, _::k) => Some(Unwinding(jump, σ, k))
      case _ => None
    }
  }

  // A landing frame is the target of unwinding jump.
  // In normal execution, it's just popped.
  trait LandingFrame extends Frame {
    override def step(s: Co): Option[State] = s match {
      case Co(v, σ, _::k) => Some(Co(v, σ, k))
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Exceptions
  ////////////////////////////////////////////////////////////////

  // try catch finally
  case class CatchFrame(cs: List[Exp], ρ: Env) extends LandingFrame {
    override def unwind(s: Unwinding) = s match {
      // No catches to try...keep unwinding
      case Unwinding(Throw(v: Value), σ, CatchFrame(Nil, _)::k) =>
        Some(Unwinding(Throw(v), σ, k))

      case Unwinding(Throw(v: Value), σ, CatchFrame(Catch(ex, Some(test), body)::cs, _)::k) =>
        // Conditional catch.
        // We have to be careful to move the remaining catches into the else part of the if below rather than
        // leaving a CatchFrame with the remaining catches in the continuation. This is because if the body
        // of the catch throws an exception we don't want it caught by later handlers of the same try.
        val loc = FreshStackLoc()
        val path = Path(loc, Local(ex))
        val ρ2 = ρ + (ex -> loc)
        val rethrow = cs match {
          case Nil => Throw(v)
          case cs => TryCatch(Throw(v), cs)
        }
        Some(Co(v, σ.assign(loc, Undefined()), DoAssign(None, path, ρ2)::SeqCont(IfElse(test, body, rethrow), ρ2)::k))

      case Unwinding(Throw(v: Value), σ, CatchFrame(Catch(ex, None, body)::cs, _)::k) =>
        // Unconditional catch.
        val loc = FreshStackLoc()
        val path = Path(loc, Local(ex))
        val ρ2 = ρ + (ex -> loc)
        Some(Co(v, σ.assign(loc, Undefined()), DoAssign(None, path, ρ2)::SeqCont(body, ρ2)::k))
    }
  }

  case class FinallyFrame(fin: Exp, ρ: Env) extends Frame {
    // If we're unwinding and we hit a finally block,
    // evaluate the finally block and then resume unwinding.
    override def unwind(s: Unwinding) = s match {
      case Unwinding(jump, σ, _::k) => Some(Ev(fin, ρ, σ, JumpCont(jump)::k))
      case _ => super.unwind(s)
    }
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Ev(fin, ρ, σ, FocusCont(v)::k))
      case _ => super.step(s)
    }
  }

  // throw
  case class DoThrow() extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Unwinding(Throw(v), σ, k))
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // CallStack
  ////////////////////////////////////////////////////////////////

  case class CallFrame(ρ: Env) extends LandingFrame {
    override def unwind(s: Unwinding) = s match {
      case Unwinding(Return(Some(v: Value)), σ, _::k) => Some(Co(v, σ, k))
      case Unwinding(Return(None), σ, _::k) => Some(Co(Undefined(), σ, k))
      case s => super.unwind(s)
    }
  }

  case class DoReturn() extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Unwinding(Return(Some(v)), σ, k))
      case s => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Breaks
  ////////////////////////////////////////////////////////////////

  case class BreakFrame(label: Option[Name]) extends LandingFrame {
    override def unwind(s: Unwinding) = s match {
      case Unwinding(Break(None), σ, _::k) => Some(Co(Undefined(), σ, k))
      case Unwinding(Break(x), σ, _::k) if x == label => Some(Co(Undefined(), σ, k))
      case s => super.unwind(s)
    }
  }

  case class ContinueFrame(label: Option[Name]) extends LandingFrame {
    override def unwind(s: Unwinding) = s match {
      case Unwinding(Continue(None), σ, _::k) => Some(Co(Undefined(), σ, k))
      case Unwinding(Continue(x), σ, _::k) if x == label => Some(Co(Undefined(), σ, k))
      case s => super.unwind(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // UnaryOps
  ////////////////////////////////////////////////////////////////

  case class DoUnaryOp(op: Operator, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) =>
        evalUnaryOp(op, v) map {
          result => Co(result, σ, k)
        }
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // BinaryOps
  ///////////////////////////////////////////////////////////////

  case class EvalBinaryOpRight(op: Operator, e2: Exp, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(v1, σ, _::k) =>
        evalBinaryShortCircuitOp(op, v1) match {
          case Some(v) => Some(Co(v, σ, k))
          case None => Some(Ev(e2, ρ, σ, DoBinaryOp(op, v1, ρ)::k))
        }
      case s =>
        super.step(s)
    }
  }

  case class DoBinaryOp(op: Operator, v1: Value, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(v2, σ, _::k) =>
        evalBinaryOp(op, v1, v2) map {
          result => Co(result, σ, k)
        }
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // NaryOps
  ////////////////////////////////////////////////////////////////

  // Used for call, new, array literals, etc.
  // For simple calls, we treat the function as an argument.
  // For method calls, the receiver and the function are arguments.
  case class EvalMoreArgs(op: Operator, pending: List[Exp], done: List[Value], ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(argv, σ, _::k) =>
        pending match {
          case Nil => doCall(op, done :+ argv, ρ, σ, k)
          case arg::args => Some(Ev(arg, ρ, σ, EvalMoreArgs(op, args, done :+ argv, ρ)::k))
        }
      case _ => super.step(s)
    }
  }

  // Used as the continuation of a function (method selector) value.
  case class EvalArgs(op: Operator, pending: List[Exp], ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(fun, σ, _::k) =>
        pending match {
          case Nil => doCall(op, fun::Nil, ρ, σ, k)
          case arg::args =>
            Some(Ev(arg, ρ, σ, EvalMoreArgs(op, args, fun::Nil, ρ)::k))
        }
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Sequences
  ////////////////////////////////////////////////////////////////

  // Ev(e) next
  case class SeqCont(e: Exp, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Ev(e, ρ, σ, k))
      case s => super.step(s)
    }
  }

  // Co(value) next
  case class FocusCont(value: Value) extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Co(value, σ, k))
      case s => super.step(s)
    }
  }

  // Unwinding(j) next
  case class JumpCont(j: Jump) extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Unwinding(j, σ, k))
      case s => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Branches
  ////////////////////////////////////////////////////////////////

  trait AbsBranchCont extends Frame {
    def pass: Exp
    def fail: Exp
    def ρ: Env

    override def step(s: Co) = s match {
      case Co(v, σ, _::k) =>
        evalPredicate(v) match {
          case Some(true) =>
            Some(Ev(pass, ρ, σ, k))
          case Some(false) =>
            Some(Ev(fail, ρ, σ, k))
          case _ =>
            super.step(s)
        }
      case s => super.step(s)
    }
  }

  case class BranchCont(pass: Exp, fail: Exp, ρ: Env) extends AbsBranchCont
  case class CondBranchCont(pass: Exp, fail: Exp, ρ: Env) extends AbsBranchCont

  ////////////////////////////////////////////////////////////////
  // Loops
  ////////////////////////////////////////////////////////////////

  case class StartLoop(loop: Exp, ρ1: Env, σ1: Store) extends Frame {
    override def step(s: Co) = s match {
      case Co(test, σ, _::k) =>
        evalPredicate(test) match {
          case Some(true) =>
            loop match {
              case Loop(label, body, next) =>
                // Optimization: collapse consecutive break frames
                val k1 = k match {
                  case BreakFrame(x)::knobreak if label == x => knobreak
                  case _ => k
                }
                Some(Ev(body, ρ1, σ, ContinueFrame(label)::SeqCont(next, ρ1)::BreakFrame(label)::k1))
              case _ =>
                super.step(s)
            }
          case Some(false) =>
            Some(Co(Undefined(), σ, k))

          case _ =>
            super.step(s)
        }
    }
  }

  ////////////////////////////////////////////////////////////////
  // Assigns
  ////////////////////////////////////////////////////////////////

  // Assignment.
  case class EvalAssignRhs(op: Option[Operator], rhs: Exp, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(lhs: Var, σ, _::k) => Some(Ev(rhs, ρ, σ, DoAssign(op, lhs, ρ)::k))
      case _ => super.step(s)
    }
  }

  case class DoAssign(op: Option[Operator], lhs: Var, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(rhs, σ, _::k) =>
        op match {
          case None =>
            lhs match {
              case Path(loc, _) => Some(Co(rhs, σ.assign(loc, rhs), k))
              case _ => super.step(s)
            }
          case Some(op) =>
            lhs match {
              case Path(loc, _) =>
                σ.get(loc) match {
                  case Some(ValueClosure(left)) =>
                    val right = rhs
                    evalBinaryOp(op, left, right) match {
                      case Some(result: Value) =>
                        Some(Co(result, σ.assign(loc, result), k))
                      case None => super.step(s)
                    }
                  case _ => super.step(s)
                }
              case _ => super.step(s)
            }
        }
      case _ => super.step(s)
    }
  }

  // ++, --, etc.
  case class DoIncDec(op: Operator, ρ: Env) extends Frame {
    override def step(s: Co): Option[State] = s match {
      case Co(v, σ, _::k) =>
        v match {
          case Path(loc, path) =>
            σ.get(loc) match {
              case Some(ValueClosure(oldValue)) =>
                val binOp = op match {
                  case Prefix.++ => Binary.+
                  case Prefix.-- => Binary.-
                  case Postfix.++ => Binary.+
                  case Postfix.-- => Binary.-
                  case _ => ???
                }
                evalBinaryOp(binOp, oldValue, IntLit(1)) match {
                  case Some(newValue) =>
                    val resultValue = op match {
                      case Prefix.++ => newValue
                      case Prefix.-- => newValue
                      case Postfix.++ => oldValue
                      case Postfix.-- => oldValue
                      case _ => ???
                    }
                    Some(Co(resultValue, σ.assign(loc, newValue), k))
                  case _ =>
                    super.step(s)
                }
              case _ => super.step(s)
            }
          case _ => super.step(s)
        }
      case _ => super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Arrays
  ////////////////////////////////////////////////////////////////

  case class EvalIndex(op: Operator, index: Exp, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(array, σ, _::k) =>
        Some(Ev(index, ρ, σ, DoArrayOp(op, array, ρ)::k))
      case _ =>
        super.step(s)
    }
  }

  case class DoArrayOp(op: Operator, array: Value, ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(index, σ, _::k) =>
        evalArrayOp(op, array, index, σ) match {
          case Some((result, σ1)) => Some(Co(result, σ1, k))
          case _ => super.step(s)
        }
      case _ =>
        super.step(s)
    }
  }

  ////////////////////////////////////////////////////////////////
  // Scopes
  ////////////////////////////////////////////////////////////////

  // If we got here with a value, just throw out the defs.
  // FIXME: careful: the value might be a location and we
  // might have to residualize the path. I don't think this can
  // happen though across a Scope boundary.
  case class PopScope(defs: List[Exp]) extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) => Some(Co(v, σ, k))
      case _ => super.step(s)
    }
  }
}
