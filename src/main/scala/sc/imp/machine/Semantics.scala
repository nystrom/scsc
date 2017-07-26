package sc.imp.machine

import sc.core.machine

trait SemanticsBase {
  this: Terms with States with Envs with Stores with Continuations =>

  def doCall(op: Operator, operands: List[Value], ρ: Env, σ: Store, k: Cont): Option[State]

  def evalArrayOp(op: Operator, array: Value, index: Value, σ: Store): Option[(Value, Store)]

  def evalUnaryOp(op: Operator, v: Value): Option[Value]
  def evalBinaryShortCircuitOp(op: Operator, v1: Value): Option[Value]
  def evalBinaryOp(op: Operator, v1: Value, v2: Value): Option[Value]

  def evalPredicate(v: Value): Option[Boolean]

  def addDeclarations(e: Exp, ρ: Env, σ: Store): (List[Exp], Env, Store)

  def eval(s: Ev): Option[State]
  def continue(s: Co): Option[State]
  def unwind(s: Unwinding): Option[State]
}

trait Semantics extends EvSemantics with CoSemantics with UnwindSemantics {
  this: Terms with States with Envs with Stores with Continuations =>
}

trait CoSemantics extends SemanticsBase {
  this: Terms with States with Envs with Stores with Continuations =>

  abstract override def continue(s: Co): Option[State] = s match {
    case Co(v, σ, FinallyFrame(fin, ρ)::k) =>
      // If we hit a finally block, evaluate the finally block and then resume.
      Some(Ev(fin, ρ, σ, FocusCont(v)::k))

    case Co(v, σ, DoThrow()::k) =>
      Some(Unwinding(Throw(v), σ, k))

    case Co(v, σ, DoReturn()::k) => Some(Unwinding(Return(Some(v)), σ, k))

    case Co(v, σ, DoUnaryOp(op, ρ)::k) =>
      evalUnaryOp(op, v) map {
        result => Co(result, σ, k)
      }

    case Co(v1, σ, EvalBinaryOpRight(op, e2, ρ)::k) =>
      evalBinaryShortCircuitOp(op, v1) match {
        case Some(v) => Some(Co(v, σ, k))
        case None => Some(Ev(e2, ρ, σ, DoBinaryOp(op, v1, ρ)::k))
      }

    case Co(v2, σ, DoBinaryOp(op, v1, ρ)::k) =>
      evalBinaryOp(op, v1, v2) map {
        result => Co(result, σ, k)
      }

    case Co(argv, σ, EvalMoreArgs(op, pending, done, ρ)::k) =>
      pending match {
        case Nil => doCall(op, done :+ argv, ρ, σ, k)
        case arg::args => Some(Ev(arg, ρ, σ, EvalMoreArgs(op, args, done :+ argv, ρ)::k))
      }

    case Co(fun, σ, EvalArgs(op, pending, ρ)::k) =>
      // Used as the continuation of a function (method selector) value.
      pending match {
        case Nil => doCall(op, fun::Nil, ρ, σ, k)
        case arg::args =>
          Some(Ev(arg, ρ, σ, EvalMoreArgs(op, args, fun::Nil, ρ)::k))
      }

    // Ev(e) next
    case Co(v, σ, SeqCont(e: Exp, ρ)::k) => Some(Ev(e, ρ, σ, k))

    // Co(value) next
    case Co(v, σ, FocusCont(value)::k) => Some(Co(value, σ, k))

    // Unwinding(j) next
    case Co(v, σ, JumpCont(j)::k) => Some(Unwinding(j, σ, k))

    case Co(v, σ, (frame: AbsBranchCont)::k) =>
      evalPredicate(v) match {
        case Some(true) =>
          Some(Ev(frame.pass, frame.ρ, σ, k))
        case Some(false) =>
          Some(Ev(frame.fail, frame.ρ, σ, k))
        case _ =>
          super.continue(s)
      }

    case Co(test, σ, StartLoop(loop: Exp, ρ1: Env, σ1: Store)::k) =>
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
              super.continue(s)
          }
        case Some(false) =>
          Some(Co(Undefined(), σ, k))

        case _ =>
          super.continue(s)
      }

    // Assignment.
    case Co(lhs: Var, σ, EvalAssignRhs(op: Option[Operator], rhs: Exp, ρ)::k) => Some(Ev(rhs, ρ, σ, DoAssign(op, lhs, ρ)::k))

    case Co(rhs, σ, DoAssign(op: Option[Operator], lhs: Var, ρ)::k) =>
      op match {
        case None =>
          lhs match {
            case Path(loc, _) => Some(Co(rhs, σ.assign(loc, rhs), k))
            case _ => super.continue(s)
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
                    case None => super.continue(s)
                  }
                case _ => super.continue(s)
              }
            case _ => super.continue(s)
          }
      }

    // ++, --, etc.
    case Co(v, σ, DoIncDec(op, ρ)::k) =>
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
                  super.continue(s)
              }
            case _ => super.continue(s)
          }
        case _ => super.continue(s)
      }

    case Co(array, σ, EvalIndex(op, index, ρ)::k) =>
      Some(Ev(index, ρ, σ, DoArrayOp(op, array, ρ)::k))

    case Co(index, σ, DoArrayOp(op, array, ρ)::k) =>
      evalArrayOp(op, array, index, σ) match {
        case Some((result, σ1)) => Some(Co(result, σ1, k))
        case _ => super.continue(s)
      }

    // If we got here with a value, just throw out the defs.
    // FIXME: careful: the value might be a location and we
    // might have to residualize the path. I don't think this can
    // happen though across a Scope boundary.
    case Co(v, σ, PopScope(defs)::k) =>
      Some(Co(v, σ, k))

    case Co(v, σ, (_: LandingFrame)::k) =>
      // A landing frame is the target of unwinding jump.
      // In normal execution, it's just popped.
      Some(Co(v, σ, k))

    case Co(v, σ, k) => super.continue(s)
  }
}

trait UnwindSemantics extends SemanticsBase {
  this: Terms with States with Envs with Stores with Continuations =>

  abstract override def unwind(s: Unwinding): Option[State] = s match {
    case Unwinding(jump, σ, Nil) => super.unwind(s)

    case Unwinding(jump, σ, frame::k) => (jump, frame) match {
      case (Throw(v: Value), CatchFrame(Nil, _)) =>
        // No catches to try...keep unwinding
        Some(Unwinding(Throw(v), σ, k))

      case (Throw(v: Value), CatchFrame(Catch(ex, Some(test), body)::cs, ρ)) =>
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

      case (Throw(v: Value), CatchFrame(Catch(ex, None, body)::cs, ρ)) =>
        // Unconditional catch.
        val loc = FreshStackLoc()
        val path = Path(loc, Local(ex))
        val ρ2 = ρ + (ex -> loc)
        Some(Co(v, σ.assign(loc, Undefined()), DoAssign(None, path, ρ2)::SeqCont(body, ρ2)::k))

      case (jump, FinallyFrame(fin, ρ)) =>
        // If we're unwinding and we hit a finally block,
        // evaluate the finally block and then resume unwinding.
        Some(Ev(fin, ρ, σ, JumpCont(jump)::k))

      case (Return(Some(v: Value)), CallFrame(_)) => Some(Co(v, σ, k))
      case (Return(None), CallFrame(_)) => Some(Co(Undefined(), σ, k))

      case (Break(None), BreakFrame(label)) => Some(Co(Undefined(), σ, k))
      case (Break(x), BreakFrame(label)) if x == label => Some(Co(Undefined(), σ, k))

      case (Continue(None), ContinueFrame(label)) => Some(Co(Undefined(), σ, k))
      case (Continue(x), ContinueFrame(label)) if x == label => Some(Co(Undefined(), σ, k))

      case (jump, frame) => super.unwind(s)
    }
  }


}

trait EvSemantics extends SemanticsBase {
  this: Terms with States with Envs with Stores with Continuations =>

  abstract override def eval(s: Ev): Option[State] = s match {
    case Ev(focus, ρ, σ, k) => focus match {
      // For values, just continue
      case v: Value => Some(Co(v, σ, k))

      ////////////////////////////////////////////////////////////////
      // Scopes
      // Remember to pop the scope
      ////////////////////////////////////////////////////////////////

      case Scope(e) =>
        val (defs, ρ1, σ1) = addDeclarations(e, ρ, σ)
        Some(Ev(e, ρ1, σ1, PopScope(defs)::k))

      ////////////////////////////////////////////////////////////////
      // Conditionals
      // ? : and if/else are handled identically, duplicating code
      ////////////////////////////////////////////////////////////////

      // if e then s1 else s2
      case IfElse(e, s1, s2) =>
        Some(Ev(e, ρ, σ, BranchCont(s1, s2, ρ)::k))

      // e ? s1 : s2
      case Cond(e, s1, s2) =>
        Some(Ev(e, ρ, σ, CondBranchCont(s1, s2, ρ)::k))

      ////////////////////////////////////////////////////////////////
      // Loops.
      // This is very much complicated by break and continue.
      // Otherwise we could just desugar everything into IfElse,
      // unrolling the loop and letting generlization handle
      // termination detection and rebuilding the loop.
      ////////////////////////////////////////////////////////////////

      case e @ For(label, Undefined(), test, iter, body) => Some {
        Ev(test, ρ, σ, StartLoop(e, ρ, σ)::k)
      }

      case For(label, init, test, iter, body) => Some {
        Ev(Seq(init, For(label, Undefined(), test, iter, body)), ρ, σ, k)
      }

      // do body while test
      case e @ DoWhile(label, body, test) => Some {
        k match {
          // optimization: don't push a new break frame unless needed.
          case BreakFrame(x)::_ if label == x =>
            Ev(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::k)
          case _ =>
            Ev(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)
        }
      }

      case e @ While(label, test, body) => Some {
        Ev(test, ρ, σ, StartLoop(e, ρ, σ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Break and continue.
      ////////////////////////////////////////////////////////////////

      case Break(label) => Some {
        Unwinding(Break(label), σ, k)
      }

      case Continue(label) => Some {
        Unwinding(Continue(label), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Sequences and empty statement.
      ////////////////////////////////////////////////////////////////

      case Empty() => Some {
        Co(Undefined(), σ, k)
      }

      case Seq(s1, s2) => Some {
        Ev(s1, ρ, σ, SeqCont(s2, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Definitions.
      ////////////////////////////////////////////////////////////////

      // Definitions eval to undefined.
      // Look up the location, which should have been added to the environment
      // when we entered the block.
      // Then run the initializer, assigning to the location.
      // The DoAssign continuation should leave the initializer in the focus,
      // but we should evaluate to undefined, so add block continuation for that.

      case VarDef(x, e) =>
        ρ.get(x) map {
          loc => Ev(e, ρ, σ, DoAssign(None, Path(loc, Local(x)), ρ)::k)
        }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case Assign(op, Local(x), rhs) =>
        ρ.get(x) collect {
          case loc =>
            Co(Path(loc, Local(x)), σ, EvalAssignRhs(op, rhs, ρ)::k)
        }

        case Assign(op, Index(a, i), rhs) => Some {
          Ev(a, ρ, σ, EvalIndex(Array.Address, i, ρ)::EvalAssignRhs(op, rhs, ρ)::k)
        }

        case IncDec(op, Local(x)) =>
          ρ.get(x) collect {
            case loc =>
              Co(Path(loc, Local(x)), σ, DoIncDec(op, ρ)::k)
          }

        case IncDec(op, Index(a, i)) => Some {
          Ev(a, ρ, σ, EvalIndex(Array.Address, i, ρ)::DoIncDec(op, ρ)::k)
        }


        ////////////////////////////////////////////////////////////////
        // Variables. Just lookup the value. If not present, residualize.
        ////////////////////////////////////////////////////////////////

        case Local(x) =>
          ρ.get(x) flatMap {
            case loc =>
              σ.get(loc) collect {
                case LocClosure(heapLoc) =>
                  Co(Path(heapLoc, Local(x)), σ, k)
                case ValueClosure(v) =>
                  Co(v, σ, k)
              }
          }

        case Index(a, i) => Some {
          Ev(a, ρ, σ, EvalIndex(Array.Load, i, ρ)::k)
        }

        ////////////////////////////////////////////////////////////////
        // Unary operators.
        ////////////////////////////////////////////////////////////////

        case Unary(op, e) => Some {
          Ev(e, ρ, σ, DoUnaryOp(op, ρ)::k)
        }

        ////////////////////////////////////////////////////////////////
        // Binary operators.
        ////////////////////////////////////////////////////////////////

        case Binary(op, e1, e2) => Some {
          Ev(e1, ρ, σ, EvalBinaryOpRight(op, e2, ρ)::k)
        }

        ////////////////////////////////////////////////////////////////
        // Calls.
        ////////////////////////////////////////////////////////////////

        // A method call "x.m()" passes "x" as "this"
        case Call(Index(e, m), args) => Some {
          Ev(e, ρ, σ, EvalIndex(Array.Load, m, ρ)::EvalArgs(Nary.Call, args, ρ)::k)
        }

        case Call(fun @ Local(x), args) =>
          println(s"CALL LOCAL $fun $args")
          ρ.get(x) flatMap {
            loc =>
              σ.get(loc) collect {
                case LocClosure(funLoc) =>
                  Ev(Path(funLoc, fun), ρ, σ, EvalArgs(Nary.Call, args, ρ)::k)
            }
          }

        case Call(fun, args) => Some {
          Ev(fun, ρ, σ, EvalArgs(Nary.Call, args, ρ)::k)
        }

        ////////////////////////////////////////////////////////////////
        // Return. Pop the continuations until we hit the caller.
        ////////////////////////////////////////////////////////////////

        case Return(Some(e)) => Some {
          Ev(e, ρ, σ, DoReturn()::k)
        }

        case Return(None) => Some {
          Co(Undefined(), σ, DoReturn()::k)
        }

        ////////////////////////////////////////////////////////////////
        // Throw. This is implemented similarly to Return.
        ////////////////////////////////////////////////////////////////

        case Throw(e) => Some {
          Ev(e, ρ, σ, DoThrow()::k)
        }

        case TryCatch(e, Nil) => Some {
          Ev(e, ρ, σ, k)
        }

        case TryCatch(e, cs) => Some {
          // FIXME: need to add try/catch to the residual in case
          // residual code throws an exception...
          // OR: when a call is added to the residual, branch and simulate a residual throw
          Ev(e, ρ, σ, CatchFrame(cs, ρ)::k)
        }

        case TryFinally(e, fin) => Some {
          // FIXME: need to add try/finally to the residual in case
          // residual code throws an exception...
          Ev(e, ρ, σ, FinallyFrame(fin, ρ)::k)
        }

        ////////////////////////////////////////////////////////////////
        // Object and array literals and lambdas.
        ////////////////////////////////////////////////////////////////

        case Property(key, value) =>
          Some(Ev(key, ρ, σ, EvalBinaryOpRight(Binary.Pair, value, ρ)::k))

        // Create an empty object
        case ObjectLit(Nil) =>
          doCall(Nary.InitObject, Nil, ρ, σ, k)

        // Initialize a non-empty object.
        case ObjectLit(p::ps) => Some {
          // val q::qs = (p::ps) flatMap {
          //   case Property(k, v) => k::v::Nil
          // }
          Ev(p, ρ, σ, EvalMoreArgs(Nary.InitObject, ps, Nil, ρ)::k)
        }

        case ArrayLit(Nil) =>
          doCall(Nary.InitArray, Nil, ρ, σ, k)

        // Initialize a non-empty object.
        case ArrayLit(e::es) => Some {
          Ev(e, ρ, σ, EvalMoreArgs(Nary.InitArray, es, Nil, ρ)::k)
        }

        // Put a lambda in the heap.
        case lam @ Lambda(xs, e) => Some {
          // x = v
          // x.proto = v2
          val loc = FreshHeapLoc()
          val blob = LambdaBlob(lam)
          Co(Path(loc, lam), σ.assign(loc, blob, ρ), k)
        }

        case e => super.eval(s)
    }
  }
}
