package sc.imp.sc

trait ReSemantics {
  this: sc.imp.machine.Terms with States with Envs with Stores with sc.imp.machine.Continuations =>

  def reify(e: Exp) = {
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._

    lazy val fixPaths = rule[Exp] {
      case Path(_, path) => path
      case e => e
    }

    fixPaths(e) match {
      case Some(e: Exp) => e
      case _ => e
    }
  }

  abstract override def rebuild(s: Re): Option[State] = s match {
    case Re(e @ residual, σ, k) => k match {
      case Nil => None

      // Here we're about to branch with a residual test.
      // We can't actually rebuild this, dammit,
      // since we can't evaluate the continuations properly
      // here. Instead, return None, this will cause the
      // us to get stuck and we'll split.
      case BranchCont(t, f, ρ)::k => Some {
        Re(IfElse(e, reify(t), reify(f)), σ, k)
      }

      case CondBranchCont(t, f, ρ)::k => Some {
        Re(Cond(e, reify(t), reify(f)), σ, k)
      }

      case PopScope(defs)::k => Some {
        Re(defs.foldRight(e)(Seq), σ, k)
      }

      case StartLoop(loop, ρ1, σ1)::k => Some {
        Re(loop, σ1, k)
      }

      // discard useless break and continue frames
      // but wrap in a useless loop so that residual
      // breaks and continues still work.
      case BreakFrame(label)::k => Some {
        Re(DoWhile(label, e, BooleanLit(false)), σ, k)
      }

      case ContinueFrame(label)::k => Some {
        Re(DoWhile(label, e, BooleanLit(false)), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      // Discard the value and evaluate the sequel.
      case SeqCont(s2, ρ1)::k => Some {
        Re(Seq(e, s2), σ, k)
      }

      // Change the focus
      case FocusCont(v2)::k => Some {
        Re(Seq(e, reify(v2)), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, ρ1)::k => Some {
        Re(Assign(op, e, rhs), σ, k)
      }

      case DoAssign(op, lhs, ρ1)::k => Some {
        // Normal assignment... the result is the rhs value
        Re(Assign(op, reify(lhs), e), σ, k)
      }

      case DoIncDec(op, ρ1)::k => Some {
        Re(IncDec(op, e), σ, k)
      }

      case DoUnaryOp(op, ρ1)::k => Some {
        Re(Unary(op, e), σ, k)
      }

      case EvalBinaryOpRight(op, e2, ρ1)::k => Some {
        Re(Binary(op, e, e2), σ, k)
      }

      case DoBinaryOp(op, v1, ρ1)::k => Some {
        Re(Binary(op, reify(v1), e), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Calls and lambda.
      // FIXME
      // Environment handling is completely broken here.
      // See the old SCSC implementation.
      ////////////////////////////////////////////////////////////////

      case EvalArgs(op, args, ρ1)::k =>
        op match {
          case Nary.InitObject =>
            Some(Re(ObjectLit(e::args), σ, k))
          case Nary.InitArray =>
            Some(Re(ArrayLit(e::args), σ, k))
          case Nary.Call =>
            Some(Re(Call(e, args), σ, k))
          case _ =>
            None
        }

      case EvalMoreArgs(op, args, done, ρ1)::k =>
        val operands = done ++ (e::args)
        op match {
          case Nary.InitObject =>
            Some(Re(ObjectLit(operands map reify), σ, k))
          case Nary.InitArray =>
            Some(Re(ArrayLit(operands map reify), σ, k))
          case Nary.Call =>
            val fun::args = operands map reify
            Some(Re(Call(fun, args), σ, k))
          case _ =>
            None
        }

      ///////////////////////////////////////////////////////////////, k/
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k => Some {
        e match {
          case Undefined() =>
            Re(Return(None), σ, k)
          case e =>
            Re(Return(Some(e)), σ, k)
        }
      }

      // If we run off the end of the function body, act like we returned normally.
      case CallFrame(ρ1)::k => Some {
        Re(e, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k => Some {
        Re(Throw(e), σ, k)
      }

      // Run the finally block, if any. Then restore the value.
      case FinallyFrame(fin, ρ1)::k => Some {
        Re(TryFinally(e, fin), σ, k)
      }

      // If not throwing, just discard catch frames.
      case CatchFrame(cs, ρ1)::k => Some {
        Re(TryCatch(e, cs), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Objects and arrays.
      ////////////////////////////////////////////////////////////////

      case EvalIndex(op, i, ρ1)::k => Some {
        Re(Index(e, i), σ, k)
      }

      case DoArrayOp(op, a, ρ1)::k => Some {
        Re(Index(a, e), σ, k)
      }

      case _ =>
        None
    }
  }
}
