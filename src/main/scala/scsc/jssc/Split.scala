package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar

// This object defines the interpreter states and implements the step function
// for the JS interpreter.
object Split {
  import Machine._
  import Continuations._
  import scsc.core.Residualization._
  import States._

  val LONG_CONTINUATIONS = false

  // If we hit a stuck state.

  type Merger = (List[State], Cont) => Option[(List[State], Cont)]

  // We enter a stuck state when a Co state cannot make progress.
  // This happens in a few cases:
  // - a BranchCont where the value is a residual
  // - Unwinding throw where the exception is a residual
  // - when the whistle blows and Meta changes the state to Stuck

  def split(s: State): List[State] = s match {
    case Ev(Call(fun, args), ρ, σ, φ, k) =>
      // fun is not defined, probably an unbound variable
      // in this case, evaluate the args in sequence (since we need to pass the store)
      // If there are no args, return Nil and let handle it.
      // In other cases we'd residualize the function and move on, but we
      // need to save the function name to rebuild the call
      args match {
        case Nil =>
          Nil
        case arg::args =>
          Ev(arg, ρ, σ, φ, EvalMoreArgsForResidual(fun, args, Nil, ρ)::Nil)::Nil
      }

    case Ev(NewCall(fun, args), ρ, σ, φ, k) =>
      // fun not defined, but eval the args
      args match {
        case Nil =>
          Nil
        case arg::args =>
          Ev(arg, ρ, σ, φ, EvalMoreArgsForNewResidual(fun, args, Nil, ρ)::Nil)::Nil
      }

    // We should only get stuck on an Ev state if the whistle blew.
    // We only handle the cases that can actually lead to nontermination.
    // In other cases we just advance to the next state and
    case Ev(While(label, test, body), ρ, σ, φ, k) =>
      // Simulate the loop, restricting the store more and more.
      Ev(test, ρ, σ, φ0, SeqCont(body, ρ)::Nil)::Nil

    case Ev(DoWhile(label, test, body), ρ, σ, φ, k) =>
      // Simulate the loop, restricting the store more and more.
      Ev(body, ρ, σ, φ0, SeqCont(test, ρ)::Nil)::Nil

    case Ev(For(label, Empty(), test, iter, body), ρ, σ, φ, k) =>
      // Simulate the loop, restricting the store more and more.
      Ev(test, ρ, σ, φ0, SeqCont(body, ρ)::SeqCont(iter, ρ)::Nil)::Nil

    case Co(v, σ, φ, BranchCont(kt, kf, ρ)::k) =>
      // If the result cannot be converted to a boolean, we residualize.
      // We split into two states, one which runs the true
      // branch and one which runs the false branch.
      // We also return a merger function that reconstructs the residual if
      // at (or after) the join point.

      // We have two options here.
      // - LONG_CONTINUATIONS.
      //   We run both continuations to the end of the program and then merge
      // - !LONG_CONTINUATIONS.
      //   We run both continuations to the join point, then merge
      // We choose the latter because it yields a smaller residual
      // program, although the former might result in better performance
      // because of the information loss after the join, despite
      // exponential code growth.

      if (LONG_CONTINUATIONS)
        splitBranch(v, ρ, σ, kt ++ k, kf ++ k)
      else
        splitBranch(v, ρ, σ, kt, kf)

    case Co(v, σ, φ, StartLoop(e, ρ1, σ1, φ1)::k) =>
      // We got stuck on the loop test (v). Just split the loop again, rerunning
      // from the start.
      // FIXME: this breaks the graph since the Ev config is never actually
      // part of the graph.
      split(Ev(e, ρ1, σ1, φ1, k))

    case s =>
      Nil
  }

  def splitBranch(test: Val, ρ: Env, σ: Store, kt: Cont, kf: Cont): List[State] = {
    val σ1 = Eval.extendWithCond(test, σ, ρ, true)
    val σ2 = Eval.extendWithCond(test, σ, ρ, false)
    List(Co(test, σ1, Machine.φ0, kt), Co(test, σ2, Machine.φ0, kf))
  }

  def findLandingPad(jump: Exp, k: Cont, acc: Cont = Nil): (Cont, Cont) = (jump, k) match {
    case (_: Return, (frame: CallFrame)::k) => (acc :+ frame, k)
    case (_: Throw, (frame: CatchFrame)::k) => (acc :+ frame, k)
    case (Break(Some(x)), (frame @ BreakFrame(Some(y)))::k) if x == y => (acc :+ frame, k)
    case (Continue(Some(x)), (frame @ ContinueFrame(Some(y)))::k) if x == y => (acc :+ frame, k)
    case (Break(None), (frame: BreakFrame)::k) => (acc :+ frame, k)
    case (Continue(None), (frame: ContinueFrame)::k) => (acc :+ frame, k)
    case (_, frame::k) => findLandingPad(jump, k, acc :+ frame)
    case (_, Nil) => (acc, Nil)
  }

  def mergeBranch(test: Exp, ρ0: Env, φ0: Effect)(ss: List[State], k: Cont): Option[(List[State], Cont)] = {
    (ss, k) match {
      ////////////////////////////////////////////////////////////////
      // Both Halt
      ////////////////////////////////////////////////////////////////

      // Both branches halted normally.
      // Merge the values and resume computation with k.
      case (List(Halt(v1, σ1, φ1), Halt(v2, σ2, φ2)), k) if v1 == v2 =>
        // If the values are the same, just use them.
        (φ1.seq, φ2.seq) match {
          case (Undefined(), Undefined()) =>
            // If the branches had no effects, we can just discard them.
            Some((List(Co(v1, σ1.merge(σ2, ρ0), φ0.extend(test), k)), Nil))
          case (s1, s2) =>
            val φ = φ0.extend(IfElse(test, s1, s2))
            Some((List(Co(v1, σ1.merge(σ2, ρ0), φ, k)), Nil))
        }

      case (List(Halt(v1, σ1, φ1), Halt(v2, σ2, φ2)), k) =>
        // Otherwise create a fresh residual variable
        // and then assign the values at the end of each branch.
        // cf. removing SSA.
        val x = FreshVar()
        val a1 = Assign(None, Residual(x), v1)
        val a2 = Assign(None, Residual(x), v2)

        val φ = φ0.extend(x, IfElse(test, φ1.seq(a1), φ2.seq(a2)))
        Some((List(Co(Residual(x), σ1.merge(σ2, ρ0), φ, k)), Nil))

      ////////////////////////////////////////////////////////////////
      // Both Unwinding
      ////////////////////////////////////////////////////////////////

      // Both branches halted abnormally.
      // We can try to merge the states and continue unwinding the stack.

      // exactly the same jump
      case (List(Unwinding(jump1, σ1, φ1, Nil), Unwinding(jump2, σ2, φ2, Nil)), k) if jump1 == jump2 =>
        (φ1.seq, φ2.seq) match {
          case (Undefined(), Undefined()) =>
            // If the branches had no effects, we can just dicard them.
            Some((List(Unwinding(jump1, σ1.merge(σ2, ρ0), φ0.extend(test), k)), Nil))
          case (s1, s2) =>
            val φ = φ0.extend(IfElse(test, s1, s2))
            Some((List(Unwinding(jump1, σ1.merge(σ2, ρ0), φ, k)), Nil))
        }

      case (List(Unwinding(Return(Some(v1)), σ1, φ1, Nil), Unwinding(Return(Some(v2)), σ2, φ2, Nil)), k) =>
        // merge two returns
        val x = FreshVar()
        val a1 = Assign(None, Residual(x), v1)
        val a2 = Assign(None, Residual(x), v2)
        val φ = φ0.extend(x, IfElse(test, φ1.seq(a1), φ2.seq(a2)))
        Some((List(Unwinding(Return(Some(Residual(x))), σ1.merge(σ2, ρ0), φ, k)), Nil))

      case (List(Unwinding(Throw(v1), σ1, φ1, Nil), Unwinding(Throw(v2), σ2, φ2, Nil)), k) =>
        // merge two throws
        val x = FreshVar()
        val a1 = Assign(None, Residual(x), v1)
        val a2 = Assign(None, Residual(x), v2)
        val φ = φ0.extend(x, IfElse(test, φ1.seq(a1), φ2.seq(a2)))
        Some((List(Unwinding(Throw(Residual(x)), σ1.merge(σ2, ρ0), φ, k)), Nil))

      case (List(Unwinding(jump1, σ1, φ1, Nil), Unwinding(jump2, σ2, φ2, Nil)), k) =>
        // cannot merge the jumps
        // Extend the continuations past the landing pad for the jumps
        val (kConsumed1, kRemaining1) = findLandingPad(jump1, k)
        val (kConsumed2, kRemaining2) = findLandingPad(jump2, k)
        val (kConsumed, kRemaining) = if (kConsumed1.length >= kConsumed2.length) (kConsumed1, kRemaining1) else (kConsumed2, kRemaining2)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, φ1, kConsumed), Unwinding(jump2, σ2, φ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Unwinding, one Halt
      ////////////////////////////////////////////////////////////////

      case (List(Unwinding(jump1, σ1, φ1, Nil), Halt(v2, σ2, φ2)), k) =>
        // one branch completed abnormally, the other normally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump1, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, φ1, kConsumed), Co(v2, σ2, φ2, kConsumed)), kRemaining))
        }

      case (List(Halt(v1, σ1, φ1), Unwinding(jump2, σ2, φ2, Nil)), k) =>
        // one branch completed normally, the other abnormally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump2, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Co(v1, σ1, φ1, kConsumed), Unwinding(jump2, σ2, φ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Unwinding, one Stuck
      ////////////////////////////////////////////////////////////////

      case (List(Unwinding(jump1, σ1, φ1, Nil), Co(v2, σ2, φ2, k2)), k) =>
        // one branch completed abnormally, the other is stuck.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump1, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, φ1, kConsumed), Co(v2, σ2, φ2, k2 ++ kConsumed)), kRemaining))
        }

      case (List(Co(v1, σ1, φ1, k1), Unwinding(jump2, σ2, φ2, Nil)), k) =>
        // one branch is stuck, the other completed abnormally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump2, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Co(v1, σ1, φ1, k1 ++ kConsumed), Unwinding(jump2, σ2, φ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Halt, one Stuck
      ////////////////////////////////////////////////////////////////

      case (List(Halt(v1, σ1, φ1), Co(v2, σ2, φ2, k2)), frame::k) =>
        // one branch completed abnormally, the other normally.
        // pull in a frame from after the merge point
        Some((List(Co(v1, σ1, φ1, frame::Nil), Co(v2, σ2, φ2, k2 :+ frame)), k))

      case (List(Co(v1, σ1, φ1, k1), Halt(v2, σ2, φ2)), frame::k) =>
        Some((List(Co(v1, σ1, φ1, k1 :+ frame), Co(v2, σ2, φ2, frame::Nil)), k))

      ////////////////////////////////////////////////////////////////
      // Both Stuck
      ////////////////////////////////////////////////////////////////

      case (List(Co(v1, σ1, φ1, k1), Co(v2, σ2, φ2, k2)), frame::k) =>
        Some((List(Co(v1, σ1, φ1, k1 :+ frame), Co(v2, σ2, φ2, k2 :+ frame)), k))

      // error
      case (states, k) => None
    }
  }

  // merges after a split.
  // in general we might return either a rebuilt state
  // or we return a state from which we can continue driving.
  def unsplit(root: State, children: List[List[State]]): Either[List[State], State] = root match {
    case Ev(Call(fun, Nil), ρ, σ, φ, k) =>
      println(s"UNSPLIT $root")
      rebuildEv(Call(fun, Nil), ρ, σ, φ, k) match { case Some(s) => Right(s) case _ => Left(Nil) }

    case Ev(Call(fun, args), ρ, σ, φ, k) =>
      println(s"UNSPLIT $root")
      children match {
        case hist::Nil =>
          println(s"UNSPLIT hist = $hist")
          val newCall = hist collectFirst {
            case Co(v, σ1, φ1, EvalMoreArgsForResidual(_, Nil, args, _)::Nil) =>
              rebuildEv(Call(fun, args :+ v), ρ, σ1, φ1, k)
          }
          println(s"UNSPLIT newCall = $newCall")
          newCall match {
            case Some(Some(s)) => Right(s)
            case _ => Left(Nil)
          }
        case _ => Left(Nil)
      }

    case Ev(NewCall(fun, Nil), ρ, σ, φ, k) =>
      rebuildEv(NewCall(fun, Nil), ρ, σ, φ, k) match { case Some(s) => Right(s) case _ => Left(Nil) }

    case Ev(NewCall(fun, args), ρ, σ, φ, k) =>
      children match {
        case hist::Nil =>
          val newCall = hist collectFirst {
            case Co(v, σ1, φ1, EvalMoreArgsForNewResidual(_, Nil, args, _)::Nil) =>
              rebuildEv(NewCall(fun, args :+ v), ρ, σ1, φ1, k)
          }
          newCall match {
            case Some(Some(s)) => Right(s)
            case _ => Left(Nil)
          }
        case _ => Left(Nil)
      }

    case Ev(While(label, test, body), ρ, σ, φ, k) =>
      children match {
        case (Stopped(v2, σ2, φ2)::hist)::Nil =>
          // For loops, we have to discard information from the store until we
          // hit a fixed point.
          if (σ2 == σ) {
            // Split ok
            val testState = hist.collectFirst {
              case (Co(v1, σ1, φ1, SeqCont(_, _)::Nil)) => Halt(v1, σ1, φ1)
              case (Ev(_, _, _, _, SeqCont(_, _)::Nil)) => Err("could not find test Co before Ev", root)
            }

            testState match {
              case Some(s1 @ Halt(v1, σ1, φ1)) =>
                if (φ1.seq(v1) == Undefined()) {
                  rebuildEv(While(label, v1, Halt(v2, σ2, φ2).residual), ρ, σ, φ, k) match { case Some(s) => Right(s) case None => Left(Nil) }
                }
                else {
                  // the test had side effects, just leave it in place entirely
                  // we should
                  rebuildEv(While(label, test, Halt(v2, σ2, φ2).residual), ρ, σ, φ, k) match { case Some(s) => Right(s) case None => Left(Nil) }
                }
              case _ =>
                // we couldn't find the test value.
                // this shouldn't happen, but just leave the test alone then
                rebuildEv(While(label, test, Halt(v2, σ2, φ2).residual), ρ, σ, φ, k) match { case Some(s) => Right(s) case None => Left(Nil) }
            }
          }
          else {
            // The store hasn't reached a fixed point yet.
            // Split again.
            // Termination argument: merging only makes the store less precise
            val σtop = σ.merge(σ2, ρ)
            Left(Ev(While(label, test, body), ρ, σtop, φ, k)::Nil)
          }
      }

    case Ev(DoWhile(label, body, test), ρ, σ, φ, k) =>
      children match {
        case (Stopped(v2, σ2, φ2)::hist)::Nil =>
          // For loops, we have to discard information from the store until we
          // hit a fixed point.
          if (σ2 == σ) {
            // Split ok
            val bodyState = hist.collectFirst {
              case (Co(v1, σ1, φ1, SeqCont(_, _)::Nil)) => Halt(v1, σ1, φ1)
              case (Ev(_, _, _, _, SeqCont(_, _)::Nil)) => Err("could not find test Co before Ev", root)
            }

            bodyState match {
              case Some(s1 @ Halt(v1, σ1, φ1)) =>
                rebuildEv(DoWhile(label, s1.residual, Halt(v2, σ2, φ2).residual), ρ, σ, φ, k) match { case Some(s) => Right(s) case None => Left(Nil) }
              case _ =>
                // we couldn't find the body value.
                // this shouldn't happen, but just leave the body alone then
                rebuildEv(DoWhile(label, body, Halt(v2, σ2, φ2).residual), ρ, σ, φ, k) match { case Some(s) => Right(s) case None => Left(Nil) }
            }
          }
          else {
            // The store hasn't reached a fixed point yet.
            // Split again.
            // Termination argument: merging only makes the store less precise
            val σtop = σ.merge(σ2, ρ)
            Left(Ev(DoWhile(label, body, test), ρ, σtop, φ, k)::Nil)
          }
      }

    case Ev(For(label, Empty(), test, iter, body), ρ, σ, φ, k) =>
      // TODO
      Left(Nil)

    case Co(v, σ, φ, BranchCont(kt, kf, ρ)::k) =>
      // If the result cannot be converted to a boolean, we residualize.
      // We split into two states, one which runs the true
      // branch and one which runs the false branch.
      // We also return a merger function that reconstructs the residual if
      // at (or after) the join point.

      // We have two options here.
      // - LONG_CONTINUATIONS.
      //   We run both continuations to the end of the program and then merge
      // - !LONG_CONTINUATIONS.
      //   We run both continuations to the join point, then merge
      // We choose the latter because it yields a smaller residual
      // program, although the former might result in better performance
      // because of the information loss after the join, despite
      // exponential code growth.

      val kont = {
        if (LONG_CONTINUATIONS)
          Nil
        else
          k
      }

      val inputs = children collect { case s::_ => s }

      mergeBranch(v, ρ, φ)(inputs, kont) match {
        case None => Left(Nil)
        case Some((s::Nil, Nil)) => Right(s) // success
        case Some((Nil, k)) => Left(Nil)  // failed
        case Some((ss, k)) =>
          // resplit but merge with a new continuation
          // should replace root configuration with: Co(v, σ, φ, BranchCont(kt, kf, ρ)::k)
          // g.rebuild(rootPos, Co(v, σ, φ, BranchCont(kt, kf, ρ)::k)).complete
          // should continue driving with ss
          // (inputs zip ss) map { (s0, s1) => g.focus(s0).addChild(s1, Extend) }

          // But we don't have the interface for that. Instead, just return a new Co and try to split again.
          Left(Co(v, σ, φ, BranchCont(kt, kf, ρ)::k)::Nil)
      }

    case _ =>
      Left(Nil)
  }

  // def rollback(s: St, hist: List[(Pos, St, Option[EdgeKind])]): Option[(Pos, St)] = s match {
  //   case Co(v, σ1, φ1, EvalMoreArgsForResidual(fun, Nil, args1, ρ)::Nil) =>
  //     // walk back up to the previous split
  //     hist.collectFirst {
  //       case (_, _, Some(SplitAt(Ev(Call(_, args), ρ, σ, φ, k), pos, 0, 1))) =>
  //         rebuildEv(Call(fun, args1 :+ v), ρ, σ1, φ1, k) map { s1 => (pos, s1) }
  //     }.get
  //   case Co(v, σ1, φ1, EvalMoreArgsForNewResidual(fun, Nil, args1, ρ)::Nil) =>
  //     // walk back up to the previous split
  //     hist.collectFirst {
  //       case (_, _, Some(SplitAt(Ev(NewCall(_, args), ρ, σ, φ, k), pos, 0, 1))) =>
  //         rebuildEv(Call(fun, args1 :+ v), ρ, σ1, φ1, k) map { s1 => (pos, s1) }
  //     }.get
  //   case _ =>
  //     None
  // }

  def findMatchingEv(hist: List[St])(s: State): Option[St] = s match {
    case Co(v, σ, φ, k) =>
      hist.find {
        case s1 @ Ev(e1, ρ1, σ1, φ1, k1) => k == k1
        case _ => false
      }
    case _ =>
      None
  }

  // Given a state and a history, replace one node in the history with a new node.
  def rollback(s: St, hist: List[St]): Option[St] = hist.headOption match {
    case Some(Ev(e, ρ, σ, φ, k)) =>
      rebuildEv(e, ρ, σ, φ, k)

    case Some(Co(v, σ, φ, k)) =>
      // Search the history for the Ev that led to here and replace it.
      findMatchingEv(hist)(s) match {
        case Some(st) =>
          k match {
            case DoAssign(op, lhs, ρ1)::k =>
              rebuildEv(Assign(op, lhs, v), ρ1, σ, φ, k)
            case DoIncDec(op, ρ1)::k =>
              rebuildEv(IncDec(op, v), ρ1, σ, φ, k)
            case DoTypeof(ρ1)::k =>
              rebuildEv(Typeof(v), ρ1, σ, φ, k)
            case DoUnaryOp(op, ρ1)::k =>
              rebuildEv(Unary(op, v), ρ1, σ, φ, k)
            case DoBinaryOp(op, v1, ρ1)::k =>
              rebuildEv(Binary(op, v1, v), ρ1, σ, φ, k)
            case EvalArgs(thisValue, Nil, ρ1)::k =>
              rebuildEv(Call(v, Nil), ρ1, σ, φ, k)
            case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
              rebuildEv(Call(fun, done :+ v), ρ1, σ, φ, k)
            case EvalMoreArgsForResidual(fun, Nil, done, ρ1)::k =>
              rebuildEv(Call(fun, done :+ v), ρ1, σ, φ, k)
            case EvalMoreArgsForNewResidual(fun, Nil, done, ρ1)::k =>
              rebuildEv(NewCall(fun, done :+ v), ρ1, σ, φ, k)
            case InitProto(fun, args, ρ1)::k =>
              rebuildEv(NewCall(fun, args), ρ1, σ, φ, k)
            case DoDeleteProperty(a, ρ1)::k =>
              rebuildEv(Delete(Index(a, v)), ρ1, σ, φ, k)
            case GetPropertyAddressOrCreate(a, ρ1)::k =>
              rebuildEv(Index(a, v), ρ1, σ, φ, k)
            case GetProperty(a, ρ1)::k =>
              rebuildEv(Index(a, v), ρ1, σ, φ, k)
            case k =>
              None
          }
        case None =>
          None
      }
    case _ =>
      None
  }

  // rebuild is called when we are in a state that cannot make a step

  def rebuildEv(e: Exp, ρ: Env, σ: Store, φ: Effect, k: Cont): Option[St] = {
    // TODO: if a variable used in e is in ρ, we have to generate an assignment to it.
    lazy val x = FreshVar()

    reify(e) match {
      // Don't residualize values
      case e: Val =>
        None

      // Statements evaluate to undefined, so don't generate a variable
      // for the value.
      // FIXME: we need to be able to residualize jumps.
      // This means we have to residualize the landing pads too (call, break, continue, catch frames)
      case e: Empty =>
        None

      // for if, just residualize the test
      // this will force a Stuck state.
      case IfElse(e, pass, fail) => Some {
        Ev(IfElse(Residual(x), pass, fail), ρ, Eval.simulateStore(e)(σ, ρ), φ.extend(x, e), k)
      }

      // for loops, just residualize the test
      case e: While => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      case e @ For(label, Empty(), test, Empty(), body) => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      case e: DoWhile => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      case e: For => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      case e: ForIn => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      case e: VarDef => Some {
        Co(Undefined(), Eval.simulateStore(e)(σ, ρ), φ.extend(e), k)
      }

      // Unwinding statements cannot be residualized.
      case e: Break =>
        None

      case e: Continue =>
        None

      case e @ Return(None) =>
        None

      // For return value and throw, residualize the value, but keep the jump.
      case Return(Some(e)) => Some {
        Ev(Return(Some(Residual(x))), ρ, Eval.simulateStore(e)(σ, ρ), φ.extend(x, e), k)
      }

      case Throw(e) => Some {
        Ev(Throw(Residual(x)), ρ, Eval.simulateStore(e)(σ, ρ), φ.extend(x, e), k)
      }

      case Seq(e1, e2) =>
        rebuildEv(e1, ρ, σ, φ, SeqCont(e2, ρ)::k)

      // Convert locals to residuals after manifesting the value.
      // TODO need to manifest the value.
      // This doesn't really work since a later expression
      // might assign x.
      // We should just be more careful with calls.
      // case e @ Local(x) =>
      //   Co(Residual(x), σ, φ, k)

      case e @ Assign(op, lhs, rhs) => Some {
        println(s"simulating $e")
        println(s"initial σ = $σ")
        println(s"  final σ = ${Eval.simulateStore(e)(σ, ρ)}")
        Co(Residual(x), Eval.simulateStore(e)(σ, ρ), φ.extend(x, lhs), k)
      }

      case e => Some {
        // TODO
        // if e might throw an exception, split and simulate the exception throw
        // f() k -->
        // (try x = f() catch (ex) { Throw(ex) } :: k
        println(s"simulating $e")
        println(s"initial σ = $σ")
        println(s"  final σ = ${Eval.simulateStore(e)(σ, ρ)}")
        val SIM_EXCEPTIONS = false
        if (SIM_EXCEPTIONS) {
          val y = FreshVar()
          TryCatch(Assign(None, Residual(x), e), Catch(y, None, Throw(Residual(y)))::Nil)
          Co(Residual(x), Eval.simulateStore(e)(σ, ρ), φ.extend(x, e), CatchFrame(Catch(y, None, Throw(Residual(y)))::Nil, ρ)::k)
        }
        else {
          Co(Residual(x), Eval.simulateStore(e)(σ, ρ), φ.extend(x, e), k)
        }
      }
    }
  }
}
