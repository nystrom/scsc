package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar
import scsc.core.Residualization._
import scsc.core.Unsplit._
import Machine._
import Continuations._
import States._


object EvSplit {

  import Split._

    trait EvSplit {
      self: Ev =>

      def split = e match {
            case Index(e1, e2) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::Rebuilt(v2, σ2, _)::_ =>
                    rebuildEv(Index(v1, v2), ρ, σ2, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Assign(op, Index(a, i), e2) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::Rebuilt(v2, σ2, _)::Rebuilt(v3, σ3, _)::_ =>
                    rebuildEv(Assign(op, Index(v1, v2), v3), ρ, σ3, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(a::i::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Assign(op, Local(x), e2) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::_ =>
                    rebuildEv(Assign(op, Local(x), v1), ρ, σ1, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Binary(op, e1, e2) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::Rebuilt(v2, σ2, _)::_ =>
                    rebuildEv(Binary(op, v1, v2), ρ, σ2, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Unary(op, e1) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::_ =>
                    rebuildEv(Unary(op, v1), ρ, σ1, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Typeof(e1) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::_ =>
                    rebuildEv(Typeof(v1), ρ, σ1, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Return(Some(e1)) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::_ =>
                    rebuildEv(Return(Some(v1)), ρ, σ1, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Throw(e1) =>
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                val u = unsplitArgs[Option[State]](children)(None) {
                  case Rebuilt(v1, σ1, _)::_ =>
                    rebuildEv(Throw(v1), ρ, σ1, k)
                }
                u match {
                  case Some(s) => UnsplitOk(s)
                  case None => UnsplitFail()
                }
              }

              splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

            case Call(fun, args) =>
              // fun is not defined, probably an unbound variable
              // in this case, evaluate the args in sequence (since we need to pass the store)
              // If there are no args, return Nil and let handle it.
              // In other cases we'd residualize the function and move on, but we
              // need to save the function name to rebuild the call
              args match {
                case Nil =>
                  None
                case arg::args =>
                  val split = Ev(arg, ρ, σ, EvalMoreArgsForResidual(fun, args, Nil, ρ)::Nil)

                  def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                    children match {
                      case hist::Nil =>
                        println(s"UNSPLIT hist = $hist")
                        val newCall = hist collectFirst {
                          case Co(v, σ1, EvalMoreArgsForResidual(_, Nil, args, _)::Nil) =>
                            rebuildEv(Call(fun, args :+ v), ρ, σ1, k)
                          case Rebuilt(e, σ1, EvalMoreArgsForResidual(_, Nil, args, _)::Nil) =>
                            rebuildEv(Call(fun, args :+ e), ρ, σ1, k)
                        }
                        println(s"UNSPLIT newCall = $newCall")
                        newCall match {
                          case Some(Some(s)) => UnsplitOk(s)
                          case _ => UnsplitFail()
                        }
                      case _ => UnsplitFail()
                    }
                  }

                  Some((split::Nil, unsplit _))
              }

            case NewCall(fun, args) =>
              // fun not defined, but eval the args
              args match {
                case Nil =>
                  None
                case arg::args =>
                  val split = Ev(arg, ρ, σ, EvalMoreArgsForNewResidual(fun, args, Nil, ρ)::Nil)

                  def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                    children match {
                      case hist::Nil =>
                        println(s"UNSPLIT hist = $hist")
                        val newCall = hist collectFirst {
                          case Co(v, σ1, EvalMoreArgsForNewResidual(_, Nil, args, _)::Nil) =>
                            rebuildEv(NewCall(fun, args :+ v), ρ, σ1, k)
                          case Rebuilt(e, σ1, EvalMoreArgsForNewResidual(_, Nil, args, _)::Nil) =>
                            rebuildEv(NewCall(fun, args :+ e), ρ, σ1, k)
                        }
                        println(s"UNSPLIT newCall = $newCall")
                        newCall match {
                          case Some(Some(s)) => UnsplitOk(s)
                          case _ => UnsplitFail()
                        }
                      case _ => UnsplitFail()
                    }
                  }

                  Some((split::Nil, unsplit _))
              }

            // We should only get stuck on an Ev state if the whistle blew.
            // We only handle the cases that can actually lead to nontermination.
            // In other cases we just advance to the next state and
            case While(label, test, body) =>
              // Simulate the loop, restricting the store more and more.
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                children match {
                  case (Stopped(v2, σ2)::hist)::Nil =>
                    // For loops, we have to discard information from the store until we
                    // hit a fixed point.
                    if (σ2 == σ) {
                      // Split ok
                      val testState = hist.collectFirst {
                        case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(v1, σ1, Nil)
                        case (Rebuilt(e1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(e1, σ1, Nil)
                      }

                      testState match {
                        case Some(s1 @ Rebuilt(e1, σ1, Nil)) =>
                          rebuildEv(While(label, e1, Rebuilt(v2, σ2, Nil).residual), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case _ =>
                          // we couldn't find the test value.
                          // this shouldn't happen, but just leave the test alone then
                          rebuildEv(While(label, test, Rebuilt(v2, σ2, Nil).residual), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                      }
                    }
                    else {
                      // The store hasn't reached a fixed point yet.
                      // Split again.
                      // Termination argument: merging only makes the store less precise
                      val σtop = σ.merge(σ2, ρ)
                      Resplit(Ev(While(label, test, body), ρ, σtop, k)::Nil, unsplit _)
                    }
                }
              }

              val split = Ev(test, ρ, σ, SeqCont(body, ρ)::Nil)
              Some((split::Nil, unsplit _))

            case DoWhile(label, test, body) =>
              // Simulate the loop, restricting the store more and more.
              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                children match {
                  case (Stopped(v2, σ2)::hist)::Nil =>
                    // For loops, we have to discard information from the store until we
                    // hit a fixed point.
                    if (σ2 == σ) {
                      // Split ok
                      val bodyState = hist.collectFirst {
                        case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(v1, σ1, Nil)
                        case (Rebuilt(e1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(e1, σ1, Nil)
                      }

                      bodyState match {
                        case Some(s1 @ Rebuilt(e1, σ1, Nil)) =>
                          rebuildEv(DoWhile(label, e1, Rebuilt(v2, σ2, Nil).residual), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case _ =>
                          // we couldn't find the body value.
                          // this shouldn't happen, but just leave the body alone
                          rebuildEv(DoWhile(label, body, Rebuilt(v2, σ2, Nil).residual), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                      }
                    }
                    else {
                      // The store hasn't reached a fixed point yet.
                      // Split again.
                      // Termination argument: merging only makes the store less precise
                      val σtop = σ.merge(σ2, ρ)
                      Resplit(Ev(DoWhile(label, body, test), ρ, σtop, k)::Nil, unsplit _)
                    }
                }
              }

              val split = Ev(body, ρ, σ, SeqCont(test, ρ)::Nil)
              Some((split::Nil, unsplit _))

            case For(label, Empty(), test, iter, body) =>
              // Simulate the loop, restricting the store more and more.

              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                children match {
                  case (Stopped(v2, σ2)::hist)::Nil =>
                    // For loops, we have to discard information from the store until we
                    // hit a fixed point.
                    if (σ2 == σ) {
                      // Split ok
                      val testState = hist.collectFirst {
                        case (Co(v1, σ1, SeqCont(body1, _)::SeqCont(_, _)::Nil)) if body1 == body => Rebuilt(v1, σ1, Nil)
                        case (Rebuilt(e1, σ1, SeqCont(body1, _)::SeqCont(_, _)::Nil)) if body1 == body => Rebuilt(e1, σ1, Nil)
                      }
                      val bodyState = hist.collectFirst {
                        case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(v1, σ1, Nil)
                        case (Rebuilt(e1, σ1, SeqCont(_, _)::Nil)) => Rebuilt(e1, σ1, Nil)
                      }
                      val iterState = Rebuilt(v2, σ2, Nil)

                      (testState, iterState, bodyState) match {
                        case (Some(Rebuilt(e1, σ1, Nil)), Rebuilt(e2, σ2, Nil), Some(Rebuilt(e3, σ3, Nil))) =>
                          rebuildEv(For(label, Empty(), e1, e2, e3), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case (_, Rebuilt(e2, σ2, Nil), Some(Rebuilt(e3, σ3, Nil))) =>
                          rebuildEv(For(label, Empty(), test, e2, e3), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case (Some(Rebuilt(e1, σ1, Nil)), Rebuilt(e2, σ2, Nil), _) =>
                          rebuildEv(For(label, Empty(), e1, e2, body), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case (_, Rebuilt(e2, σ2, Nil), _) =>
                          rebuildEv(For(label, Empty(), test, e2, body), ρ, σ, k) match {
                            case Some(s) => UnsplitOk(s)
                            case None => UnsplitFail()
                          }
                        case _ =>
                          UnsplitFail()
                      }
                    }
                    else {
                      // The store hasn't reached a fixed point yet.
                      // Split again.
                      // Termination argument: merging only makes the store less precise
                      val σtop = σ.merge(σ2, ρ)
                      Resplit(Ev(For(label, Empty(), test, iter, body), ρ, σtop, k)::Nil, unsplit _)
                    }
                }
              }

              val split = Ev(test, ρ, σ, SeqCont(body, ρ)::SeqCont(iter, ρ)::Nil)
              Some((split::Nil, unsplit _))

            case _ =>
              None
      }
    }

}

object CoSplit {
  import Split._

  def splitBranchCont(isCond: Boolean, test: Exp, ρ: Env, σ: Store, kt: Cont, kf: Cont, k: Cont) = {
    def unsplit(k: Cont)(children: List[List[State]]): UnsplitResult[State] = {
      val kont = {
        if (LONG_CONTINUATIONS)
          Nil
        else
          k
      }

      val inputs = children collect { case s::_ => s }

      mergeBranch(test, ρ, isCond)(inputs, kont) match {
        case None => UnsplitFail()
        case Some((s::Nil, Nil)) => UnsplitOk(s)
        case Some((Nil, k)) => UnsplitFail()
        case Some((ss, k)) =>
          // Return a new Co and try to split again.
          if (isCond) {
            Resplit(Rebuilt(test, σ, CondBranchCont(kt, kf, ρ)::k)::Nil, unsplit(k) _)
          }
          else {
            Resplit(Rebuilt(test, σ, BranchCont(kt, kf, ρ)::k)::Nil, unsplit(k) _)
          }
      }
    }

    val splits = {
      if (LONG_CONTINUATIONS)
        splitBranch(test, ρ, σ, kt ++ k, kf ++ k)
      else
        splitBranch(test, ρ, σ, kt, kf)
    }

    Some((splits, unsplit(k) _))

  }

    trait CoSplit {
      self: Co =>

      def split = k match {

            case BranchCont(kt, kf, ρ)::k =>
              splitBranchCont(false, v, ρ, σ, kt, kf, k)

            case CondBranchCont(kt, kf, ρ)::k =>
              splitBranchCont(true, v, ρ, σ, kt, kf, k)

            case StartLoop(e, ρ1, σ1)::k =>
              // We got stuck on the loop test (v).
              // Split the loop.
              // If the split fails, we'll end up rebuilding
              // the Ev, then splitting again.
              Ev(e, ρ1, σ1, k).split

            // In general, recreate the term and split it.
            // If the split fails, we'll end up rebuilding the term
            case DoAssign(op, lhs, ρ1)::k =>
              Ev(Assign(op, lhs, v), ρ1, σ, k).split

            case DoIncDec(op, ρ1)::k =>
              Ev(IncDec(op, v), ρ1, σ, k).split

            case DoTypeof(ρ1)::k =>
              Ev(Typeof(v), ρ1, σ, k).split

            case DoUnaryOp(op, ρ1)::k =>
              Ev(Unary(op, v), ρ1, σ, k).split

            case DoBinaryOp(op, v1, ρ1)::k =>
              Ev(Binary(op, v1, v), ρ1, σ, k).split

            case EvalArgs(thisValue, Nil, ρ1)::k =>
              Ev(Call(v, Nil), ρ1, σ, k).split

            case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
              Ev(Call(fun, done :+ v), ρ1, σ, k).split

            case EvalMoreArgsForResidual(fun, Nil, done, ρ1)::k =>
              Ev(Call(fun, done :+ v), ρ1, σ, k).split

            case EvalMoreArgsForNewResidual(fun, Nil, done, ρ1)::k =>
              Ev(NewCall(fun, done :+ v), ρ1, σ, k).split

            case InitProto(fun, args, ρ1)::k =>
              Ev(NewCall(fun, args), ρ1, σ, k).split

            case DoDeleteProperty(a, ρ1)::k =>
              Ev(Delete(Index(a, v)), ρ1, σ, k).split

            case GetPropertyAddressOrCreate(a, ρ1)::k =>
              Ev(Index(a, v), ρ1, σ, k).split

            case GetProperty(a, ρ1)::k =>
              Ev(Index(a, v), ρ1, σ, k).split

            case k =>
              None
          }

    }

}

object UnwindingSplit {
  import Split._

  trait UnwindingSplit {
    self: Unwinding =>

    def split = None

  }
}

object RebuiltSplit {
  import Split._
  import CoSplit._

    trait RebuiltSplit {
      self: Rebuilt =>

      def split = k match {
            case BranchCont(kt, kf, ρ)::k =>
              splitBranchCont(false, residual, ρ, σ, kt, kf, k)

            case CondBranchCont(kt, kf, ρ)::k =>
              splitBranchCont(true, residual, ρ, σ, kt, kf, k)

            // In general we should not split a rebuild
            // since if it fails we'll end up rebuilding and resplitting.
            case k =>
              None

          }

    }

}


// This object defines the interpreter states and implements the step function
// for the JS interpreter.
object Split {
  val LONG_CONTINUATIONS = false
  type Merger = (List[State], Cont) => Option[(List[State], Cont)]

  // Split returns:
  // - a list of starting states with a possibly truncated continuation
  // - a function to merge split histories back into a new state from which
  //   (hopefully) evaluation can resume
  //   Unsplit should return a new state with the same continuation as the state
  //   we're splitting.

  def splitArgs(args: List[Exp], ρ: Env, σ: Store): Option[State] = {
    args match {
      case Nil => None
      case arg::Nil =>
        Some(Ev(arg, ρ, σ, Nil))
      case arg1::arg2::args =>
        val seq = args.foldLeft(arg2)(Seq)
        Some(Ev(arg1, ρ, σ, SeqCont(seq, ρ)::Nil))
    }
  }

  def unsplitArgs[A](children: List[List[State]])(fail: => A)(body: PartialFunction[List[State], A]): A = {
    children match {
      case hist::Nil =>
        hist match {
          case last::hist =>
            val ss = hist collect {
              case Co(v, σ1, SeqCont(_, _)::Nil) => Rebuilt(v, σ1, Nil)
              case Rebuilt(e, σ1, SeqCont(_, _)::Nil) => Rebuilt(e, σ1, Nil)
            }

            val s = List(last) collect {
              case Co(v, σ1, Nil) => Rebuilt(v, σ1, Nil)
              case Rebuilt(e, σ1, Nil) => Rebuilt(e, σ1, Nil)
            }

            val result = (s ++ ss).reverse

            if (body.isDefinedAt(result)) {
              body(result)
            }
            else {
              fail
            }
          case _ => fail
        }
      case _ => fail
    }
  }

  def splitBranch(test: Exp, ρ: Env, σ: Store, kt: Cont, kf: Cont): List[State] = {
    val σ1 = Eval.extendWithCond(test, σ, ρ, true)
    val σ2 = Eval.extendWithCond(test, σ, ρ, false)
    List(Co(Undefined(), σ1, kt), Co(Undefined(), σ2, kf))
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

  def mergeBranch(test: Exp, ρ0: Env, isCond: Boolean = false)(ss: List[State], k: Cont): Option[(List[State], Cont)] = {
    (ss, k) match {
      // To reconstruct the branch, compare the resulting states from the two branches.
      // If we can reconcile, reconstruct the if or cond. We MUST residualize the test here.
      // And return Nil for the continuation.
      // If we cannot reconcile, return 2 states which will continue the split,
      // pulling in more of the continuation. We should return the continuation not
      // consumed by the resplit.

      ////////////////////////////////////////////////////////////////
      // Both Rebuilt
      ////////////////////////////////////////////////////////////////

      // Both branches halted normally.
      // Merge the values and resume computation with k.
      case (List(Rebuilt(v1: Val, σ1, Nil), Rebuilt(v2: Val, σ2, Nil)), k) if v1 == v2 =>
        // If the values are the same, just use them.
        // And resume...
        Some((List(Co(v1, σ1.merge(σ2, ρ0), k)), Nil))

      case (List(Rebuilt(e1, σ1, Nil), Rebuilt(e2, σ2, Nil)), k) =>
        if (isCond) {
          Some((List(Rebuilt(Cond(test, e1, e2), σ1.merge(σ2, ρ0), k)), Nil))
        }
        else {
          Some((List(Rebuilt(IfElse(test, e1, e2), σ1.merge(σ2, ρ0), k)), Nil))
        }

      ////////////////////////////////////////////////////////////////
      // Both Unwinding
      ////////////////////////////////////////////////////////////////

      // Both branches halted abnormally.
      // We can try to merge the states and continue unwinding the stack.

      case (List(Unwinding(jump1, σ1, Nil), Unwinding(jump2, σ2, Nil)), k) if jump1 == jump2 =>
        // If the branches had no effects, we can just discard them.
        Some((List(Unwinding(jump1, σ1.merge(σ2, ρ0), k)), Nil))

      case (List(Unwinding(Return(Some(v1)), σ1, Nil), Unwinding(Return(Some(v2)), σ2, Nil)), k) =>
        // merge two returns
        // if (x) ... return 1 ... else return 2
        // ->
        // return x ? 1 : 2
        Some((List(Rebuilt(Return(Some(Cond(test, v1, v2))), σ1.merge(σ2, ρ0), k)), Nil))

      case (List(Unwinding(Throw(v1), σ1, Nil), Unwinding(Throw(v2), σ2, Nil)), k) =>
        // merge two throws
        Some((List(Rebuilt(Throw(Cond(test, v1, v2)), σ1.merge(σ2, ρ0), k)), Nil))

      case (List(Unwinding(jump1, σ1, Nil), Unwinding(jump2, σ2, Nil)), k) =>
        // cannot merge the jumps
        // Extend the continuations past the next possible landing pad for both jumps
        // Find the two landing pads and pick the one farthest out.
        val (kConsumed1, kRemaining1) = findLandingPad(jump1, k)
        val (kConsumed2, kRemaining2) = findLandingPad(jump2, k)
        val (kConsumed, kRemaining) = if (kConsumed1.length >= kConsumed2.length) (kConsumed1, kRemaining1) else (kConsumed2, kRemaining2)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, kConsumed), Unwinding(jump2, σ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Unwinding, one Halt
      ////////////////////////////////////////////////////////////////

      case (List(Unwinding(jump1, σ1, Nil), Rebuilt(v2: Val, σ2, Nil)), k) =>
        // one branch completed abnormally, the other normally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump1, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, kConsumed), Co(v2, σ2, kConsumed)), kRemaining))
        }

      case (List(Rebuilt(v1: Val, σ1, Nil), Unwinding(jump2, σ2, Nil)), k) =>
        // one branch completed normally, the other abnormally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump2, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Co(v1, σ1, kConsumed), Unwinding(jump2, σ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Unwinding, one Stuck
      ////////////////////////////////////////////////////////////////

      case (List(Unwinding(jump1, σ1, Nil), Co(v2, σ2, k2)), k) =>
        // one branch completed abnormally, the other is stuck.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump1, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, kConsumed), Co(v2, σ2, k2 ++ kConsumed)), kRemaining))
        }

      case (List(Co(v1, σ1, k1), Unwinding(jump2, σ2, Nil)), k) =>
        // one branch is stuck, the other completed abnormally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump2, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Co(v1, σ1, k1 ++ kConsumed), Unwinding(jump2, σ2, kConsumed)), kRemaining))
        }

      ////////////////////////////////////////////////////////////////
      // One Halt, one Stuck
      ////////////////////////////////////////////////////////////////

      case (List(Rebuilt(v1: Val, σ1, k1), Co(v2, σ2, k2)), frame::k) =>
        // one branch completed abnormally, the other normally.
        // pull in a frame from after the merge point
        Some((List(Co(v1, σ1, frame::k1), Co(v2, σ2, k2 :+ frame)), k))

      case (List(Co(v1, σ1, k1), Rebuilt(v2: Val, σ2, k2)), frame::k) =>
        Some((List(Co(v1, σ1, k1 :+ frame), Co(v2, σ2, frame::k2)), k))

      ////////////////////////////////////////////////////////////////
      // Both Stuck (probably the whistle blew)
      ////////////////////////////////////////////////////////////////

      case (List(s1, s2), frame::k) =>
        def extendCont(s: State, frame: ContFrame) = s match {
          case Co(v1, σ1, k1) => Co(v1, σ1, k1 :+ frame)
          case Unwinding(jump1, σ1, k1) => Unwinding(jump1, σ1, k1 :+ frame)
          case Ev(e1, ρ1, σ1, k1) => Ev(e1, ρ1, σ1, k1 :+ frame)
          case Rebuilt(e1, σ1, k1) => Rebuilt(e1, σ1, k1 :+ frame)
        }
        // Extend the continuations to see if they get unstuck
        Some((List(extendCont(s1, frame), extendCont(s2, frame)), k))

      // error
      case (states, k) => None
    }
  }

  // def rollback(s: St, hist: List[(Pos, St, Option[EdgeKind])]): Option[(Pos, St)] = s match {
  //   case Co(v, σ1, EvalMoreArgsForResidual(fun, Nil, args1, ρ)::Nil) =>
  //     // walk back up to the previous split
  //     hist.collectFirst {
  //       case (_, _, Some(SplitAt(Ev(Call(_, args), ρ, σ, k), pos, 0, 1))) =>
  //         rebuildEv(Call(fun, args1 :+ v), ρ, σ1, k) map { s1 => (pos, s1) }
  //     }.get
  //   case Co(v, σ1, EvalMoreArgsForNewResidual(fun, Nil, args1, ρ)::Nil) =>
  //     // walk back up to the previous split
  //     hist.collectFirst {
  //       case (_, _, Some(SplitAt(Ev(NewCall(_, args), ρ, σ, k), pos, 0, 1))) =>
  //         rebuildEv(Call(fun, args1 :+ v), ρ, σ1, k) map { s1 => (pos, s1) }
  //     }.get
  //   case _ =>
  //     None
  // }

  // Search for the first Ev that matches the given Co
  // Returns (_, Nil) if not found
  def findMatchingEv(hist: List[St])(k: Cont): (List[St], List[St]) = hist match {
    case Nil => (Nil, Nil)
    case s1::rest =>
      s1 match {
        case Ev(e1, ρ1, σ1, k1) if k == k1 =>
          (Nil, s1::rest)
        case _ =>
          findMatchingEv(rest)(k) match {
            case (before, after) => (before :+ s1, after)
          }
      }
  }

  val SIMPLE_REBUILD = true

  // Rollback converts an active state to a rebuild, if possible.
  // Given a state and a history, replace the entire history.
  // This isn't really necessary... splitting should handle these cases.
  // I don't think this will ever run.
  def rollback(hist: List[St]): Option[List[St]] = hist match {
    case Ev(e, ρ, σ, k)::tail =>
      rebuildEv(e, ρ, σ, k) map { _::tail }

    case (s @ Co(v, σ, frame::k))::tail if SIMPLE_REBUILD =>
      Some(Rebuilt(reify(v), σ, k)) map { _::tail }

    case (s @ Co(v, σ, frame::k))::hist =>
      // We're about to pop the frame and continue with k.
      // Find the Ev that pushed the offending frame
      // and replace it with a rewritten expression.
      findMatchingEv(hist)(k) match {
        case (below, ev::above) =>
          val newState = frame match {
            case DoAssign(op, lhs, ρ1) =>
              rebuildEv(Assign(op, lhs, v), ρ1, σ, k)
            case DoIncDec(op, ρ1) =>
              rebuildEv(IncDec(op, v), ρ1, σ, k)
            case DoTypeof(ρ1) =>
              rebuildEv(Typeof(v), ρ1, σ, k)
            case DoUnaryOp(op, ρ1) =>
              rebuildEv(Unary(op, v), ρ1, σ, k)
            case DoBinaryOp(op, v1, ρ1) =>
              rebuildEv(Binary(op, v1, v), ρ1, σ, k)
            case EvalArgs(thisValue, Nil, ρ1) =>
              rebuildEv(Call(v, Nil), ρ1, σ, k)
            case EvalMoreArgs(fun, thisValue, Nil, done, ρ1) =>
              rebuildEv(Call(fun, done :+ v), ρ1, σ, k)
            case EvalMoreArgsForResidual(fun, Nil, done, ρ1) =>
              rebuildEv(Call(fun, done :+ v), ρ1, σ, k)
            case EvalMoreArgsForNewResidual(fun, Nil, done, ρ1) =>
              rebuildEv(NewCall(fun, done :+ v), ρ1, σ, k)
            case InitProto(fun, args, ρ1) =>
              rebuildEv(NewCall(fun, args), ρ1, σ, k)
            case DoDeleteProperty(a, ρ1) =>
              rebuildEv(Delete(Index(a, v)), ρ1, σ, k)
            case GetPropertyAddressOrCreate(a, ρ1) =>
              rebuildEv(Index(a, v), ρ1, σ, k)
            case GetProperty(a, ρ1) =>
              rebuildEv(Index(a, v), ρ1, σ, k)
            case frame =>
              // just convert to a rebuilt and run until the continuation
              // drains
              None
          }

          newState map { _::above }
        case _ =>
          None
      }
    case _ =>
      None
  }

  // rebuild is called when we are in a state from which cannot make a step

  def rebuildEv(e: Exp, ρ: Env, σ: Store, k: Cont): Option[St] = {
    // TODO: if a variable used in e is in ρ, we have to generate an assignment to it.
    lazy val x = FreshVar()

    reify(e) match {
      // Don't residualize values
      case v: Val => Some {
        Co(v, σ, k)
      }

      // Statements evaluate to undefined, so don't generate a variable
      // for the value.
      // FIXME: we need to be able to residualize jumps.
      // This means we have to residualize the landing pads too (call, break, continue, catch frames)
      case e: Empty => Some {
        Co(Undefined(), σ, k)
      }

      case e @ For(label, Empty(), test, Empty(), body) => Some {
        Rebuilt(While(label, test, body), Eval.simulateStore(e)(σ, ρ), k)
      }

      case e => Some {
        // TODO
        // if e might throw an exception, split and simulate the exception throw
        // f() k -->
        // (try x = f() catch (ex) { Throw(ex) } :: k
        println(s"simulating $e")
        println(s"initial σ = $σ")
        println(s"  final σ = ${Eval.simulateStore(e)(σ, ρ)}")
        Rebuilt(e, Eval.simulateStore(e)(σ, ρ), k)
      }
    }
  }
}
