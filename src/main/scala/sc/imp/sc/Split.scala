package sc.imp.sc

import sc.core.sc.Unsplit._

class Split[M <: Machine](val machine: M) {
  import machine._
  import terms._
  import states._
  import continuations._
  import envs._
  import stores._
  import states.Rollback._

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
              case Co(v, σ1, SeqCont(_, _)::Nil) => Re(v, σ1, Nil)
              case Re(e, σ1, SeqCont(_, _)::Nil) => Re(e, σ1, Nil)
            }

            val s = List(last) collect {
              case Co(v, σ1, Nil) => Re(v, σ1, Nil)
              case Re(e, σ1, Nil) => Re(e, σ1, Nil)
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

  def splitBranch(test: Exp, ρ: Env, σ: Store, pass: Exp, fail: Exp, k: Cont): List[State] = {
    val σ1 = stores.extendWithCond(test, σ, ρ, true)
    val σ2 = stores.extendWithCond(test, σ, ρ, false)
    List(Ev(pass, ρ, σ1, k), Ev(fail, ρ, σ2, k))
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
      // Both Re
      ////////////////////////////////////////////////////////////////

      // Both branches halted normally with the same residual expression.
      // Merge the values and resume computation with k.
      case (List(Re(e1, σ1, Nil), Re(e2, σ2, Nil)), k) if e1 == e2 =>
        val σ = σ1.merge(σ2)
        e1 match {
          case v: Value =>
            // if the branches ended with a value, just resume with the value
            // PROBLEM: if the branches changed the store in incompatible ways
            // we need to residualize the different effects
            Some((List(Co(v, σ, k)), Nil))
          case e =>
            Some((List(Re(e, σ, k)), Nil))
        }

      case (List(Re(e1, σ1, Nil), Re(e2, σ2, Nil)), k) =>
        if (isCond) {
          Some((List(Re(Cond(test, e1, e2), σ1.merge(σ2), k)), Nil))
        }
        else {
          Some((List(Re(IfElse(test, e1, e2), σ1.merge(σ2), k)), Nil))
        }
/*
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
        Some((List(Re(Return(Some(Cond(test, v1, v2))), σ1.merge(σ2, ρ0), k)), Nil))

      case (List(Unwinding(Throw(v1), σ1, Nil), Unwinding(Throw(v2), σ2, Nil)), k) =>
        // merge two throws
        Some((List(Re(Throw(Cond(test, v1, v2)), σ1.merge(σ2, ρ0), k)), Nil))

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

      case (List(Unwinding(jump1, σ1, Nil), Re(v2: Value, σ2, Nil)), k) =>
        // one branch completed abnormally, the other normally.
        // Extend the continuations past the landing pad for the jump
        val (kConsumed, kRemaining) = findLandingPad(jump1, k)
        kConsumed match {
          case Nil => None
          case _ =>
            Some((List(Unwinding(jump1, σ1, kConsumed), Co(v2, σ2, kConsumed)), kRemaining))
        }

      case (List(Re(v1: Value, σ1, Nil), Unwinding(jump2, σ2, Nil)), k) =>
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

      case (List(Re(v1: Value, σ1, k1), Co(v2, σ2, k2)), frame::k) =>
        // one branch completed abnormally, the other normally.
        // pull in a frame from after the merge point
        Some((List(Co(v1, σ1, frame::k1), Co(v2, σ2, k2 :+ frame)), k))

      case (List(Co(v1, σ1, k1), Re(v2: Value, σ2, k2)), frame::k) =>
        Some((List(Co(v1, σ1, k1 :+ frame), Co(v2, σ2, frame::k2)), k))

      ////////////////////////////////////////////////////////////////
      // Both Stuck (probably the whistle blew)
      ////////////////////////////////////////////////////////////////

      case (List(s1, s2), frame::k) =>
        def extendCont(s: State, frame: ContFrame) = s match {
          case Co(v1, σ1, k1) => Co(v1, σ1, k1 :+ frame)
          case Unwinding(jump1, σ1, k1) => Unwinding(jump1, σ1, k1 :+ frame)
          case Ev(e1, ρ1, σ1, k1) => Ev(e1, ρ1, σ1, k1 :+ frame)
          case Re(e1, σ1, k1) => Re(e1, σ1, k1 :+ frame)
        }
        // Extend the continuations to see if they get unstuck
        Some((List(extendCont(s1, frame), extendCont(s2, frame)), k))
*/
      // error
      case (states, k) => None
    }
  }

  // Search for the first Ev that matches the given Co
  // Returns (_, Nil) if not found
  def findMatchingEv(hist: List[State])(k: Cont): (List[State], List[State]) = hist match {
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
}

class EvSplit[M <: Machine](m: M) extends Split[M](m) {
  import machine._
  import terms._
  import states._
  import continuations._
  import envs._
  import stores._
  import states.Rollback._

  def split(s: Ev): Option[(List[State], Unsplitter[State])] = s match {
    case Ev(e, ρ, σ, k) =>
      e match {
        case Index(e1, e2) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::Re(v2, σ2, Nil)::_ =>
                UnsplitOk(rebuildEv(Index(v1, v2), ρ, σ2, k))
            }
          }

          splitArgs(e1::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Assign(op, Index(a, i), e2) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::Re(v2, σ2, _)::Re(v3, σ3, _)::_ =>
                UnsplitOk(rebuildEv(Assign(op, Index(v1, v2), v3), ρ, σ3, k))
            }
          }

          splitArgs(a::i::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Assign(op, Local(x), e2) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::_ =>
                UnsplitOk(rebuildEv(Assign(op, Local(x), v1), ρ, σ1, k))
            }
          }

          splitArgs(e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Binary(op, e1, e2) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::Re(v2, σ2, Nil)::_ =>
                UnsplitOk(rebuildEv(Binary(op, v1, v2), ρ, σ2, k))
            }
          }

          splitArgs(e1::e2::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Unary(op, e1) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::_ =>
                UnsplitOk(rebuildEv(Unary(op, v1), ρ, σ1, k))
            }
          }

          splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Return(Some(e1)) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::_ =>
                UnsplitOk(rebuildEv(Return(Some(v1)), ρ, σ1, k))
            }
          }

          splitArgs(e1::Nil, ρ, σ) map { s => (s::Nil, unsplit _) }

        case Throw(e1) =>
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
              case Re(v1, σ1, Nil)::_ =>
                UnsplitOk(rebuildEv(Throw(v1), ρ, σ1, k))
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
              val split = splitArgs(arg::args, ρ, σ)

              def unsplit(children: List[List[State]]): UnsplitResult[State] = {
                def collect(n: Int) = new {
                  def unapply(ss: List[State]): Option[(List[Exp], Store)] = {
                    val values = ss collect {
                      case Re(e, _, Nil) => e
                    }
                    if (values.length == n)
                      Some((values, ss.last.asInstanceOf[Re].σ))
                    else
                      None
                  }
                }
                val pat = collect(args.length)
                unsplitArgs[UnsplitResult[State]](children)(UnsplitFail()) {
                  case pat(values, σ1) =>
                    UnsplitOk(rebuildEv(Call(fun, values), ρ, σ1, k))
                }
              }

              Some((split.toList, unsplit _))
          }

        // We should only get stuck on an Ev state if the whistle blew.
        // We only handle the cases that can actually lead to nontermination.
        // In other cases we just advance to the next state and
        case While(label, test, body) =>
          // Simulate the loop, restricting the store more and more.
          def unsplit(children: List[List[State]]): UnsplitResult[State] = {
            children match {
              case (Re(v2, σ2, Nil)::hist)::Nil =>
                // For loops, we have to discard information from the store until we
                // hit a fixed point.
                if (σ2 == σ) {
                  // Split ok
                  val testState = hist.collectFirst {
                    case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Re(v1, σ1, Nil)
                    case (Re(e1, σ1, SeqCont(_, _)::Nil)) => Re(e1, σ1, Nil)
                  }

                  testState match {
                    case Some(s1 @ Re(e1, σ1, Nil)) =>
                      val s = rebuildEv(While(label, e1, Re(v2, σ2, Nil).residual), ρ, σ, k)
                      UnsplitOk(s)
                    case _ =>
                      // we couldn't find the test value.
                      // this shouldn't happen, but just leave the test alone then
                      val s = rebuildEv(While(label, test, Re(v2, σ2, Nil).residual), ρ, σ, k)
                      UnsplitOk(s)
                  }
                }
                else {
                  // The store hasn't reached a fixed point yet.
                  // Split again.
                  // Termination argument: merging only makes the store less precise
                  val σtop = σ.merge(σ2)
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
              case (Re(v2, σ2, Nil)::hist)::Nil =>
                // For loops, we have to discard information from the store until we
                // hit a fixed point.
                if (σ2 == σ) {
                  // Split ok
                  val bodyState = hist.collectFirst {
                    case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Re(v1, σ1, Nil)
                    case (Re(e1, σ1, SeqCont(_, _)::Nil)) => Re(e1, σ1, Nil)
                  }

                  bodyState match {
                    case Some(s1 @ Re(e1, σ1, Nil)) =>
                      val s = rebuildEv(DoWhile(label, e1, Re(v2, σ2, Nil).residual), ρ, σ, k)
                      UnsplitOk(s)
                    case _ =>
                      // we couldn't find the body value.
                      // this shouldn't happen, but just leave the body alone
                      val s = rebuildEv(DoWhile(label, body, Re(v2, σ2, Nil).residual), ρ, σ, k)
                      UnsplitOk(s)
                  }
                }
                else {
                  // The store hasn't reached a fixed point yet.
                  // Split again.
                  // Termination argument: merging only makes the store less precise
                  val σtop = σ.merge(σ2)
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
              case (Re(v2, σ2, Nil)::hist)::Nil =>
                // For loops, we have to discard information from the store until we
                // hit a fixed point.
                if (σ2 == σ) {
                  // Split ok
                  val testState = hist.collectFirst {
                    case (Co(v1, σ1, SeqCont(body1, _)::SeqCont(_, _)::Nil)) if body1 == body => Re(v1, σ1, Nil)
                    case (Re(e1, σ1, SeqCont(body1, _)::SeqCont(_, _)::Nil)) if body1 == body => Re(e1, σ1, Nil)
                  }
                  val bodyState = hist.collectFirst {
                    case (Co(v1, σ1, SeqCont(_, _)::Nil)) => Re(v1, σ1, Nil)
                    case (Re(e1, σ1, SeqCont(_, _)::Nil)) => Re(e1, σ1, Nil)
                  }
                  val iterState = Re(v2, σ2, Nil)

                  (testState, iterState, bodyState) match {
                    case (Some(Re(e1, σ1, Nil)), Re(e2, σ2, Nil), Some(Re(e3, σ3, Nil))) =>
                      val s = rebuildEv(For(label, Empty(), e1, e2, e3), ρ, σ, k)
                      UnsplitOk(s)
                    case (_, Re(e2, σ2, Nil), Some(Re(e3, σ3, Nil))) =>
                      val s = rebuildEv(For(label, Empty(), test, e2, e3), ρ, σ, k)
                      UnsplitOk(s)
                    case (Some(Re(e1, σ1, Nil)), Re(e2, σ2, Nil), _) =>
                      val s = rebuildEv(For(label, Empty(), e1, e2, body), ρ, σ, k)
                      UnsplitOk(s)
                    case (_, Re(e2, σ2, Nil), _) =>
                      val s = rebuildEv(For(label, Empty(), test, e2, body), ρ, σ, k)
                      UnsplitOk(s)
                    case _ =>
                      UnsplitFail()
                  }
                }
                else {
                  // The store hasn't reached a fixed point yet.
                  // Split again.
                  // Termination argument: merging only makes the store less precise
                  val σtop = σ.merge(σ2)
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

class CoSplit[M <: Machine](m: M) extends Split[M](m) {
  import machine._
  import terms._
  import states._
  import continuations._
  import envs._
  import stores._

  def splitBranchCont(isCond: Boolean, test: Exp, ρ: Env, σ: Store, e1: Exp, e2: Exp, k: Cont) = {
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
            Resplit(Re(test, σ, CondBranchCont(e1, e2, ρ)::k)::Nil, unsplit(k) _)
          }
          else {
            Resplit(Re(test, σ, BranchCont(e1, e2, ρ)::k)::Nil, unsplit(k) _)
          }
      }
    }

    val splits = {
      if (LONG_CONTINUATIONS)
        splitBranch(test, ρ, σ, e1, e2, k)
      else
        splitBranch(test, ρ, σ, e1, e2, Nil)
    }

    Some((splits, unsplit(k) _))
  }

  def split(s: Co): Option[(List[State], Unsplitter[State])] = s match {
    case Co(v, σ, k) =>
      k match {
        case BranchCont(e1, e2, ρ)::k =>
          splitBranchCont(false, v, ρ, σ, e1, e2, k)

        case CondBranchCont(e1, e2, ρ)::k =>
          splitBranchCont(true, v, ρ, σ, e1, e2, k)

        case StartLoop(e, ρ1, σ1)::k =>
          // We got stuck on the loop test (v).
          // Split the loop.
          // If the split fails, we'll end up rebuilding
          // the Ev, then splitting again.
          states.split(Ev(e, ρ1, σ1, k))

        // In general, recreate the term and split it.
        // If the split fails, we'll end up rebuilding the term
        case DoAssign(op, lhs, ρ1)::k =>
          states.split(Ev(Assign(op, lhs, v), ρ1, σ, k))

        case DoIncDec(op, ρ1)::k =>
          states.split(Ev(IncDec(op, v), ρ1, σ, k))

        case DoUnaryOp(op, ρ1)::k =>
          states.split(Ev(Unary(op, v), ρ1, σ, k))

        case DoBinaryOp(op, v1, ρ1)::k =>
          states.split(Ev(Binary(op, v1, v), ρ1, σ, k))

        case EvalArgs(op, args, ρ1)::k =>
          op match {
            case Nary.Call =>
              states.split(Ev(Call(v, args), ρ1, σ, k))
            case Nary.InitObject =>
              states.split(Ev(ObjectLit(v::args), ρ1, σ, k))
            case Nary.InitArray =>
              states.split(Ev(ArrayLit(v::args), ρ1, σ, k))
          }

        case EvalMoreArgs(op, pending, done, ρ1)::k =>
          val operands: List[Exp] = pending ++ (v :: done)
          op match {
            case Nary.Call =>
              val fun::args = operands
              states.split(Ev(Call(fun, args), ρ1, σ, k))
            case Nary.InitObject =>
              states.split(Ev(ObjectLit(operands), ρ1, σ, k))
            case Nary.InitArray =>
              states.split(Ev(ArrayLit(operands), ρ1, σ, k))
          }

        case DoArrayOp(op, a, ρ1)::k =>
          states.split(Ev(Index(a, v), ρ1, σ, k))

        case k =>
          None
      }
    }
}
