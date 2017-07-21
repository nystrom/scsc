package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar
import Machine._
import Continuations._
import scsc.jssc.SC._
import scsc.core.Residualization._
import States._

object UnwindingStep {
  trait UnwindingStep {
    self: Unwinding =>

    def step = (k, jump) match {
      // if we hit the bottom of the stack, we're stuck.
      case (Nil, _) => None

      // If we're breaking and we hit a finally block,
      // evaluate the finally block and then rebreak.
      case (FinallyFrame(fin, ρ1)::k, jump) => Some {
        Ev(fin, ρ1, σ, SeqCont(jump, ρ1)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Break
      ////////////////////////////////////////////////////////////////
      case (BreakFrame(_)::k, Break(None)) => Some {
        Co(Undefined(), σ, k)
      }

      case (BreakFrame(Some(x))::k, Break(Some(y))) if x == y => Some {
        Co(Undefined(), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Continue
      ////////////////////////////////////////////////////////////////
      case (ContinueFrame(_)::k, Continue(None)) => Some {
        Co(Undefined(), σ, k)
      }

      case (ContinueFrame(Some(x))::k, Break(Some(y))) if x == y => Some {
        Co(Undefined(), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Return
      ////////////////////////////////////////////////////////////////

      // Once we hit the call frame, evaluate the return value.
      case (CallFrame(ρ1)::k, Return(Some(v: Val))) => Some {
        Co(v, σ, k)
      }

      case (CallFrame(ρ1)::k, Return(None)) => Some {
        Co(Undefined(), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw
      ////////////////////////////////////////////////////////////////

      // If we hit an empty catch frame, just keep propagating the exception.
      case (CatchFrame(Nil, ρ1)::k, Throw(v)) => Some {
        Unwinding(Throw(v), σ, k)
      }

      // Conditional catch.
      // We have to be careful to move the remaining catches into the else part of the if below rather than
      // leaving a CatchFrame with the remaining catches in the continuation. This is because if the body
      // of the catch throws an exception we don't want it caught by later handlers of the same try.
      case (CatchFrame(Catch(ex, Some(test), body)::cs, ρ1)::k, Throw(v: Val)) => Some {
        val loc = FreshLoc()
        val path = Path(loc.address, Local(ex))
        val ρ2 = ρ1 + (ex -> loc)
        val rethrow = cs match {
          case Nil => Throw(v)
          case cs => TryCatch(Throw(v), cs)
        }
        Co(v, σ.assign(path, Undefined(), ρ2), DoAssign(None, path, ρ2)::SeqCont(IfElse(test, body, rethrow), ρ2)::k)
      }

      // Unconditional catch.
      case (CatchFrame(Catch(ex, None, body)::cs, ρ1)::k, Throw(v: Val)) => Some {
        val loc = FreshLoc()
        val path = Path(loc.address, Local(ex))
        val ρ2 = ρ1 + (ex -> loc)
        Co(v, σ.assign(path, Undefined(), ρ2), DoAssign(None, path, ρ2)::SeqCont(body, ρ2)::k)
      }

      // In all other cases, just unwind the stack.
      case (_::k, jump) => Some {
        Unwinding(jump, σ, k)
      }
    }
  }
}

object EvStep {

  trait EvStep {
    self: Ev =>

    def step: Option[State] = e match {

      // For any value (or residual), just run the continuation.
      case v: Val => Some {
        Co(v, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Scopes.
      ////////////////////////////////////////////////////////////////

      case Scope(s) =>
      // Go through all the bindings in the block and add them to the environment
      // as `undefined`. As we go thorugh the block, we'll initialize the variables.
      object CollectBindings extends Rewriter {
        var bindings: Vector[(Name, Exp)] = Vector()
        override def rewrite(e: Exp) = e match {
          case VarDef(x, e) =>
          bindings = bindings :+ ((x, e))
          super.rewrite(e)
          case _: Lambda | _: Scope =>
          // don't recurse on these
          e
          case e =>
          super.rewrite(e)
        }
      }
      CollectBindings.rewrite(s)
      val bindings = CollectBindings.bindings

      val locs = bindings map { case (x, e) => Path(FreshLoc().address, Local(x)) }
      val ρ1 = (bindings zip locs).foldLeft(ρ) {
        case (ρ, ((x, _), loc)) => ρ + (x -> Loc(loc.address))
      }
      val σ1 = locs.foldLeft(σ) {
        case (σ, loc) => σ.assign(loc, Undefined(), ρ1)
      }

      val defs = bindings map {
        case (x, e @ Lambda(xs, body)) => VarDef(x, e)
        case (x, e) => VarDef(x, Undefined())
      }

      // MakeTrees ensures builds the tree so that function bindings
      // are evaluated first, so we don't have to initialize them explicitly.
      // Also all bindings should be either to lambdas or to undefined.
      Some {
        Ev(s, ρ1, σ1, PopScope(defs.toList)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Conditionals
      // ? : and if/else are handled identically, duplicating code
      ////////////////////////////////////////////////////////////////

      // if e then s1 else s2
      case IfElse(e, s1, s2) => Some {
        Ev(e, ρ, σ, BranchCont(SeqCont(s1, ρ)::Nil,
        SeqCont(s2, ρ)::Nil,
        ρ)::k)
      }

      // e ? s1 : s2
      case Cond(e, s1, s2) => Some {
        Ev(e, ρ, σ, CondBranchCont(SeqCont(s1, ρ)::Nil,
        SeqCont(s2, ρ)::Nil,
        ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Loops.
      // This is very much complicated by break and continue.
      // Otherwise we could just desugar everything into IfElse,
      // unrolling the loop and letting generlization handle
      // termination detection and rebuilding the loop.
      ////////////////////////////////////////////////////////////////

      case e @ For(label, Empty(), test, iter, body) => Some {
        Ev(test, ρ, σ, StartLoop(e, ρ, σ)::k)
      }

      case For(label, init, test, iter, body) => Some {
        Ev(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, k)
      }

      // do body while test
      case e @ DoWhile(label, body, test) => Some {
        // optimization: don't push a new break frame unless needed.
        k match {
          case BreakFrame(x)::_ if label == x =>
          Ev(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::k)
          case _ =>
          Ev(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)
        }
      }

      // just desugar into a for loop
      case e @ While(label, test, body) => Some {
        Ev(test, ρ, σ, StartLoop(e, ρ, σ)::k)
      }

      case ForIn(label, init, iter, body) => None

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
      // Blocks.
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
      case VarDef(x, lam @ Lambda(xs, e)) =>
      // Special case lambdas because we need to set the name of the heap object.
      // var Point = function (x, y) { this.x = x; this.y = y}
      // ==
      // var Point = { __code__: fun..., prototype: { __proto__: Function.prototype } }
      ρ.get(x) map {
        loc =>
        val lambdaPath = Local(x)
        val lambdaLoc = Path(FreshLoc().address, lambdaPath)
        val protoPath = Index(Local(x), StringLit("prototype"))
        val protoLoc = Path(FreshLoc().address, protoPath)
        val proto = FunObject("object", Eval.getPrimAddress(Prim("Function.prototype")), Nil, None, Nil)
        val funObj = FunObject("function", Eval.getPrimAddress(Prim("Function.prototype")), xs, Some(e), Nil)
        // TODO Whenever we create a fresh location, we add a temporary to the environment
        // to ensure it's reachable in case we have to
        // residualize before making it reachable from x.
        // TODO: the store has to be robust to deletions.
        // Sanitizing the heap can delete locations from the heap.
        // But really these should map to UNKNOWN rather than to nothing.
        // The location is valid (in one heap), just not known.
        val ass = List(
          Assign(None, Local(x), lambdaLoc),
          Assign(None, Index(lambdaLoc, StringLit("name")), StringLit(x)),
          Assign(None, Index(lambdaLoc, StringLit("length")), Num(xs.length)),
          Assign(None, Index(lambdaLoc, StringLit("prototype")), protoLoc)
        )

        val s2 = ass.reverse.foldRight(Undefined(): Exp) {
          case (e, rest) => Seq(e, rest)
        }

        val σ2 = σ.assign(lambdaLoc, funObj, ρ).assign(protoLoc, proto, ρ)

        Ev(s2, ρ, σ2, k)
      }

      case VarDef(x, e) =>
      ρ.get(x) map {
        loc =>
        Ev(e, ρ, σ, DoAssign(None, Path(loc.address, Local(x)), ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      // We can assign to undefined. yep, that's right.
      case Assign(None, Undefined(), rhs) => Some {
        Ev(rhs, ρ, σ, k)
      }

      case Assign(Some(op), Undefined(), rhs) => Some {
        Ev(rhs, ρ, σ, DoBinaryOp(op, Undefined(), ρ)::k)
      }

      case Assign(op, Local(x), rhs) =>
      ρ.get(x) collect {
        case Loc(addr) =>
        Co(Path(addr, Local(x)), σ, EvalAssignRhs(op, rhs, ρ)::k)
      }

      case Assign(op, Index(a, i), rhs) => Some {
        Ev(a, ρ, σ, EvalPropertyNameForSet(i, ρ)::EvalAssignRhs(op, rhs, ρ)::k)
      }

      case IncDec(op, Local(x)) =>
      ρ.get(x) collect {
        case Loc(addr) =>
        Co(Path(addr, Local(x)), σ, DoIncDec(op, ρ)::k)
      }

      case IncDec(op, Index(a, i)) => Some {
        Ev(a, ρ, σ, EvalPropertyNameForSet(i, ρ)::DoIncDec(op, ρ)::k)
      }


      ////////////////////////////////////////////////////////////////
      // Variables. Just lookup the value. If not present, residualize.
      ////////////////////////////////////////////////////////////////

      case Local(x) =>
      ρ.get(x) flatMap {
        case loc =>
        σ.get(loc) collect {
          case LocClosure(Loc(v)) =>
          Co(Path(v, Local(x)), σ, k)
          case ValClosure(v) =>
          Co(v, σ, k)
        }
      }

      case Index(a, i) => Some {
        Ev(a, ρ, σ, EvalPropertyNameForGet(i, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Special unary operators.
      ////////////////////////////////////////////////////////////////

      case Typeof(e) => Some {
        Ev(e, ρ, σ, DoTypeof(ρ)::k)
      }

      case Void(e) => Some {
        // void e just discards the value and evaluates to undefined
        Ev(e, ρ, σ, FocusCont(Undefined())::k)
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
        Ev(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)
      }

      // A non-method call "f()" passes "window" as "this".
      // Preempt the local not being found.
      // We don't want to residualize the local to another name.

      case Call(fun @ Local(x), args) =>
      ρ.get(x) flatMap {
        loc =>
        σ.get(loc) collect {
          case LocClosure(Loc(v)) =>
          Ev(fun, ρ, σ, EvalArgs(Prim("window"), args, ρ)::k)
        }
      }

      case Call(fun, args) => Some {
        Ev(fun, ρ, σ, EvalArgs(Prim("window"), args, ρ)::k)
      }

      case NewCall(fun @ Local(x), args) =>
      ρ.get(x) flatMap {
        case loc =>
        σ.get(loc) collect {
          case LocClosure(Loc(v)) =>
          Ev(fun, ρ, σ, EvalArgsForNew(args, ρ)::k)
        }
      }

      case NewCall(fun, args) => Some {
        Ev(fun, ρ, σ, EvalArgsForNew(args, ρ)::k)
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
      // Delete a property
      ////////////////////////////////////////////////////////////////

      case Delete(Index(a, i)) => Some {
        Ev(a, ρ, σ, EvalPropertyNameForDel(i, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Object and array literals and lambdas.
      ////////////////////////////////////////////////////////////////

      // Create an empty object
      case ObjectLit(Nil) => Some {
        val loc = Path(FreshLoc().address, ObjectLit(Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
        Co(loc, σ.assign(loc, v, ρ), k)
      }

      // Initialize a non-empty object.
      case ObjectLit(ps) => Some {
        val x = FreshVar()
        val seq = ps.foldLeft(Assign(None, Local(x), ObjectLit(Nil)): Exp) {
          case (seq, Property(prop, value, _, _)) =>
          Seq(seq, Assign(None, Index(Local(x), prop), value))
          case _ => ???
        }
        Ev(Seq(seq, Local(x)), ρ + (x -> FreshLoc()), σ, k)
      }

      // Array literals desugar to objects
      case ArrayLit(es) => Some {
        val loc = Path(FreshLoc().address, NewCall(Prim("Array"), Num(es.length)::Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Array.prototype")), Nil, None, Nil)
        val x = FreshVar()
        val seq = es.zipWithIndex.foldLeft(Assign(None, Local(x), loc): Exp) {
          case (seq, (value, i)) =>
          Seq(seq, Assign(None, Index(Local(x), StringLit(i.toInt.toString)), value))
        }
        Ev(Seq(seq, Seq(Assign(None, Index(Local(x), StringLit("length")), Num(es.length)), Local(x))), ρ, σ.assign(loc, v, ρ), k)
      }

      // Put a lambda in the heap.
      case lam @ Lambda(xs, e) => Some {
        // x = v
        // x.proto = v2
        val x = FreshVar()
        val loc = Path(FreshLoc().address, Local(x))
        val v = FunObject("function", Eval.getPrimAddress(Prim("Function.prototype")), xs, Some(e), Nil)
        val xloc = Path(FreshLoc().address, Local(x))
        val protoLoc = Path(FreshLoc().address, Index(Local(x), StringLit("prototype")))
        val v2 = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
        val ρ2 = ρ + (x -> Loc(xloc.address))
        Co(loc, σ.assign(xloc, loc, ρ2).assign(loc, v, ρ2).assign(protoLoc, v2, ρ2), k)
      }

      ////////////////////////////////////////////////////////////////
      // Other cases.
      ////////////////////////////////////////////////////////////////

      // Don't implement with.
      case With(exp, body) => None

      case e => None
    }
  }

}

object CoStep {

  trait CoStep {
    self: Co =>


    def callDepth = k.foldLeft(0) {
      case (n, CallFrame(_)) => n+1
      case (n, _) => n
    }

    class Subst(subst: Map[Name,Name]) extends scsc.js.TreeWalk.Rewriter {
      override def rewrite(e: Exp) = e match {
        case Local(x) =>
        subst.get(x) match {
          case Some(y) => Local(y)
          case None => Local(x)
        }
        case Lambda(xs, e) =>
        val e1 = new Subst(subst -- xs).rewrite(e)
        Lambda(xs, e1)
        case e =>
        super.rewrite(e)
      }
    }

    def doCall(fun: Val, thisValue: Val, args: List[Val], result: Option[Val], ρ1: Env, σ: Store, k: Cont): Option[St] = {
      val callNumber = CallCounter()

      val SUBST_PARAMS = false

      fun match {
        case Path(addr, path) =>
        σ.get(Loc(addr)) match {
          case Some(ObjClosure(FunObject(_, _, ys, Some(body0), _), ρ2)) =>
          // HACK (breaks eval): rename the variables to prevent name collisions
          val xthis = if (SUBST_PARAMS) s"this$callNumber" else "this"
          val xs = if (SUBST_PARAMS) ys map { y => s"$y$callNumber" } else ys
          val subst = ("this", xthis) :: (ys zip xs)
          val body = if (SUBST_PARAMS)
          new Subst(subst.toMap).rewrite(body0)
          else
          body0

          // Pad the arguments with undefined.
          def pad(params: List[Name], args: List[Exp]): List[Exp] = (params, args) match {
            case (Nil, _) => Nil
            case (_::params, Nil) => Undefined()::pad(params, Nil)
            case (_::params, arg::args) => arg::pad(params, args)
          }
          val args2 = pad(xs, args)
          val seq = (xs zip args2).foldLeft(Assign(None, Local(xthis), thisValue): Exp) {
            case (seq, (x, a)) => Seq(seq, Assign(None, Local(x), a))
          }
          val ρ2 = (xthis::xs).foldLeft(ρ1) {
            case (ρ1, x) => ρ1 + (x -> FreshLoc())
          }
          result match {
            case Some(result) => Some {
              Ev(Seq(Seq(seq, body), result), ρ2, σ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
            }
            case None => Some {
              Ev(Seq(seq, body), ρ2, σ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
            }
          }

          case Some(ValClosure(Prim(fun))) =>
          Eval.evalPrim(fun, args) map {
            case e =>
            // Use Ev, not Co... the prim might be eval and return the expression to eval.
            Ev(e, ρ1, σ, k)
          }

          case _ => None
        }
        case _ => None
      }
    }

    def step: Option[State] = k match {
      // Done!
      case Nil => Some {
        Rebuilt(v, σ, Nil)
      }

      case BranchCont(kt, kf, ρ)::k => v match {
        case v @ CvtBool(true) => Some {
          Co(v, σ, kt ++ k)
        }
        case v @ CvtBool(false) => Some {
          Co(v, σ, kf ++ k)
        }
        case v => Some {
          Rebuilt(v, σ, BranchCont(kt, kf, ρ)::k)
        }
      }

      case CondBranchCont(kt, kf, ρ)::k => v match {
        case v @ CvtBool(true) => Some {
          Co(v, σ, kt ++ k)
        }
        case v @ CvtBool(false) => Some {
          Co(v, σ, kf ++ k)
        }
        case v => Some {
          Rebuilt(v, σ, CondBranchCont(kt, kf, ρ)::k)
        }
      }

      case StartLoop(e @ While(label, test, body), ρ1, σ1)::k => v match {
        case v @ CvtBool(_) =>
          // TODO If we always halt with a value in an empty store, then we must be either
          // a loop that never executes or an infinite loop.
          // optimization: don't push a new break frame unless needed.
          val k1 = k match {
            case BreakFrame(x)::knobreak if label == x => knobreak
            case _ => k
          }

          Some {
            Co(v, σ,
              BranchCont(
                SeqCont(body, ρ1)::ContinueFrame(label)::SeqCont(While(label, test, body), ρ1)::BreakFrame(label)::Nil,
                FocusCont(Undefined())::Nil,
                ρ1)::k1)
          }
        case v => None
      }

      case StartLoop(e @ For(label, Empty(), test, iter, body), ρ1, σ1)::k => v match {
        case v @ CvtBool(_) =>
        // TODO If we always halt with a value in an empty store, then we must be either
        // a loop that never executes or an infinite loop.
          // optimization: don't push a new break frame unless needed.
          val k1 = k match {
            case BreakFrame(x)::knobreak if label == x => knobreak
            case _ => k
          }

          Some {
          Co(v, σ,
            BranchCont(
              SeqCont(body, ρ1)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ1)::BreakFrame(label)::Nil,
              FocusCont(Undefined())::Nil,
              ρ1)::k1)
          }
          case v => None

            // we can't create a Rebuilt state here because break/continue would not work
      }

      // discard useless break and continue frames
      case BreakFrame(_)::k => Some {
        Co(v, σ, k)
      }

      case ContinueFrame(_)::k => Some {
        Co(v, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      // If we got here with a value, just throw out the defs.
      // FIXME: careful: the value might be a location and we
      // might have to residualize the path. I don't think this can
      // happen though across a Scope boundary.
      case PopScope(defs)::k => Some {
        Co(v, σ, k)
      }

      // Discard the value and evaluate the sequel.
      case SeqCont(s2, ρ1)::k => Some {
        Ev(s2, ρ1, σ, k)
      }

      // Change the focus
      case FocusCont(v2)::k => Some {
        Co(v2, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, ρ1)::k => Some {
        val lhs = v
        Ev(rhs, ρ1, σ, DoAssign(op, lhs, ρ1)::k)
      }

      case DoAssign(None, lhs: Path, ρ1)::k => Some {
        // Normal assignment... the result is the rhs value
        Co(v, σ.assign(lhs, v, ρ1), k)
      }

      case DoAssign(Some(op), lhs: Path, ρ1)::k =>
        σ.get(Loc(lhs.address)) flatMap {
          case ValClosure(left) =>
          val right = v
          Eval.evalOp(op, left, right) map {
            case result =>
            Co(result, σ.assign(lhs, result, ρ1), k)
          }
          case _ => None
        }

      case DoAssign(op, lhs, ρ1)::k =>
      None

      case DoIncDec(op, ρ1)::k =>
      v match {
        case loc @ Path(addr, path) =>
        σ.get(Loc(addr)) flatMap {
          case ValClosure(oldValue) =>
          val binOp = op match {
            case Prefix.++ => Binary.+
            case Prefix.-- => Binary.-
            case Postfix.++ => Binary.+
            case Postfix.-- => Binary.-
            case _ => ???
          }
          Eval.evalOp(binOp, oldValue, Num(1)) map {
            case newValue =>
            val resultValue = op match {
              case Prefix.++ => newValue
              case Prefix.-- => newValue
              case Postfix.++ => oldValue
              case Postfix.-- => oldValue
              case _ => ???
            }
            Co(resultValue, σ.assign(loc, newValue, ρ1), k)
          }
          case _ =>
            None

        }

        case v =>
          None
      }

      case DoTypeof(ρ1)::k =>
      v match {
        case Num(v) => Some {
          Co(StringLit("number"), σ, k)
        }
        case Bool(v) => Some {
          Co(StringLit("boolean"), σ, k)
        }
        case StringLit(v) => Some {
          Co(StringLit("string"), σ, k)
        }
        case Undefined() => Some {
          Co(StringLit("undefined"), σ, k)
        }
        case Null() => Some {
          Co(StringLit("object"), σ, k)
        }
        case loc @ Path(addr, path) =>
        σ.get(Loc(addr)) match {
          case Some(ObjClosure(FunObject(typeof, _, _, _, _), _)) => Some {
            Co(StringLit(typeof), σ, k)
          }
          case Some(ValClosure(v)) => Some {
            Co(v, σ, DoTypeof(ρ1)::k)
          }
          case Some(LocClosure(Loc(v))) => Some {
            // The address of an object
            Co(Path(v, path), σ, DoTypeof(ρ1)::k)
          }
          case Some(UnknownClosure()) =>
None

          case None =>
None
        }
        case e =>
None
      }

      case DoUnaryOp(op, ρ1)::k =>
      (op, v) match {
        case (Prefix.!, CvtBool(v)) => Some {
          Co(Bool(!v), σ, k)
        }
        case (Prefix.~, CvtNum(v)) => Some {
          Co(Num(~v.toLong), σ, k)
        }
        case (Prefix.+, CvtNum(v)) => Some {
          Co(Num(+v), σ, k)
        }
        case (Prefix.-, CvtNum(v)) => Some {
          Co(Num(-v), σ, k)
        }
        case (op, v) =>
None
      }

      case EvalBinaryOpRight(op, e2, ρ1)::k =>
      (op, v) match {
        // Short-circuit && and ||
        case (Binary.&&, v @ CvtBool(false)) => Some {
          Co(v, σ, k)
        }
        case (Binary.||, v @ CvtBool(true)) => Some {
          Co(v, σ, k)
        }
        case (op, v) => Some {
          Ev(e2, ρ1, σ, DoBinaryOp(op, v, ρ1)::k)
        }
      }

      case DoBinaryOp(op, v1, ρ1)::k =>
      (op, v1, v) match {
        case (Binary.IN, i, loc @ Path(addr, path)) =>
        // Does the property i exist in loc?
        σ.get(Loc(addr)) match {
          case Some(ObjClosure(_, _)) =>
          Eval.getPropertyAddress(Loc(addr), i, σ) match {
            case Some(v) =>
              Some { Co(Bool(true), σ, k)}
            case None =>
              Some {   Co(Bool(false), σ, k)}
          }
          case _ =>
None
        }
        case (Binary.INSTANCEOF, Null(), Path(_, _)) => Some {
          Co(Bool(false), σ, k)
        }
        case (Binary.INSTANCEOF, Undefined(), Path(_, _)) => Some {
          Co(Bool(false), σ, k)
        }
        case (Binary.INSTANCEOF, v1 @ Path(addr1, path1), v2 @ Path(addr2, path2)) =>
        // x instanceof y
        // ==
        // x.__proto__ === y.prototype
        val result = for {
          ObjClosure(FunObject(_, v1protoLoc, _, _, _), _) <- σ.get(Loc(addr1))
          v2protoLoc <- Eval.getPropertyAddress(Loc(addr2), StringLit("prototype"), σ)
        } yield (v1protoLoc, v2protoLoc)

        result map {
          case (proto1, proto2) if proto1 == proto2 =>
          Co(Bool(true), σ, k)
        }

        case (op, v1, v2) =>
        Eval.evalOp(op, v1, v2) map {
        case v => Co(v, σ, k)
        }
      }


      ////////////////////////////////////////////////////////////////
      // Calls and lambda.
      // FIXME
      // Environment handling is completely broken here.
      // See the old SCSC implementation.
      ////////////////////////////////////////////////////////////////

      case EvalMethodProperty(m, es, ρ1)::k => Some {
        val thisValue = v
        Ev(m, ρ1, σ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)
      }

      case EvalArgs(thisValue, Nil, ρ1)::k =>
        val fun = v
        doCall(fun, thisValue, Nil, None, ρ1, σ, k)

      case EvalArgs(thisValue, arg::args, ρ1)::k => Some {
        val fun = v
        Ev(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)
      }

      case EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
        doCall(fun, thisValue, done :+ v, None, ρ1, σ, k)

      // The function is unknown, so just residualize after evaluating
      // the arguments.
      case EvalMoreArgsForResidual(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, EvalMoreArgsForResidual(fun, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForResidual(fun, Nil, done, ρ1)::k =>
        None

      ///////////////////////////////////////////////////////////////, k/
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k => Some {
        Unwinding(Return(Some(v)), σ, k)
      }

      // If we run off the end of the function body, act like we returned normally.
      case CallFrame(ρ1)::k => Some {
        Co(v, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k => Some {
        Unwinding(Throw(v), σ, k)
      }

      // Run the finally block, if any. Then restore the value.
      case FinallyFrame(fin, ρ1)::k => Some {
        Ev(fin, ρ1, σ, FocusCont(v)::k)
      }

      // If not throwing, just discard catch frames.
      case CatchFrame(cs, ρ1)::k => Some {
        Co(v, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Objects and arrays.
      ////////////////////////////////////////////////////////////////

      // new Point(x, y)
      // creates a new empty object
      // binds the object to this
      // sets this.__proto__ to Point.prototype
      // calls the Point function

      case EvalArgsForNew(Nil, ρ1)::k => Some {
        val fun = v
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, Nil, ρ1)::k)
      }

      case EvalArgsForNew(arg::args, ρ1)::k => Some {
        val fun = v
        Ev(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, Nil, ρ1)::k)
      }

      case EvalMoreArgsForNew(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForNew(fun, Nil, done, ρ1)::k => Some {
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForNewResidual(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, EvalMoreArgsForNewResidual(fun, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForNewResidual(fun, Nil, done, ρ1)::k => None

      case InitProto(fun, args, ρ1)::k =>
        val proto = v

        // Put the object in the heap
        val loc = Path(FreshLoc().address, NewCall(fun, args))

        val protoLoc = proto match {
          case Path(a, p) => Some(Loc(a))
          case Prim(x) => Some(Eval.getPrimAddress(Prim(x)))
          case _ => None
        }

        protoLoc flatMap {
          case protoLoc =>
          val obj = FunObject("object", protoLoc, Nil, None, Nil)
          doCall(fun, loc, args, Some(loc), ρ1, σ.assign(loc, obj, ρ1), k)
        }

      case EvalPropertyNameForDel(i, ρ1)::k => Some {
        val a = v
        Ev(i, ρ1, σ, DoDeleteProperty(a, ρ1)::k)
      }

      case DoDeleteProperty(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, p), i @ CvtString(istr)) =>
          σ.get(Loc(addr)) collect {
            case ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2) =>
            val v = props collectFirst {
              case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Some(Bool(true)) => v
            }
            v match {
              case Some(v) =>
              val removed = props filter {
                case (k, w: Loc) if v == w => false
                case _ => true
              }
              Co(a, σ.assign(a, FunObject(typeof, proto, xs, body, removed), ρ2), k)
              case None =>
              // The field isn't there anyway.
              Co(a, σ, k)
            }
            case ValClosure(_) | LocClosure(_) =>
            Co(a, σ, k)
          }

          case (a, i) =>
          None
        }

      case EvalPropertyNameForSet(i, ρ1)::k => Some {
        val a = v
        Ev(i, ρ1, σ, GetPropertyAddressOrCreate(a, ρ1)::k)
      }

      case GetPropertyAddressOrCreate(a, ρ1)::k =>
      (a, v) match {
        case (a @ Path(addr, path), i @ CvtString(istr)) =>
        σ.get(Loc(addr)) collect {
          case ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2) =>
          val v = props collectFirst {
            case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Some(Bool(true)) => v
          }
          v match {
            case Some(v) =>
            Co(Path(v.address, Index(path, i)), σ, k)
            case None =>
            // FIXME: maybe the property key is reified?
            // I don't think this can happen, though.

            // The field is missing.
            // Create it.
            val fieldLoc = Path(FreshLoc().address, Index(path, i))
            val σ1 = σ.assign(a, FunObject(typeof, proto, xs, body, props :+ (istr, Loc(fieldLoc.address))), ρ2)
            val σ2 = σ1.assign(fieldLoc, Undefined(), ρ2)
            Co(fieldLoc, σ2, k)
          }
          case ValClosure(_) | LocClosure(_) =>
          Co(Undefined(), σ, k)
        }
        case (a, i) =>
        None
      }

      case EvalPropertyNameForGet(i, ρ1)::k => Some {
        val a = v
        Ev(i, ρ1, σ, GetProperty(a, ρ1)::k)
      }

      // restrict the property to values to ensure == during property lookup works correctly
      // otherwise, a[f()] will result in undefined rather than a reified access
      case GetProperty(a, ρ1)::k =>
      (a, v) match {
        case (a @ Path(addr, path), i) =>
        σ.get(Loc(addr)) flatMap {
          case ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2) =>
          println(s"looking for $i in $props")
          val propAddr = props collectFirst {
            case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Some(Bool(true)) => v
          }
          println(s"looking for $i in $props: found $propAddr")
          propAddr match {
            case Some(loc) =>
            println(s"looking for $i in $props: loading $loc")
            σ.get(loc) collect {
              case LocClosure(Loc(v)) =>
              Co(Path(v, Index(path, i)), σ, k)
              case ValClosure(v) =>
              Co(v, σ, k)
            }
            case None => Some {
              if (body != None && Eval.evalOp(Binary.==, StringLit("length"), i) == Some(Bool(true))) {
                Co(Num(xs.length), σ, k)
              }
              else {
                // Try the prototype.
                // If not found, return undefined.
                Co(i, σ, GetProperty(Path(proto.address, path), ρ1)::k)
              }
            }
          }
          case ValClosure(_) | LocClosure(_) => Some {
            Co(Undefined(), σ, k)
          }
          case _ => None
        }
        case (a, i) =>
        None
      }

      /////////////////
      // No more cases....
      /////////////////
    }
  }

}

// Except for branches, stepping rebuilt states are total.
// For branches, the state will split.
object RebuiltStep {


  trait RebuiltStep {
    self: Rebuilt =>

    def step = k match {
      case Nil => None

      // Here we're about to branch with a residual test.
      // We can't actually rebuild this, dammit,
      // since we can't evaluate the continuations properly
      // here. Instead, return None, this will cause the
      // us to get stuck and we'll split.
      case BranchCont(kt, kf, ρ)::k => None
      case CondBranchCont(kt, kf, ρ)::k => None

      case PopScope(defs)::k => Some {
        Rebuilt(defs.foldRight(e)(Sequence.apply), σ, k)
      }

      case StartLoop(loop, ρ1, σ1)::k => Some {
        Rebuilt(loop, σ1, k)
      }

      // discard useless break and continue frames
      // but wrap in a useless loop so that residual
      // breaks and continues still work.
      case BreakFrame(_)::k => Some {
        Rebuilt(e, σ, k)
      }

      case ContinueFrame(_)::k => Some {
        Rebuilt(e, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      // Discard the value and evaluate the sequel.
      case SeqCont(s2, ρ1)::k => Some {
        Rebuilt(Seq(e, s2), σ, k)
      }

      // Change the focus
      case FocusCont(v2)::k => Some {
        Rebuilt(Seq(e, v2), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, ρ1)::k => Some {
        Rebuilt(Assign(op, e, rhs), σ, k)
      }

      case DoAssign(op, lhs, ρ1)::k => Some {
        // Normal assignment... the result is the rhs value
        Rebuilt(Assign(op, reify(lhs), e), σ, k)
      }

      case DoIncDec(op, ρ1)::k => Some {
        Rebuilt(IncDec(op, e), σ, k)
      }

      case DoTypeof(ρ1)::k => Some {
        Rebuilt(Typeof(e), σ, k)
      }

      case DoUnaryOp(op, ρ1)::k => Some {
        Rebuilt(Unary(op, e), σ, k)
      }

      case EvalBinaryOpRight(op, e2, ρ1)::k => Some {
        Rebuilt(Binary(op, e, reify(e2)), σ, k)
      }

      case DoBinaryOp(op, v1, ρ1)::k => Some {
        Rebuilt(Binary(op, reify(v1), e), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Calls and lambda.
      // FIXME
      // Environment handling is completely broken here.
      // See the old SCSC implementation.
      ////////////////////////////////////////////////////////////////

      case EvalMethodProperty(m, es, ρ1)::k => Some {
        Rebuilt(Call(Index(e, m), es), σ, k)
      }

      case EvalArgs(thisValue, args, ρ1)::k => Some {
        Rebuilt(Call(e, args), σ, k)
      }

      case EvalMoreArgs(fun, thisValue, args, done, ρ1)::k => Some {
        Rebuilt(Call(reify(fun), done ++ (e::args)), σ, k)
      }

      // The function is unknown, so just residualize after evaluating
      // the arguments.
      case EvalMoreArgsForResidual(fun, args, done, ρ1)::k => Some {
        Rebuilt(Call(reify(fun), done ++ (e::args)), σ, k)
      }

      ///////////////////////////////////////////////////////////////, k/
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k => Some {
        e match {
          case Undefined() =>
          Rebuilt(Return(None), σ, k)
          case e =>
          Rebuilt(Return(Some(e)), σ, k)
        }
      }

      // If we run off the end of the function body, act like we returned normally.
      case CallFrame(ρ1)::k => Some {
        Rebuilt(e, σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k => Some {
        Rebuilt(Throw(e), σ, k)
      }

      // Run the finally block, if any. Then restore the value.
      case FinallyFrame(fin, ρ1)::k => Some {
        Rebuilt(TryFinally(e, fin), σ, k)
      }

      // If not throwing, just discard catch frames.
      case CatchFrame(cs, ρ1)::k => Some {
        Rebuilt(TryCatch(e, cs), σ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Objects and arrays.
      ////////////////////////////////////////////////////////////////

      // new Point(x, y)
      // creates a new empty object
      // binds the object to this
      // sets this.__proto__ to Point.prototype
      // calls the Point function

      case EvalArgsForNew(args, ρ1)::k => Some {
        Rebuilt(NewCall(e, args), σ, k)
      }

      case EvalMoreArgsForNew(fun, args, done, ρ1)::k => Some {
        Rebuilt(NewCall(reify(fun), done ++ (e::args)), σ, k)
      }

      case EvalMoreArgsForNewResidual(fun, args, done, ρ1)::k => Some {
        Rebuilt(NewCall(reify(fun), done ++ (e::args)), σ, k)
      }

      case InitProto(fun, args, ρ1)::k => Some {
        Rebuilt(NewCall(reify(fun), args :+ e), σ, k)
      }

      case EvalPropertyNameForDel(i, ρ1)::k => Some {
        Rebuilt(Delete(Index(e, i)), σ, k)
      }

      case DoDeleteProperty(a, ρ1)::k => Some {
        Rebuilt(Delete(Index(a, e)), σ, k)
      }

      case EvalPropertyNameForSet(i, ρ1)::k => Some {
        Rebuilt(Index(e, i), σ, k)
      }

      case GetPropertyAddressOrCreate(a, ρ1)::k => Some {
        Rebuilt(Index(a, e), σ, k)
      }

      case EvalPropertyNameForGet(i, ρ1)::k => Some {
        Rebuilt(Index(e, i), σ, k)
      }

      // restrict the property to values to ensure == during property lookup works correctly
      // otherwise, a[f()] will result in undefined rather than a reified access
      case GetProperty(a, ρ1)::k => Some {
        Rebuilt(Index(a, e), σ, k)
      }

      /////////////////
      // No more cases....
      /////////////////
    }

  }

}
