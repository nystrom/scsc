package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar

// This object defines the interpreter states and implements the step function
// for the JS interpreter.
object States {
  import Machine._
  import Continuations._
  import scsc.jssc.SC._
  import scsc.core.Residualization._

  val LONG_CONTINUATIONS = false

  import org.bitbucket.inkytonik.kiama.util.Counter

  object CallCounter extends Counter {
    def apply(): Int = next()
  }

  // We implement the machine in "apply, eval, continue" form, following:
  // Olivier Danvy. An Analytical Approach to Program as Data Objects.
  // DSc thesis, Department of Computer Science, Aarhus University, 2006.

  // Ev dispatches on the expression, shifting the focus to a subexpression.
  // Co has a value in the focus and dispatches on the continuation.
  // Unwinding has a jump in the focus and dispatches on the continuation.
  //
  // The followings do not advance at all
  // Halt is done
  // Err is done badly
  // Stuck wraps a state where no rule applies or where the whistle blue indicating evaluation should stop.

  // The step function can return either zero or one state.
  sealed trait State {
    def step: Option[State]
  }

  sealed trait FinalState extends State {
    def step = None
  }

  object Stopped {
    def unapply(s: State): Option[(Val, Store, Effect)] = s match {
      case Halt(v2, σ2, φ2) => Some((v2, σ2, φ2))
      case Co(v2, σ2, φ2, k) => Some((v2, σ2, φ2))
      case Ev(e, ρ, σ, φ, k) => Split.rebuildEv(e, ρ, σ, φ, k).flatMap(unapply _)
      case Unwinding(jump, σ2, φ2, k) => Some((Undefined(), σ2, φ2.extend(jump)))
      case _ => None
    }
  }

  case class Halt(v: Val, σ: Store, φ: Effect) extends FinalState {
    def residual: Exp = {
      val seq = φ.seq(v)
      φ.vars.foldRight(seq) {
        case (x, e) => Seq(VarDef(x, Undefined()), e)
      }
    }
  }

  case class Err(message: String, st: State) extends FinalState

  case class Ev(e: Exp, ρ: Env, σ: Store, φ: Effect, k: Cont) extends State {
    override def toString = s"""Ev
  e = $e
  φ = $φ
  k = ${k.mkString("[", "\n       ", "]")}"""
  //   override def toString = s"""Ev
  // e = $e
  // ρ = ${ρ.toVector.sortBy(_._1).mkString("{", "\n       ", "}")}
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // φ = $φ
  // k = ${k.mkString("[", "\n       ", "]")}"""

    def step: Option[State] = e match {

      // For any value (or residual), just run the continuation.
      case v: Val => Some {
        Co(v, σ, φ, k)
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
          Ev(s, ρ1, σ1, φ.extend(defs.foldLeft(Undefined(): Exp)(Sequence.apply)), k)
        }

      ////////////////////////////////////////////////////////////////
      // Conditionals
      // ? : and if/else are handled identically, duplicating code
      ////////////////////////////////////////////////////////////////

      // if e then s1 else s2
      case IfElse(e, s1, s2) => Some {
        Ev(e, ρ, σ, φ, BranchCont(SeqCont(s1, ρ)::Nil,
                                  SeqCont(s2, ρ)::Nil,
                                  ρ)::k)
      }

      // e ? s1 : s2
      case Cond(e, s1, s2) => Some {
        Ev(e, ρ, σ, φ, BranchCont(SeqCont(s1, ρ)::Nil,
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
        Ev(test, ρ, σ, φ, StartLoop(e, ρ, σ, φ)::k)
      }

      case For(label, init, test, iter, body) => Some {
        Ev(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, φ, k)
      }

      // do body while test
      case e @ DoWhile(label, body, test) => Some {
        // optimization: don't push a new break frame unless needed.
        k match {
          case BreakFrame(x)::_ if label == x =>
            Ev(body, ρ, σ, φ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::k)
          case _ =>
            Ev(body, ρ, σ, φ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)
        }
      }

      // just desugar into a for loop
      case e @ While(label, test, body) => Some {
        Ev(test, ρ, σ, φ, StartLoop(e, ρ, σ, φ)::k)
      }

      case ForIn(label, init, iter, body) => None

      ////////////////////////////////////////////////////////////////
      // Break and continue.
      ////////////////////////////////////////////////////////////////

      case Break(label) => Some {
        Unwinding(Break(label), σ, φ, k)
      }

      case Continue(label) => Some {
        Unwinding(Continue(label), σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      case Empty() => Some {
        Co(Undefined(), σ, φ, k)
      }

      case Seq(s1, s2) => Some {
        Ev(s1, ρ, σ, φ, SeqCont(s2, ρ)::k)
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

            Ev(s2, ρ, σ2, φ, k)
        }

      case VarDef(x, e) =>
        ρ.get(x) map {
          loc =>
            Ev(e, ρ, σ, φ, DoAssign(None, Path(loc.address, Local(x)), ρ)::k)
        }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      // We can assign to undefined. yep, that's right.
      case Assign(None, Undefined(), rhs) => Some {
        Ev(rhs, ρ, σ, φ, k)
      }

      case Assign(Some(op), Undefined(), rhs) => Some {
        Ev(rhs, ρ, σ, φ, DoBinaryOp(op, Undefined(), ρ)::k)
      }

      case Assign(op, Local(x), rhs) =>
        ρ.get(x) collect {
          case Loc(addr) =>
            Co(Path(addr, Local(x)), σ, φ, EvalAssignRhs(op, rhs, ρ)::k)
        }

      case Assign(op, Index(a, i), rhs) => Some {
        Ev(a, ρ, σ, φ, EvalPropertyNameForSet(i, ρ)::EvalAssignRhs(op, rhs, ρ)::k)
      }

      case IncDec(op, Local(x)) =>
        ρ.get(x) collect {
          case Loc(addr) =>
            Co(Path(addr, Local(x)), σ, φ, DoIncDec(op, ρ)::k)
        }

      case IncDec(op, Index(a, i)) => Some {
        Ev(a, ρ, σ, φ, EvalPropertyNameForSet(i, ρ)::DoIncDec(op, ρ)::k)
      }


      ////////////////////////////////////////////////////////////////
      // Variables. Just lookup the value. If not present, residualize.
      ////////////////////////////////////////////////////////////////

      case Local(x) =>
        ρ.get(x) flatMap {
          case loc =>
            σ.get(loc) map {
              case LocClosure(Loc(v)) =>
                Co(Path(v, Local(x)), σ, φ, k)
              case ValClosure(v) =>
                Co(v, σ, φ, k)
            }
        }

      case Index(a, i) => Some {
        Ev(a, ρ, σ, φ, EvalPropertyNameForGet(i, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Special unary operators.
      ////////////////////////////////////////////////////////////////

      case Typeof(e) => Some {
        Ev(e, ρ, σ, φ, DoTypeof(ρ)::k)
      }

      case Void(e) => Some {
        // void e just discards the value and evaluates to undefined
        Ev(e, ρ, σ, φ, FocusCont(Undefined())::k)
      }

      ////////////////////////////////////////////////////////////////
      // Unary operators.
      ////////////////////////////////////////////////////////////////

      case Unary(op, e) => Some {
        Ev(e, ρ, σ, φ, DoUnaryOp(op, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Binary operators.
      ////////////////////////////////////////////////////////////////

      case Binary(op, e1, e2) => Some {
        Ev(e1, ρ, σ, φ, EvalBinaryOpRight(op, e2, ρ)::k)
      }


      ////////////////////////////////////////////////////////////////
      // Calls.
      ////////////////////////////////////////////////////////////////

      // A method call "x.m()" passes "x" as "this"
      case Call(Index(e, m), args) => Some {
        Ev(e, ρ, σ, φ, EvalMethodProperty(m, args, ρ)::k)
      }

      // A non-method call "f()" passes "window" as "this".
      // Preempt the local not being found.
      // We don't want to residualize the local to another name.

      case Call(fun @ Local(x), args) =>
        ρ.get(x) flatMap {
          loc =>
            σ.get(loc) collect {
              case LocClosure(Loc(v)) =>
                Ev(fun, ρ, σ, φ, EvalArgs(Prim("window"), args, ρ)::k)
            }
        }

      case Call(fun, args) => Some {
        Ev(fun, ρ, σ, φ, EvalArgs(Prim("window"), args, ρ)::k)
      }

      case NewCall(fun @ Local(x), args) =>
        ρ.get(x) flatMap {
          case loc =>
            σ.get(loc) collect {
              case LocClosure(Loc(v)) =>
                Ev(fun, ρ, σ, φ, EvalArgsForNew(args, ρ)::k)
            }
        }

      case NewCall(fun, args) => Some {
        Ev(fun, ρ, σ, φ, EvalArgsForNew(args, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case Return(Some(e)) => Some {
        Ev(e, ρ, σ, φ, DoReturn()::k)
      }

      case Return(None) => Some {
        Co(Undefined(), σ, φ, DoReturn()::k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case Throw(e) => Some {
        Ev(e, ρ, σ, φ, DoThrow()::k)
      }

      case TryCatch(e, Nil) => Some {
        Ev(e, ρ, σ, φ, k)
      }

      case TryCatch(e, cs) => Some {
        // FIXME: need to add try/catch to the residual in case
        // residual code throws an exception...
        // OR: when a call is added to the residual, branch and simulate a residual throw
        Ev(e, ρ, σ, φ, CatchFrame(cs, ρ)::k)
      }

      case TryFinally(e, fin) => Some {
        // FIXME: need to add try/finally to the residual in case
        // residual code throws an exception...
        Ev(e, ρ, σ, φ, FinallyFrame(fin, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Delete a property
      ////////////////////////////////////////////////////////////////

      case Delete(Index(a, i)) => Some {
        Ev(a, ρ, σ, φ, EvalPropertyNameForDel(i, ρ)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Object and array literals and lambdas.
      ////////////////////////////////////////////////////////////////

      // Create an empty object
      case ObjectLit(Nil) => Some {
        val loc = Path(FreshLoc().address, ObjectLit(Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
        Co(loc, σ.assign(loc, v, ρ), φ, k)
      }

      // Initialize a non-empty object.
      case ObjectLit(ps) => Some {
        val x = FreshVar()
        val seq = ps.foldLeft(Assign(None, Local(x), ObjectLit(Nil)): Exp) {
          case (seq, Property(prop, value, _, _)) =>
            Seq(seq, Assign(None, Index(Local(x), prop), value))
          case _ => ???
        }
        Ev(Seq(seq, Local(x)), ρ + (x -> FreshLoc()), σ, φ, k)
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
        Ev(Seq(seq, Seq(Assign(None, Index(Local(x), StringLit("length")), Num(es.length)), Local(x))), ρ, σ.assign(loc, v, ρ), φ, k)
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
        Co(loc, σ.assign(xloc, loc, ρ2).assign(loc, v, ρ2).assign(protoLoc, v2, ρ2), φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Other cases.
      ////////////////////////////////////////////////////////////////

      // Don't implement with.
      case With(exp, body) => None

      case e => None
    }
  }

  case class Rebuild(s: State) extends FinalState {
    override def step = None
  }

  // The Unwinding state just pops continuations until hitting a call or loop or catch.
  case class Unwinding(jump: Exp, σ: Store, φ: Effect, k: Cont) extends State {
  //   override def toString = s"""Unwinding
  // e = $jump
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // φ = $φ
  // k = ${k.mkString("[", "\n       ", "]")}"""
    override def toString = s"""Unwinding
  e = $jump
  φ = $φ
  k = ${k.mkString("[", "\n       ", "]")}"""

    def step = (k, jump) match {
      // if we hit the bottom of the stack, we're stuck.
      case (Nil, _) => None

      // If we're breaking and we hit a finally block,
      // evaluate the finally block and then rebreak.
      case (FinallyFrame(fin, ρ1)::k, jump) => Some {
        Ev(fin, ρ1, σ, φ, SeqCont(jump, ρ1)::k)
      }

      ////////////////////////////////////////////////////////////////
      // Break
      ////////////////////////////////////////////////////////////////
      case (BreakFrame(_)::k, Break(None)) => Some {
        Co(Undefined(), σ, φ, k)
      }

      case (BreakFrame(Some(x))::k, Break(Some(y))) if x == y => Some {
        Co(Undefined(), σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Continue
      ////////////////////////////////////////////////////////////////
      case (ContinueFrame(_)::k, Continue(None)) => Some {
        Co(Undefined(), σ, φ, k)
      }

      case (ContinueFrame(Some(x))::k, Break(Some(y))) if x == y => Some {
        Co(Undefined(), σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Return
      ////////////////////////////////////////////////////////////////

      // Once we hit the call frame, evaluate the return value.
      case (CallFrame(ρ1)::k, Return(Some(v: Val))) => Some {
        Co(v, σ, φ, k)
      }

      case (CallFrame(ρ1)::k, Return(None)) => Some {
        Co(Undefined(), σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Throw
      ////////////////////////////////////////////////////////////////

      // If we hit an empty catch frame, just keep propagating the exception.
      case (CatchFrame(Nil, ρ1)::k, Throw(v)) => Some {
        Unwinding(Throw(v), σ, φ, k)
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
        Co(v, σ.assign(path, Undefined(), ρ2), φ, DoAssign(None, path, ρ2)::SeqCont(IfElse(test, body, rethrow), ρ2)::k)
      }

      // Unconditional catch.
      case (CatchFrame(Catch(ex, None, body)::cs, ρ1)::k, Throw(v: Val)) => Some {
        val loc = FreshLoc()
        val path = Path(loc.address, Local(ex))
        val ρ2 = ρ1 + (ex -> loc)
        Co(v, σ.assign(path, Undefined(), ρ2), φ, DoAssign(None, path, ρ2)::SeqCont(body, ρ2)::k)
      }

      // In all other cases, just unwind the stack.
      case (_::k, jump) => Some {
        Unwinding(jump, σ, φ, k)
      }
    }
  }

  case class Co(v: Val, σ: Store, φ: Effect, k: Cont) extends State {
  //   override def toString = s"""Co
  // v = $v
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // φ = $φ
  // k = ${k.mkString("[", "\n       ", "]")}"""

    override def toString = s"""Co
  v = $v
  φ = $φ
  k = ${k.mkString("[", "\n       ", "]")}"""

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

      fun match {
        case Path(addr, path) =>
          σ.get(Loc(addr)) match {
            case Some(ObjClosure(FunObject(_, _, ys, Some(body0), _), ρ2)) =>
              // HACK (breaks eval): rename the variables to prevent name collisions
              val xthis = s"this$callNumber"
              val xs = ys map { y => s"$y$callNumber" }
              val subst = ("this", xthis) :: (ys zip xs)
              val body = new Subst(subst.toMap).rewrite(body0)

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
                  Ev(Seq(Seq(seq, body), result), ρ2, σ, φ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
                }
                case None => Some {
                  Ev(Seq(seq, body), ρ2, σ, φ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
                }
              }

            case Some(ValClosure(Prim(fun))) =>
              Eval.evalPrim(fun, args) map {
                case e =>
                  // Use Ev, not Co... the prim might be eval and return the expression to eval.
                  Ev(e, ρ1, σ, φ, k)
              }

            case _ =>
              None
          }
        case _ =>
          None
      }
    }

    def step = k match {
      // Done!
      case Nil => Some {
        Halt(v, σ, φ)
      }

      case BranchCont(kt, kf, ρ)::k =>
        v match {
          case v @ CvtBool(true) => Some {
            Co(v, σ, φ, kt ++ k)
          }
          case v @ CvtBool(false) => Some {
            Co(v, σ, φ, kf ++ k)
          }
          case _ => None
        }

      case StartLoop(e @ While(label, test, body), ρ1, σ1, φ1)::k =>
        v match {
          case Residual(x) =>
            // just get stuck immediately
            None

          case v =>
            // If we always halt with a value in an empty store, then we must be either
            // a loop that never executes or an infinite loop.
            /*
            Drive.drive(Nil, Nil, false)(Ev(test, ρ1, σ0, φ0, Nil)) match {
              case (Halt(CvtBool(true), σ2, φ2), _) =>
                // just get stuck immediately
                Stuck(Ev(e, ρ1, σ1, φ1, k))
              case _ =>
              */
            Some {
                // optimization: don't push a new break frame unless needed.
                val k1 = k match {
                  case BreakFrame(x)::knobreak if label == x => knobreak
                  case _ => k
                }

                Co(v, σ, φ,
                  BranchCont(
                    SeqCont(body, ρ1)::ContinueFrame(label)::SeqCont(While(label, test, body), ρ1)::BreakFrame(label)::Nil,
                    FocusCont(Undefined())::Nil,
                    ρ1)::k1)
            }
        }

      case StartLoop(e @ For(label, Empty(), test, iter, body), ρ1, σ1, φ1)::k =>
        v match {
          case Residual(x) =>
            // just get stuck immediately
            None

          case v =>
            // If we always halt with a value in an empty store, then we must be either
            // a loop that never executes or an infinite loop.
            /*
            Drive.drive(Nil, Nil, false)(Ev(test, ρ1, σ0, φ0, Nil)) match {
              case (Halt(CvtBool(true), σ2, φ2), _) =>
                // just get stuck immediately
                Stuck(Ev(e, ρ1, σ1, φ1, k))
              case _ =>
              */
            Some {
                // optimization: don't push a new break frame unless needed.
                val k1 = k match {
                  case BreakFrame(x)::knobreak if label == x => knobreak
                  case _ => k
                }

                Co(v, σ, φ,
                  BranchCont(
                    SeqCont(body, ρ1)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ1)::BreakFrame(label)::Nil,
                    FocusCont(Undefined())::Nil,
                    ρ1)::k1)
            }
        }

      // discard useless break and continue frames
      case BreakFrame(_)::k => Some {
        Co(v, σ, φ, k)
      }

      case ContinueFrame(_)::k => Some {
        Co(v, σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      // Discard the value and evaluate the sequel.
      case SeqCont(s2, ρ1)::k => Some {
        Ev(s2, ρ1, σ, φ, k)
      }

      // Change the focus
      case FocusCont(v2)::k => Some {
        Co(v2, σ, φ, k)
      }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, ρ1)::k => Some {
        val lhs = v
        Ev(rhs, ρ1, σ, φ, DoAssign(op, lhs, ρ1)::k)
      }

      case DoAssign(None, lhs: Path, ρ1)::k => Some {
        // Normal assignment... the result is the rhs value
        Co(v, σ.assign(lhs, v, ρ1), φ, k)
      }

      case DoAssign(Some(op), lhs: Path, ρ1)::k =>
        σ.get(Loc(lhs.address)) flatMap {
          case ValClosure(left) =>
            val right = v
            Eval.evalOp(op, left, right) map {
              case result =>
                Co(result, σ.assign(lhs, result, ρ1), φ, k)
            }
        }

      case DoAssign(op, lhs, ρ1)::k => None

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
                    Co(resultValue, σ.assign(loc, newValue, ρ1), φ, k)
                }
            }

          case v =>
            None
        }

      case DoTypeof(ρ1)::k =>
        v match {
          case Num(v) => Some {
            Co(StringLit("number"), σ, φ, k)
          }
          case Bool(v) => Some {
            Co(StringLit("boolean"), σ, φ, k)
          }
          case StringLit(v) => Some {
            Co(StringLit("string"), σ, φ, k)
          }
          case Undefined() => Some {
            Co(StringLit("undefined"), σ, φ, k)
          }
          case Null() => Some {
            Co(StringLit("object"), σ, φ, k)
          }
          case loc @ Path(addr, path) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, _, _, _, _), _)) => Some {
                Co(StringLit(typeof), σ, φ, k)
              }
              case Some(ValClosure(v)) => Some {
                Co(v, σ, φ, DoTypeof(ρ1)::k)
              }
              case Some(LocClosure(Loc(v))) => Some {
                // The address of an object
                Co(Path(v, path), σ, φ, DoTypeof(ρ1)::k)
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
            Co(Bool(!v), σ, φ, k)
          }
          case (Prefix.~, CvtNum(v)) => Some {
            Co(Num(~v.toLong), σ, φ, k)
          }
          case (Prefix.+, CvtNum(v)) => Some {
            Co(Num(+v), σ, φ, k)
          }
          case (Prefix.-, CvtNum(v)) => Some {
            Co(Num(-v), σ, φ, k)
          }
          case (op, v) =>
            None
        }

      case EvalBinaryOpRight(op, e2, ρ1)::k =>
        (op, v) match {
          // Short-circuit && and ||
          case (Binary.&&, v @ CvtBool(false)) => Some {
            Co(v, σ, φ, k)
          }
          case (Binary.||, v @ CvtBool(true)) => Some {
            Co(v, σ, φ, k)
          }
          case (op, v) => Some {
            Ev(e2, ρ1, σ, φ, DoBinaryOp(op, v, ρ1)::k)
          }
        }

      case DoBinaryOp(op, v1, ρ1)::k =>
        (op, v1, v) match {
          case (Binary.IN, i, loc @ Path(addr, path)) =>
            // Does the property i exist in loc?
            σ.get(Loc(addr)) collect {
              case ObjClosure(_, _) =>
                Eval.getPropertyAddress(Loc(addr), i, σ) match {
                  case Some(v) =>
                    Co(Bool(true), σ, φ, k)
                  case None =>
                    Co(Bool(false), σ, φ, k)
                }
            }
          case (Binary.INSTANCEOF, Null(), Path(_, _)) => Some {
            Co(Bool(false), σ, φ, k)
          }
          case (Binary.INSTANCEOF, Undefined(), Path(_, _)) => Some {
            Co(Bool(false), σ, φ, k)
          }
          case (Binary.INSTANCEOF, v1 @ Path(addr1, path1), v2 @ Path(addr2, path2)) =>
            // x instanceof y
            // ==
            // x.__proto__ === y.prototype
            val result = for {
              ObjClosure(FunObject(_, v1protoLoc, _, _, _), _) <- σ.get(Loc(addr1))
              v2protoLoc <- Eval.getPropertyAddress(Loc(addr2), StringLit("prototype"), σ)
            } yield (v1protoLoc, v2protoLoc)

            result collect {
              case (proto1, proto2) if proto1 == proto2 =>
                Co(Bool(true), σ, φ, k)
            }

          case (op, v1, v2) =>
            Eval.evalOp(op, v1, v2) map {
              v => Co(v, σ, φ, k)
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
        Ev(m, ρ1, σ, φ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)
      }

      case EvalArgs(thisValue, Nil, ρ1)::k =>
        val fun = v
        doCall(fun, thisValue, Nil, None, ρ1, σ, k)

      case EvalArgs(thisValue, arg::args, ρ1)::k => Some {
        val fun = v
        Ev(arg, ρ1, σ, φ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)
      }

      case EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, φ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
        doCall(fun, thisValue, done :+ v, None, ρ1, σ, k)

      // The function is unknown, so just residualize after evaluating
      // the arguments.
      case EvalMoreArgsForResidual(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForResidual(fun, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForResidual(fun, Nil, done, ρ1)::k =>
        None

      ///////////////////////////////////////////////////////////////, k/
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k => Some {
        Unwinding(Return(Some(v)), σ, φ, k)
      }

      // If we run off the end of the function body, act like we returned normally.
      case CallFrame(ρ1)::k => Some {
        Co(v, σ, φ, k)
      }


      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k => Some {
        Unwinding(Throw(v), σ, φ, k)
      }

      // Run the finally block, if any. Then restore the value.
      case FinallyFrame(fin, ρ1)::k => Some {
        Ev(fin, ρ1, σ, φ, FocusCont(v)::k)
      }

      // If not throwing, just discard catch frames.
      case CatchFrame(cs, ρ1)::k => Some {
        Co(v, σ, φ, k)
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
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, φ, InitProto(fun, Nil, ρ1)::k)
      }

      case EvalArgsForNew(arg::args, ρ1)::k => Some {
        val fun = v
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForNew(fun, args, Nil, ρ1)::k)
      }

      case EvalMoreArgsForNew(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForNew(fun, args, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForNew(fun, Nil, done, ρ1)::k => Some {
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, φ, InitProto(fun, done :+ v, ρ1)::k)
      }

      case EvalMoreArgsForNewResidual(fun, arg::args, done, ρ1)::k => Some {
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForNewResidual(fun, args, done :+ v, ρ1)::k)
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
        Ev(i, ρ1, σ, φ, DoDeleteProperty(a, ρ1)::k)
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
                    Co(a, σ.assign(a, FunObject(typeof, proto, xs, body, removed), ρ2), φ, k)
                  case None =>
                    // The field isn't there anyway.
                    Co(a, σ, φ, k)
                }
              case ValClosure(_) | LocClosure(_) =>
                Co(a, σ, φ, k)
            }

          case (a, i) =>
            None
        }

      case EvalPropertyNameForSet(i, ρ1)::k => Some {
        val a = v
        Ev(i, ρ1, σ, φ, GetPropertyAddressOrCreate(a, ρ1)::k)
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
                    Co(Path(v.address, Index(path, i)), σ, φ, k)
                  case None =>
                    // FIXME: maybe the property key is reified?
                    // I don't think this can happen, though.

                    // The field is missing.
                    // Create it.
                    val fieldLoc = Path(FreshLoc().address, Index(path, i))
                    val σ1 = σ.assign(a, FunObject(typeof, proto, xs, body, props :+ (istr, Loc(fieldLoc.address))), ρ2)
                    val σ2 = σ1.assign(fieldLoc, Undefined(), ρ2)
                    Co(fieldLoc, σ2, φ, k)
                }
              case ValClosure(_) | LocClosure(_) =>
                Co(Undefined(), σ, φ, k)
            }
          case (a, i) =>
            None
        }

      case EvalPropertyNameForGet(i, ρ1)::k => Some {
        val a = v
        Ev(i, ρ1, σ, φ, GetProperty(a, ρ1)::k)
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
                        Co(Path(v, Index(path, i)), σ, φ, k)
                      case ValClosure(v) =>
                        Co(v, σ, φ, k)
                    }
                  case None => Some {
                    if (body != None && Eval.evalOp(Binary.==, StringLit("length"), i) == Some(Bool(true))) {
                      Co(Num(xs.length), σ, φ, k)
                    }
                    else {
                      // Try the prototype.
                      // If not found, return undefined.
                      Co(i, σ, φ, GetProperty(Path(proto.address, path), ρ1)::k)
                    }
                  }
                }
              case ValClosure(_) | LocClosure(_) => Some {
                Co(Undefined(), σ, φ, k)
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
