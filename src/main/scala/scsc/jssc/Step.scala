package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar

// Step function for the CESK machine. We put this in a separate module to reduce compilation time.
object Step {
  import Machine._
  import Continuations._
  import Residualization._
  import CESK._

  import org.bitbucket.inkytonik.kiama.util.Counter

  object CallCounter extends Counter {
    def apply(): Int = next()
  }

  // We implement the machine in "apply, eval, continue" form, following:
  // Olivier Danvy. An Analytical Approach to Program as Data Objects.
  // DSc thesis, Department of Computer Science, Aarhus University, 2006.

  // An Ev state dispatches on the expression, shifting the focus
  // to a subexpression.
  // A Co state has a value in the focus and dispatches on the continuation.

  sealed trait State {
    def step: State
  }

  case class Halt(v: Val, φ: Effect) extends State {
    def step = ???

    def residual: Exp = φ match {
      case Effect(_, Undefined()) => v
      case Effect(vars, e) =>
        val body = e match {
          case Undefined() => v
          case e => Seq(e, v)
        }
        vars.foldRight(body) {
          case (x, e) => Seq(VarDef(x, Undefined()), e)
        }
    }
  }

  case class Err(message: String, st: State) extends State {
    def step = ???
  }

  case class Ev(e: Exp, ρ: Env, σ: Store, φ: Effect, k: Cont) extends State {
    override def toString = s"""Ev
  e = $e
  ρ = ${ρ.toVector.sortBy(_._1).mkString("{", "\n       ", "}")}
  σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  φ = $φ
  k = ${k.mkString("[", "\n       ", "]")}"""

    def step = e match {

      // For any value (or residual), just run the continuation.
      case v: Val => Co(v, σ, φ, k)

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
        Ev(s, ρ1, σ1, Effect(φ.vars, defs.foldLeft(φ.body)(Sequence.apply)), k)

      ////////////////////////////////////////////////////////////////
      // Conditionals
      // ? : and if/else are handled identically, duplicating code
      ////////////////////////////////////////////////////////////////

      // if e then s1 else s2
      case IfElse(e, s1, s2) =>
        Ev(e, ρ, σ, φ, BranchCont(SeqCont(s1, ρ)::Nil,
                                  SeqCont(s2, ρ)::Nil,
                                  ρ)::k)

      // e ? s1 : s2
      case Cond(e, s1, s2) =>
        Ev(e, ρ, σ, φ, BranchCont(SeqCont(s1, ρ)::Nil,
                                  SeqCont(s2, ρ)::Nil,
                                  ρ)::k)

      ////////////////////////////////////////////////////////////////
      // Loops.
      // This is very much complicated by break and continue.
      // Otherwise we could just desugar everything into IfElse,
      // unrolling the loop and letting generlization handle
      // termination detection and rebuilding the loop.
      ////////////////////////////////////////////////////////////////

      case For(label, Empty(), test, iter, body) =>
        Ev(test, ρ, σ, φ, BranchCont(
                          SeqCont(body, ρ)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ)::BreakFrame(label)::Nil,
                          FocusCont(Undefined())::Nil,
                          ρ)::k)

      case For(label, init, test, iter, body) =>
        Ev(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, φ, k)


      // do body while test
      case DoWhile(label, body, test) =>
        Ev(body, ρ, σ, φ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)

      // just desugar into a for loop
      case While(label, test, body) =>
        Ev(For(label, Empty(), test, Empty(), body), ρ, σ, φ, k)

      case ForIn(label, init, iter, body) =>
        // FIXME: implement!
        // Eval iter to get an object.
        // Loop through all the properties of that object.
        Co(Undefined(), σ, φ, k).MakeResidual(ForIn(label, init, iter, body), ρ, k)

      ////////////////////////////////////////////////////////////////
      // Break and continue.
      ////////////////////////////////////////////////////////////////

      case Break(label) =>
        Co(Undefined(), σ, φ, Breaking(label)::k)

      case Continue(label) =>
        Co(Undefined(), σ, φ, Continuing(label)::k)

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      case Empty() =>
        Co(Undefined(), σ, φ, k)

      case Seq(s1, s2) =>
        Ev(s1, ρ, σ, φ, SeqCont(s2, ρ)::k)

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
        ρ.get(x) match {
          case Some(loc) =>
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
          case None =>
            Err(s"variable $x not found", this)
        }

      case VarDef(x, e) =>
        ρ.get(x) match {
          case Some(loc) =>
            Ev(e, ρ, σ, φ, DoAssign(None, Path(loc.address, Local(x)), ρ)::k)
          case None =>
            Err(s"variable $x not found", this)
        }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      // We can assign to undefined. yep, that's right.
      case Assign(None, Undefined(), rhs) =>
        Ev(rhs, ρ, σ, φ, k)

      case Assign(Some(op), Undefined(), rhs) =>
        Ev(rhs, ρ, σ, φ, DoBinaryOp(op, Undefined(), ρ)::k)

      case Assign(op, Local(x), rhs) =>
        ρ.get(x) match {
          case Some(Loc(addr)) =>
            Co(Path(addr, Local(x)), σ, φ, EvalAssignRhs(op, rhs, ρ)::k)
          case None if x == "undefined" =>
            // The special global name "undefined" evaluates to "undefined".
            val loc = Path(FreshLoc().address, Undefined())
            Co(loc, σ.assign(loc, Undefined(), ρ), φ, EvalAssignRhs(op, rhs, ρ)::k)
          case None =>
            println(s"variable $x not found... residualizing")
            Co(Undefined(), σ, φ, k).MakeResidual(Local(x), ρ, EvalAssignRhs(op, rhs, ρ)::k)
        }

      case Assign(op, Index(a, i), rhs) =>
        Ev(a, ρ, σ, φ, EvalPropertyNameForSet(i, ρ)::EvalAssignRhs(op, rhs, ρ)::k)

      case IncDec(op, Local(x)) =>
        ρ.get(x) match {
          case Some(Loc(addr)) =>
            Co(Path(addr, Local(x)), σ, φ, DoIncDec(op, ρ)::k)
          case None if x == "undefined" =>
            // The special global name "undefined" evaluates to "undefined".
            val loc = Path(FreshLoc().address, Undefined())
            Co(loc, σ.assign(loc, Undefined(), ρ), φ, DoIncDec(op, ρ)::k)
          case None =>
            println(s"variable $x not found... residualizing")
            Co(Undefined(), σ, φ, k).MakeResidual(Local(x), ρ, DoIncDec(op, ρ)::k)
        }

      case IncDec(op, Index(a, i)) =>
        Ev(a, ρ, σ, φ, EvalPropertyNameForSet(i, ρ)::DoIncDec(op, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Variables. Just lookup the value. If not present, residualize.
      ////////////////////////////////////////////////////////////////

      case Local(x) =>
        ρ.get(x) match {
          case Some(Loc(addr)) =>
            σ.get(Loc(addr)) match {
              case Some(LocClosure(Loc(v))) =>
                Co(Path(v, Local(x)), σ, φ, k)
              case Some(ValClosure(v)) =>
                Co(v, σ, φ, k)
              case Some(ObjClosure(funObject, ρ1)) =>
                assert(false) // A local variable should never point directly to an object.
                Co(Undefined(), σ, φ, k).MakeResidual(Local(x), ρ, k)
              case Some(UnknownClosure()) | None =>
                Co(Undefined(), σ, φ, k).MakeResidual(Local(x), ρ, k)
            }

          case None if x == "undefined" =>
            // The special global name "undefined" evaluates to "undefined".
            Co(Undefined(), σ, φ, k)

          case None =>
            println(s"variable $x not found... residualizing")
            Co(Undefined(), σ, φ, k).MakeResidual(Local(x), ρ, k)
        }

      case Index(a, i) =>
        Ev(a, ρ, σ, φ, EvalPropertyNameForGet(i, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Special unary operators.
      ////////////////////////////////////////////////////////////////

      case Typeof(e) =>
        Ev(e, ρ, σ, φ, DoTypeof(ρ)::k)

      case Void(e) =>
        // void e just discards the value and evaluates to undefined
        Ev(e, ρ, σ, φ, FocusCont(Undefined())::k)

      ////////////////////////////////////////////////////////////////
      // Unary operators.
      ////////////////////////////////////////////////////////////////

      case Unary(op, e) =>
        Ev(e, ρ, σ, φ, DoUnaryOp(op, ρ)::k)

      ////////////////////////////////////////////////////////////////
      // Binary operators.
      ////////////////////////////////////////////////////////////////

      case Binary(op, e1, e2) =>
        Ev(e1, ρ, σ, φ, EvalBinaryOpRight(op, e2, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Calls.
      ////////////////////////////////////////////////////////////////

      // A method call "x.m()" passes "x" as "this"
      case Call(Index(e, m), args) =>
        Ev(e, ρ, σ, φ, EvalMethodProperty(m, args, ρ)::k)

      // A non-method call "f()" passes "window" as "this"
      case Call(fun, args) =>
        Ev(fun, ρ, σ, φ, EvalArgs(Prim("window"), args, ρ)::k)

      case NewCall(fun, args) =>
        Ev(fun, ρ, σ, φ, EvalArgsForNew(args, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case Return(Some(e)) =>
        Ev(e, ρ, σ, φ, DoReturn()::k)

      case Return(None) =>
        Co(Undefined(), σ, φ, DoReturn()::k)

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case Throw(e) =>
        Ev(e, ρ, σ, φ, DoThrow()::k)

      case TryCatch(e, cs) =>
        Ev(e, ρ, σ, φ, CatchFrame(cs, ρ)::k)

      case TryFinally(e, fin) =>
        Ev(e, ρ, σ, φ, FinallyFrame(fin, ρ)::k)



      case Delete(Index(a, i)) =>
        Ev(a, ρ, σ, φ, EvalPropertyNameForDel(i, ρ)::k)


      // Create an empty object
      // Initialize a non-empty object.
      case ObjectLit(Nil) =>
        val loc = Path(FreshLoc().address, ObjectLit(Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
        Co(loc, σ.assign(loc, v, ρ), φ, k)

      case ObjectLit(ps) =>
        val x = FreshVar()
        val seq = ps.foldLeft(Assign(None, Local(x), ObjectLit(Nil)): Exp) {
          case (seq, Property(prop, value, _, _)) =>
            Seq(seq, Assign(None, Index(Local(x), prop), value))
          case _ => ???
        }
        Ev(Seq(seq, Local(x)), ρ + (x -> FreshLoc()), σ, φ, k)

      // Put a lambda in the heap.
      case lam @ Lambda(xs, e) =>
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

      // Array literals desugar to objects
      case ArrayLit(es) =>
        val loc = Path(FreshLoc().address, NewCall(Prim("Array"), Num(es.length)::Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Array.prototype")), Nil, None, Nil)
        val x = FreshVar()
        val seq = es.zipWithIndex.foldLeft(Assign(None, Local(x), loc): Exp) {
          case (seq, (value, i)) =>
            Seq(seq, Assign(None, Index(Local(x), StringLit(i.toInt.toString)), value))
        }
        Ev(Seq(seq, Seq(Assign(None, Index(Local(x), StringLit("length")), Num(es.length)), Local(x))), ρ, σ.assign(loc, v, ρ), φ, k)

      ////////////////////////////////////////////////////////////////
      // Other cases.
      ////////////////////////////////////////////////////////////////

      // Don't implement with.
      case With(exp, body) =>
        val x = FreshVar()
        val a = Assign(None, Local(x), With(exp, body))
        Co(Undefined(), σ, φ, k).MakeResidual(With(exp, body), ρ, k)

      case _ =>
        Err("no rule for $this", this)

    }
  }

  def block(φ: List[Exp]): Exp = φ match {
    case Nil => Undefined()
    case φ::φs => φs.foldLeft(φ)(Seq)
  }

  case class Co(v: Val, σ: Store, φ: Effect, k: Cont) extends State {
    require(v.isValueOrResidual, s"$v is not a value or residual")

    override def toString = s"""Co
  v = $v
  σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  φ = $φ
  k = ${k.mkString("[", "\n       ", "]")}"""

    def MakeResidual(e: Exp, ρ1: Env, k: Cont) = {
      // TODO: if a variable used in e is in ρ1, we have to generate an assignment to it.
      lazy val x = FreshVar()
      reify(e) match {
        case e: Val =>
          // Don't residualize values
          Co(e, σ, φ, k)
        case e @ Assign(op, lhs, rhs) =>
          println(s"simulating $e")
          println(s"initial σ = $σ")
          println(s"  final σ = ${Eval.simulateStore(e)(σ, ρ1)}")
          Co(Residual(x), Eval.simulateStore(e)(σ, ρ1), φ.extend(x::Nil, Seq(e, Assign(None, Residual(x), lhs))), k)
        case e =>
          println(s"simulating $e")
          println(s"initial σ = $σ")
          println(s"  final σ = ${Eval.simulateStore(e)(σ, ρ1)}")
          Co(Residual(x), Eval.simulateStore(e)(σ, ρ1), φ.extend(x::Nil, Assign(None, Residual(x), e)), k)
      }
    }

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

    def doCall(fun: Val, thisValue: Val, args: List[Val], residual: Exp, result: Option[Val], ρ1: Env, σ: Store, k: Cont) = {
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
                case Some(result) =>
                  Ev(Seq(Seq(seq, body), result), ρ2, σ, φ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
                case None =>
                  Ev(Seq(seq, body), ρ2, σ, φ, CallFrame(ρ1)::k)  // use ρ1 in the call frame.. this is the env we pop to.
              }

            case Some(ValClosure(Prim(fun))) =>
              Eval.evalPrim(fun, args) match {
                case Some(e) =>
                  // Use Ev, not Co... the prim might be eval and return the expression to eval.
                  Ev(e, ρ1, σ, φ, k)
                case None =>
                  MakeResidual(residual, ρ1, k)
              }

            case _ =>
              MakeResidual(residual, ρ1, k)
          }
        case _ =>
          MakeResidual(residual, ρ1, k)
      }
    }

    def step = k match {
      // Done!
      case Nil => Halt(v, φ)

      case BranchCont(kt, kf, ρ)::k =>
        v match {
          case v @ CvtBool(true) => Co(v, σ, φ, kt ++ k)
          case v @ CvtBool(false) => Co(v, σ, φ, kf ++ k)
          case _ =>
            // If the result cannot be converted to a boolean, we residualize.
            // We first run the true branch, discarding all the effects accumulated so far
            // and simulating a true test on the store.
            // We then Reset the store, this time simulating a false test,
            // then run the false branch.
            // We then Merge the stores and effects, prepending the effects so far.

            // We have two options here.
            // - LONG_CONTINUATIONS.
            //   We run both continuations to the end of the program and then merge
            // - !LONG_CONTINUATIONS.
            //   We run both continuations to the join point, then merge
            // and merge the resulting states and effects.
            // We choose the latter because it yields a smaller residual
            // program, although the former might result in better
            // performance.

            val σ1 = extendWithCond(v, σ, ρ, true)
            val σ2 = extendWithCond(v, σ, ρ, false)

            val LONG_CONTINUATIONS = false

            if (LONG_CONTINUATIONS)
              Co(v, σ1, Machine.φ0, (kt ++ k) :+ Reset(v, σ2, φ, ρ, kf ++ k))
            else
              Co(v, σ1, Machine.φ0, kt ++ (Reset(v, σ2, φ, ρ, kf)::k))
        }

      case Reset(test, σ2, φ0, ρ0, kf)::k =>
        Co(test, σ2, Machine.φ0, kf ++ (Merge(v, σ, φ, test, φ0, ρ0)::k))

      case Merge(v1, σ1, φ1, test, φ0, ρ0)::k =>
        val v2 = v
        val σ2 = σ
        val φ2 = φ

        if (v1 == v2) {
          // If the values are the same, just use them.
          val φ = φ0.extend(φ1.vars ++ φ2.vars, IfElse(test, φ1.body, φ2.body))
          Co(v1, σ1.merge(σ2, ρ0), φ, k)
        }
        else {
          // Otherwise create a fresh residual variable
          // and then assign the values at the end of each branch.
          // cf. removing SSA.
          val x = FreshVar()
          val a1 = Assign(None, Residual(x), v1)
          val a2 = Assign(None, Residual(x), v2)

          val φ = φ0.extend(φ1.vars ++ φ2.vars, IfElse(test, Seq(φ1.body, a1), Seq(φ2.body, a2)))
          Co(Residual(x), σ1.merge(σ2, ρ0), φ, k)
        }

      case Breaking(None)::BreakFrame(_)::k =>
        Co(v, σ, φ, k)
      case Continuing(None)::ContinueFrame(_)::k =>
        Co(v, σ, φ, k)

      case Breaking(Some(x))::BreakFrame(Some(y))::k if x == y =>
        Co(v, σ, φ, k)
      case Continuing(Some(x))::ContinueFrame(Some(y))::k if x == y =>
        Co(v, σ, φ, k)

      case Breaking(label)::_::k =>
        Co(v, σ, φ, Breaking(label)::k)
      case Continuing(label)::_::k =>
        Co(v, σ, φ, Continuing(label)::k)

      // discard useless break and continue frames
      case BreakFrame(_)::k =>
        Co(v, σ, φ, k)
      case ContinueFrame(_)::k =>
        Co(v, σ, φ, k)

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      // Discard the value and evaluate the sequel.
      case SeqCont(s2, ρ1)::k =>
        Ev(s2, ρ1, σ, φ, k)

      // Change the focus
      case FocusCont(v2)::k =>
        Co(v2, σ, φ, k)

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, ρ1)::k =>
        val lhs = v
        Ev(rhs, ρ1, σ, φ, DoAssign(op, lhs, ρ1)::k)

      case DoAssign(None, lhs: Path, ρ1)::k =>
        // Normal assignment... the result is the rhs value
        Co(v, σ.assign(lhs, v, ρ1), φ, k)

      case DoAssign(Some(op), lhs: Path, ρ1)::k =>
        σ.get(Loc(lhs.address)) match {
          case Some(ValClosure(left)) =>
            val right = v
            Eval.evalOp(op, left, right) match {
              case Some(result) =>
                Co(result, σ.assign(lhs, result, ρ1), φ, k)
              case None =>
                MakeResidual(Assign(Some(op), lhs, right), ρ1, k)
            }
          case _ =>
            val rhs = v
            MakeResidual(Assign(Some(op), lhs, rhs), ρ1, k)
        }

      case DoAssign(op, lhs, ρ1)::k =>
        val rhs = v
        MakeResidual(Assign(op, lhs, rhs), ρ1, k)

      case DoIncDec(op, ρ1)::k =>
        v match {
          case loc @ Path(addr, path) =>
            σ.get(Loc(addr)) match {
              case Some(ValClosure(oldValue)) =>
                val binOp = op match {
                  case Prefix.++ => Binary.+
                  case Prefix.-- => Binary.-
                  case Postfix.++ => Binary.+
                  case Postfix.-- => Binary.-
                  case _ => ???
                }
                Eval.evalOp(binOp, oldValue, Num(1)) match {
                  case Some(newValue) =>
                    val resultValue = op match {
                      case Prefix.++ => newValue
                      case Prefix.-- => newValue
                      case Postfix.++ => oldValue
                      case Postfix.-- => oldValue
                      case _ => ???
                    }
                    Co(resultValue, σ.assign(loc, newValue, ρ1), φ, k)
                  case None =>
                    MakeResidual(IncDec(op, loc), ρ1, k)
                }
              case _ =>
                MakeResidual(IncDec(op, loc), ρ1, k)
            }

          case v =>
            MakeResidual(IncDec(op, v), ρ1, k)
        }

      case DoTypeof(ρ1)::k =>
        v match {
          case Num(v) =>
            Co(StringLit("number"), σ, φ, k)
          case Bool(v) =>
            Co(StringLit("boolean"), σ, φ, k)
          case StringLit(v) =>
            Co(StringLit("string"), σ, φ, k)
          case Undefined() =>
            Co(StringLit("undefined"), σ, φ, k)
          case Null() =>
            Co(StringLit("object"), σ, φ, k)
          case loc @ Path(addr, path) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, _, _, _, _), _)) =>
                Co(StringLit(typeof), σ, φ, k)
              case Some(ValClosure(v)) =>
                Co(v, σ, φ, DoTypeof(ρ1)::k)
              case Some(LocClosure(Loc(v))) =>
                // The address of an object
                Co(Path(v, path), σ, φ, DoTypeof(ρ1)::k)
              case Some(UnknownClosure()) =>
                MakeResidual(Typeof(path), ρ1, k)
              case None =>
                MakeResidual(Typeof(path), ρ1, k)
            }
          case e =>
            MakeResidual(Typeof(e), ρ1, k)
        }

      case DoUnaryOp(op, ρ1)::k =>
        (op, v) match {
          case (Prefix.!, CvtBool(v)) =>
            Co(Bool(!v), σ, φ, k)
          case (Prefix.~, CvtNum(v)) =>
            Co(Num(~v.toLong), σ, φ, k)
          case (Prefix.+, CvtNum(v)) =>
            Co(Num(+v), σ, φ, k)
          case (Prefix.-, CvtNum(v)) =>
            Co(Num(-v), σ, φ, k)
          case (op, v) =>
            MakeResidual(Unary(op, v), ρ1, k)
        }

      case EvalBinaryOpRight(op, e2, ρ1)::k =>
        (op, v) match {
          // Short-circuit && and ||
          case (Binary.&&, v @ CvtBool(false)) =>
            Co(v, σ, φ, k)
          case (Binary.||, v @ CvtBool(true)) =>
            Co(v, σ, φ, k)
          case (op, v) =>
            Ev(e2, ρ1, σ, φ, DoBinaryOp(op, v, ρ1)::k)
        }

      case DoBinaryOp(op, v1, ρ1)::k =>
        (op, v1, v) match {
          case (Binary.IN, i, loc @ Path(addr, path)) =>
            // Does the property i exist in loc?
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(_, _)) =>
                Eval.getPropertyAddress(Loc(addr), i, σ) match {
                  case Some(v) =>
                    Co(Bool(true), σ, φ, k)
                  case None =>
                    Co(Bool(false), σ, φ, k)
                }
              case _ =>
                MakeResidual(Binary(Binary.IN, i, path), ρ1, k)
            }
          case (Binary.INSTANCEOF, Null(), Path(_, _)) =>
            Co(Bool(false), σ, φ, k)
          case (Binary.INSTANCEOF, Undefined(), Path(_, _)) =>
            Co(Bool(false), σ, φ, k)
          case (Binary.INSTANCEOF, v1 @ Path(addr1, path1), v2 @ Path(addr2, path2)) =>
            // x instanceof y
            // ==
            // x.__proto__ === y.prototype
            val result = for {
              ObjClosure(FunObject(_, v1protoLoc, _, _, _), _) <- σ.get(Loc(addr1))
              v2protoLoc <- Eval.getPropertyAddress(Loc(addr2), StringLit("prototype"), σ)
            } yield (v1protoLoc, v2protoLoc)

            result match {
              case Some((proto1, proto2)) if proto1 == proto2 =>
                Co(Bool(true), σ, φ, k)
              case None =>
                MakeResidual(Binary(Binary.INSTANCEOF, path1, path2), ρ1, k)
            }

          case (op, v1, v2) =>
            Eval.evalOp(op, v1, v2) match {
              case Some(v) => Co(v, σ, φ, k)
              case None => MakeResidual(Binary(op, v1, v2), ρ1, k)
            }
        }


      ////////////////////////////////////////////////////////////////
      // Calls and lambda.
      // FIXME
      // Environment handling is completely broken here.
      // See the old SCSC implementation.
      ////////////////////////////////////////////////////////////////

      case EvalMethodProperty(m, es, ρ1)::k =>
        val thisValue = v
        Ev(m, ρ1, σ, φ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)

      case EvalArgs(thisValue, Nil, ρ1)::k =>
        val fun = v
        doCall(fun, thisValue, Nil, Call(fun, Nil), None, ρ1, σ, k)

      case EvalArgs(thisValue, arg::args, ρ1)::k =>
        val fun = v
        Ev(arg, ρ1, σ, φ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)

      case EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k =>
        Ev(arg, ρ1, σ, φ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)

      case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
        doCall(fun, thisValue, done :+ v, Call(fun, done :+ v), None, ρ1, σ, k)

      ///////////////////////////////////////////////////////////////, k/
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k =>
        Co(Undefined(), σ, φ, Returning(v)::k)

      // Once we hit the call frame, evaluate the return value.
      case Returning(v1)::CallFrame(ρ1)::k =>
        Co(v1, σ, φ, k)

      // If we hit a reset frame, we had the following situation:
      // f() { if (...) return 1 else ... }
      // rather than residualizing the return, what we do is extend
      // the continuation.

      // Push reset continuations out past the call frame.
      case Returning(v1)::Reset(test, σ2, φ0, ρ0, kf)::k2::k =>
        Co(v, σ, φ, Returning(v1)::k2::Reset(test, σ2, φ0, ρ0, kf :+ k2)::k)

      case Returning(v1)::_::k =>
        Co(v, σ, φ, Returning(v1)::k)

      // If we run off the end of the function body, act like we returned normally.
      case CallFrame(ρ1)::k =>
        Co(v, σ, φ, k)


      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k =>
        Co(Undefined(), σ, φ, Throwing(v)::k)

      // If we're throwing and we hit a try block,
      // evaluate the finally block and rethrow.
      case Throwing(e)::FinallyFrame(fin, ρ1)::k =>
        Ev(fin, ρ1, σ, φ, Throwing(e)::k)

      case Throwing(e)::_::k =>
        Co(v, σ, φ, Throwing(e)::k)

      // Run the finally block, if any. Then restore the value.
      case FinallyFrame(fin, ρ1)::k =>
        Ev(fin, ρ1, σ, φ, FocusCont(v)::k)

      ////////////////////////////////////////////////////////////////
      // Objects and arrays.
      ////////////////////////////////////////////////////////////////

      // new Point(x, y)
      // creates a new empty object
      // binds the object to this
      // sets this.__proto__ to Point.prototype
      // calls the Point function

      case EvalArgsForNew(Nil, ρ1)::k =>
        val fun = v
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, φ, InitProto(fun, Nil, ρ1)::k)

      case EvalArgsForNew(arg::args, ρ1)::k =>
        val fun = v
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForNew(fun, args, Nil, ρ1)::k)

      case EvalMoreArgsForNew(fun, arg::args, done, ρ1)::k =>
        Ev(arg, ρ1, σ, φ, EvalMoreArgsForNew(fun, args, done :+ v, ρ1)::k)

      case EvalMoreArgsForNew(fun, Nil, done, ρ1)::k =>
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, φ, InitProto(fun, done :+ v, ρ1)::k)

      case InitProto(fun, args, ρ1)::k =>
        val proto = v

        // Put the object in the heap
        val loc = Path(FreshLoc().address, NewCall(fun, args))

        val protoLoc = proto match {
          case Path(a, p) => Some(Loc(a))
          case Prim(x) => Some(Eval.getPrimAddress(Prim(x)))
          case _ => None
        }

        protoLoc match {
          case Some(protoLoc) =>
            val obj = FunObject("object", protoLoc, Nil, None, Nil)
            doCall(fun, loc, args, NewCall(fun, args), Some(loc), ρ1, σ.assign(loc, obj, ρ1), k)

          case None =>
            MakeResidual(loc.path, ρ1, k)
        }

      case EvalPropertyNameForDel(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, φ, DoDeleteProperty(a, ρ1)::k)

      case DoDeleteProperty(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, p), i @ CvtString(istr)) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
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
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(a, σ, φ, k)
              case Some(UnknownClosure()) | None =>
                MakeResidual(Delete(Index(a, i)), ρ1, k)
            }

          case (a, i) =>
            MakeResidual(Delete(Index(a, i)), ρ1, k)
        }

      case EvalPropertyNameForSet(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, φ, GetPropertyAddressOrCreate(a, ρ1)::k)

      case GetPropertyAddressOrCreate(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, path), i @ CvtString(istr)) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
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
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(Undefined(), σ, φ, k)
              case Some(UnknownClosure()) | None =>
                MakeResidual(Index(a, i), ρ1, k)
            }
          case (a, i) =>
            MakeResidual(Index(a, i), ρ1, k)
        }

      case EvalPropertyNameForGet(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, φ, GetProperty(a, ρ1)::k)

      // restrict the property to values to ensure == during property lookup works correctly
      // otherwise, a[f()] will result in undefined rather than a reified access
      case GetProperty(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, path), i) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
                println(s"looking for $i in $props")
                val propAddr = props collectFirst {
                  case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Some(Bool(true)) => v
                }
                println(s"looking for $i in $props: found $propAddr")
                propAddr match {
                  case Some(loc) =>
                    println(s"looking for $i in $props: loading $loc")
                    σ.get(loc) match {
                      case Some(LocClosure(Loc(v))) =>
                        Co(Path(v, Index(path, i)), σ, φ, k)
                      case Some(ValClosure(v)) =>
                        Co(v, σ, φ, k)
                      case Some(ObjClosure(funObject, ρ2)) =>
                        MakeResidual(Index(path, i), ρ1, k)
                      case Some(UnknownClosure()) | None =>
                        MakeResidual(Index(path, i), ρ1, k)
                    }
                  case None =>
                    if (body != None && Eval.evalOp(Binary.==, StringLit("length"), i) == Some(Bool(true))) {
                      Co(Num(xs.length), σ, φ, k)
                    }
                    else {
                      // Try the prototype.
                      // If not found, return undefined.
                      Co(i, σ, φ, GetProperty(Path(proto.address, path), ρ1)::k)
                    }
                }
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(Undefined(), σ, φ, k)
              case Some(UnknownClosure()) | None =>
                MakeResidual(Index(a, i), ρ1, k)
            }
          case (a, i) =>
            MakeResidual(Index(a, i), ρ1, k)
        }

      /////////////////
      // No more cases....
      /////////////////
    }
  }
}
