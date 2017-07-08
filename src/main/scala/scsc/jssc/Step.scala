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

  // We implement the machine in "apply, eval, continue" form, following:
  // Olivier Danvy. An Analytical Approach to Program as Data Objects.
  // DSc thesis, Department of Computer Science, Aarhus University, 2006.

  sealed trait State {
    def step: State
  }

  // An Ev state dispatches on the expression, shifting the focus
  // to a subexpression.
  // A Co state has a value in the focus and dispatches on the continuation.
  case class Ev(e: Exp, ρ: Env, σ: Store, k: Cont) extends State {
    override def toString = s"""Ev
  e = $e
  ρ = ${ρ.toVector.sortBy(_._1).mkString("{", "\n       ", "}")}
  σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  k = ${k.mkString("[", "\n       ", "]")}"""

    def step = e match {

      // For any value, just run the continuation.
      case Value(v) => Co(v, σ, k)
      case v @ Residual(e) => Co(v, σ, k)

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
            case _: Lambda | _: Residual | _: Scope =>
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

        // MakeTrees ensures builds the tree so that function bindings
        // are evaluated first, so we don't have to initialize them explicitly.
        // Also all bindings should be either to lambdas or to undefined.
        Ev(s, ρ1, σ1, RebuildLet(bindings.toList.map(_._1), bindings.toList.map(_._2), ρ)::RebuildScope(ρ1)::k)

      ////////////////////////////////////////////////////////////////
      // Conditionals
      // ? : and if/else are handled identically, duplicating code
      ////////////////////////////////////////////////////////////////

      // if e then s1 else s2
      case IfElse(e, s1, s2) =>
        Ev(e, ρ, σ, BranchCont(SeqCont(s1, ρ)::Nil,
                                 SeqCont(s2, ρ)::Nil,
                                 RebuildIfElseTest(s1, s2, ρ)::Nil,
                                 ρ)::k)

      // e ? s1 : s2
      case Cond(e, s1, s2) =>
        Ev(e, ρ, σ, BranchCont(SeqCont(s1, ρ)::Nil,
                                 SeqCont(s2, ρ)::Nil,
                                 RebuildCondTest(s1, s2, ρ)::Nil,
                                 ρ)::k)

      ////////////////////////////////////////////////////////////////
      // Loops.
      // This is very much complicated by break and continue.
      // Otherwise we could just desugar everything into IfElse,
      // unrolling the loop and letting generlization handle
      // termination detection and rebuilding the loop.
      ////////////////////////////////////////////////////////////////

      case For(label, Empty(), test, iter, body) =>
        Ev(test, ρ, σ, BranchCont(
                         SeqCont(body, ρ)::ContinueFrame(label)::SeqCont(Seq(iter, For(label, Empty(), test, iter, body)), ρ)::BreakFrame(label)::Nil,
                         FocusCont(Undefined())::Nil,
                         RebuildForTest(label, test, iter, body, ρ)::Nil,
                         ρ)::k)

      case For(label, init, test, iter, body) =>
        Ev(Seq(init, For(label, Empty(), test, iter, body)), ρ, σ, k)


      // do body while test
      case DoWhile(label, body, test) =>
        Ev(body, ρ, σ, ContinueFrame(label)::SeqCont(While(label, test, body), ρ)::BreakFrame(label)::k)

      // just desugar into a for loop
      case While(label, test, body) =>
        Ev(For(label, Empty(), test, Empty(), body), ρ, σ, k)

      case ForIn(label, init, iter, body) =>
        // FIXME: implement!
        // Eval iter to get an object.
        // Loop through all the properties of that object.
        Ev(body, ρ, σ, RebuildForIn(label, init, iter, ρ)::k)

      // Break and continue.

      case Break(label) =>
        Co(Undefined(), σ, Breaking(label)::k)

      case Continue(label) =>
        Co(Undefined(), σ, Continuing(label)::k)

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      case Empty() =>
        Co(Undefined(), σ, k)

      // reassociate to reduce the size of the residual.
      case Seq(Seq(s1, s2), s3) =>
        Ev(Seq(s1, Seq(s2, s3)), ρ, σ, k)

      case Seq(s1, s2) =>
        Ev(s1, ρ, σ, SeqCont(s2, ρ)::k)

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
              Assign(None, LocalAddr(x), lambdaLoc),
              Assign(None, IndexAddr(lambdaLoc, StringLit("name")), StringLit(x)),
              Assign(None, IndexAddr(lambdaLoc, StringLit("length")), Num(xs.length)),
              Assign(None, IndexAddr(lambdaLoc, StringLit("prototype")), protoLoc)
            )

            val s2 = ass.reverse.foldRight(Undefined(): Exp) {
              case (e, rest) => Seq(e, rest)
            }

            val σ2 = σ.assign(lambdaLoc, funObj, ρ).assign(protoLoc, proto, ρ)

            Ev(s2, ρ, σ2, k)
          case None =>
            Co(e, σ, Fail(s"variable $x not found")::k)
        }

      case VarDef(x, e) =>
        ρ.get(x) match {
          case Some(loc) =>
            Ev(e, ρ, σ, DoAssign(None, Path(loc.address, Local(x)), ρ)::RebuildLet(x::Nil, Undefined()::Nil, ρ)::k)
          case None =>
            Co(e, σ, Fail(s"variable $x not found")::k)
        }

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      // we can assign to undefined. yep, that's right.
      case Assign(None, Undefined(), rhs) =>
        Ev(rhs, ρ, σ, k)

      case Assign(Some(op), Undefined(), rhs) =>
        Ev(rhs, ρ, σ, DoBinaryOp(op, Undefined(), ρ)::k)

      case Assign(op, lhs, rhs) =>
        Ev(lhs, ρ, σ, EvalAssignRhs(op, rhs, lhs, ρ)::k)

      case IncDec(op, lhs) =>
        Ev(lhs, ρ, σ, DoIncDec(op, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Variables. Just lookup the value. If not present, residualize.
      ////////////////////////////////////////////////////////////////

      case LocalAddr(x) =>
        ρ.get(x) match {
          case Some(Loc(addr)) =>
            Co(Path(addr, LocalAddr(x)), σ, k)
          case None if x == "undefined" =>
            // The special global name "undefined" evaluates to "undefined".
            val loc = Path(FreshLoc().address, Undefined())
            Co(loc, σ.assign(loc, Undefined(), ρ), k)
          case None =>
            println(s"variable $x not found... residualizing")
            Co(Residual(Local(x)), σ, k)
        }

      case Local(x) =>
        Ev(LocalAddr(x), ρ, σ, LoadCont(ρ)::k)

      case Index(a, i) =>
        Ev(a, ρ, σ, EvalPropertyNameForGet(i, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Special unary operators.
      ////////////////////////////////////////////////////////////////

      case Typeof(e) =>
        Ev(e, ρ, σ, DoTypeof(ρ)::k)

      case Void(e) =>
        // void e just discards the value and evaluates to undefined
        Ev(e, ρ, σ, FocusCont(Undefined())::k)

      ////////////////////////////////////////////////////////////////
      // Unary operators.
      ////////////////////////////////////////////////////////////////

      case Unary(op, e) =>
        Ev(e, ρ, σ, DoUnaryOp(op, ρ)::k)

      ////////////////////////////////////////////////////////////////
      // Binary operators.
      ////////////////////////////////////////////////////////////////

      case Binary(op, e1, e2) =>
        Ev(e1, ρ, σ, EvalBinaryOpRight(op, e2, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Calls.
      ////////////////////////////////////////////////////////////////

      // A method call "x.m()" passes "x" as "this"
      case Call(Index(e, m), args) =>
        Ev(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)

      case Call(IndexAddr(e, m), args) =>
        Ev(e, ρ, σ, EvalMethodProperty(m, args, ρ)::k)

      // A non-method call "f()" passes "window" as "this"
      case Call(fun, args) =>
        Ev(fun, ρ, σ, EvalArgs(Prim("window"), args, ρ)::k)

      case NewCall(fun, args) =>
        Ev(fun, ρ, σ, EvalArgsForNew(args, ρ)::k)


      ////////////////////////////////////////////////////////////////
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case Return(Some(e)) =>
        Ev(e, ρ, σ, DoReturn()::k)

      case Return(None) =>
        Co(Undefined(), σ, DoReturn()::k)

      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case Throw(e) =>
        Ev(e, ρ, σ, DoThrow()::k)

      case TryCatch(e, cs) =>
        Ev(e, ρ, σ, CatchFrame(cs, ρ)::k)

      case TryFinally(e, fin) =>
        Ev(e, ρ, σ, FinallyFrame(fin, ρ)::k)



      case Delete(IndexAddr(a, i)) =>
        Ev(a, ρ, σ, EvalPropertyNameForDel(i, ρ)::k)

      case IndexAddr(a, i) =>
        Ev(a, ρ, σ, EvalPropertyNameForSet(i, ρ)::k)


      // Create an empty object
      // Initialize a non-empty object.
      case ObjectLit(Nil) =>
        val loc = Path(FreshLoc().address, ObjectLit(Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Object.prototype")), Nil, None, Nil)
        Co(loc, σ.assign(loc, v, ρ), k)

      case ObjectLit(ps) =>
        val x = FreshVar()
        val seq = ps.foldLeft(Assign(None, LocalAddr(x), ObjectLit(Nil)): Exp) {
          case (seq, Property(prop, value, _, _)) =>
            Seq(seq, Assign(None, IndexAddr(Local(x), prop), value))
          case _ => ???
        }
        Ev(Seq(seq, Local(x)), ρ + (x -> FreshLoc()), σ, k)

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
        Co(loc, σ.assign(xloc, loc, ρ2).assign(loc, v, ρ2).assign(protoLoc, v2, ρ2), RebuildLet(x::Nil, Undefined()::Nil, ρ2)::k)

      // Array literals desugar to objects
      case ArrayLit(es) =>
        val loc = Path(FreshLoc().address, NewCall(Prim("Array"), Num(es.length)::Nil))
        val v = FunObject("object", Eval.getPrimAddress(Prim("Array.prototype")), Nil, None, Nil)
        val x = FreshVar()
        val seq = es.zipWithIndex.foldLeft(Assign(None, LocalAddr(x), loc): Exp) {
          case (seq, (value, i)) =>
            Seq(seq, Assign(None, IndexAddr(Local(x), StringLit(i.toInt.toString)), value))
        }
        Ev(Seq(seq, Seq(Assign(None, IndexAddr(Local(x), StringLit("length")), Num(es.length)), Local(x))), ρ, σ.assign(loc, v, ρ), k)

      ////////////////////////////////////////////////////////////////
      // Other cases.
      ////////////////////////////////////////////////////////////////

      // Don't implement with.
      case With(exp, body) =>
        reify(With(exp, body))(σ, ρ) match {
          case v =>
            Co(v, Eval.simulateStore(v)(σ, ρ), k)
        }


      case _ =>
        Co(e, σ, Fail("no rule for $this")::k)

    }
  }

  case class Co(v: Exp, σ: Store, k: Cont) extends State {
    require(v.isValueOrResidual)

    override def toString = s"""Co
  v = $v
  σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  k = ${k.mkString("[", "\n       ", "]")}"""

    def step = k match {
      // Done!
      case Nil => this

      // Fail!
      case Fail(_)::k => this

      case RebuildScope(ρ1)::k =>
        v match {
          case Residual(e) => Co(Residual(Scope(e)), σ, k)
          case Value(v) => Co(v, σ, k)
        }

      case BranchCont(kt, kf, kr, ρ)::k =>
        v match {
          case v @ CvtBool(true) => Co(v, σ, kt ++ k)
          case v @ CvtBool(false) => Co(v, σ, kf ++ k)
          case Residual(e) => Co(v, σ, kr ++ k)
          case Value(e) =>
            // this should not happen
            reify(e)(σ, ρ) match {
              case e =>
                Co(e, Eval.simulateStore(e)(σ, ρ), kr ++ k)
            }
        }

      // Rebuilding ? : and if-else nodes.
      // The logic is duplicated.

      // Evaluate the test to a (residual) value.
      // Save the store and evaluate the true branch.
      case RebuildCondTest(s1, s2, ρ0)::k =>
        val σAfterTest = σ
        val test = v
        val σ1 = extendWithCond(test, σAfterTest, ρ0, true)
        Ev(s1, ρ0, σ1, RebuildCondTrue(test, s2, σAfterTest, ρ0)::k)

      // Save the evaluated true branch and the store after the true branch.
      // Restore the post-test store and evaluate the false branch.
      case RebuildCondTrue(test, s2, σAfterTest, ρ0)::k =>
        val s1 = v
        val σ1 = σ
        reify(s1)(σ1, ρ0) match {
          case s1 =>
            val σ = extendWithCond(test, σAfterTest, ρ0, false)
            Ev(s2, ρ0, σ, RebuildCondFalse(test, s1, σ1, ρ0)::k)
        }

      // Rebuild and merge the post-true and post-false stores.
      case RebuildCondFalse(test, s1, σ1, ρ0)::k =>
        val s2 = v
        val σ2 = σ
        reify(s2)(σ2, ρ0) match {
          case s2 =>
            Co(Residual(Cond(test, s1, s2)), σ1.merge(σ2, ρ0), k)
        }

      case RebuildIfElseTest(s1, s2, ρ0)::k =>
        val σAfterTest = σ
        val test = v
        val σ1 = extendWithCond(test, σAfterTest, ρ0, true)
        Ev(s1, ρ0, σ1, RebuildIfElseTrue(test, s2, σAfterTest, ρ0)::k)

      // Save the evaluated true branch and the store after the true branch.
      // Restore the post-test store and evaluate the false branch.
      case RebuildIfElseTrue(test, s2, σAfterTest, ρ0)::k =>
        val s1 = v
        val σ1 = σ
        reify(s1)(σ1, ρ0) match {
          case s1 =>
            val σ = extendWithCond(test, σAfterTest, ρ0, false)
            Ev(s2, ρ0, σ, RebuildIfElseFalse(test, s1, σ1, ρ0)::k)
        }

      // Rebuild and merge the post-true and post-false stores.
      case RebuildIfElseFalse(test, s1, σ1, ρ0)::k =>
        val s2 = v
        val σ2 = σ
        reify(s2)(σ2, ρ0) match {
          case s2 =>
            Co(Residual(IfElse(test, s1, s2)), σ1.merge(σ2, ρ0), k)
        }

      case RebuildForIn(label, init, iter, ρ1)::k =>
        val body = v
        reify(ForIn(label, init, iter, body))(σ, ρ1) match {
          case s =>
            Co(s, Eval.simulateStore(s)(σ, ρ1), k)
        }

      case RebuildForTest(label0, test0, iter0, body0, ρ1)::k =>
        val test = v
        Ev(body0, ρ1, σ, RebuildForBody(label0, test, test0, iter0, body0, ρ1)::k)

      case RebuildForBody(label0, test1, test0, iter0, body0, ρ1)::k =>
        val body1 = v
        Ev(iter0, ρ1, σ, RebuildForIter(label0, body1, test1, test0, iter0, body0, ρ1)::k)

      case RebuildForIter(label, body1, test1, test0, Empty(), body0, ρ1)::k =>
        val iter1 = v
        reify(IfElse(test1, Seq(body1, Seq(iter1, While(label, test0, body0))), Undefined()))(σ, ρ1) match {
          case s =>
            Co(s, Eval.simulateStore(s)(σ, ρ1), k)
        }

      case RebuildForIter(label, body1, test1, test0, iter0, body0, ρ1)::k =>
        val iter1 = v
        reify(IfElse(test1, Seq(body1, Seq(iter1, For(label, Empty(), test0, iter0, body0))), Undefined()))(σ, ρ1) match {
          case s =>
            Co(s, Eval.simulateStore(s)(σ, ρ1), k)
        }

      case Breaking(None)::BreakFrame(_)::k =>
        Co(v, σ, k)
      case Continuing(None)::ContinueFrame(_)::k =>
        Co(v, σ, k)

      case Breaking(Some(x))::BreakFrame(Some(y))::k if x == y =>
        Co(v, σ, k)
      case Continuing(Some(x))::ContinueFrame(Some(y))::k if x == y =>
        Co(v, σ, k)

      // If we hit a rebuild continuation, we must run it, passing in v
      // (which is either undefined or a residual) to the rebuild continuation
      case Breaking(label)::(a: RebuildCont)::k =>
        Co(v, σ, a::Breaking(label)::k)
      case Continuing(label)::(a: RebuildCont)::k =>
        Co(v, σ, a::Continuing(label)::k)

      case Breaking(label)::_::k =>
        Co(v, σ, Breaking(label)::k)
      case Continuing(label)::_::k =>
        Co(v, σ, Continuing(label)::k)

      // discard useless break and continue frames
      case BreakFrame(_)::k =>
        Co(v, σ, k)
      case ContinueFrame(_)::k =>
        Co(v, σ, k)

      ////////////////////////////////////////////////////////////////
      // Blocks.
      ////////////////////////////////////////////////////////////////

      case SeqCont(s2, ρ1)::k =>
        v match {
          case Residual(s1) =>
            Ev(s2, ρ1, σ, RebuildSeq(s1, ρ1)::k)
          case Value(_) =>
            // Discard the value and evaluate the sequel.
            Ev(s2, ρ1, σ, k)
        }

      // Change the focus
      case FocusCont(v2)::k =>
        Co(v2, σ, k)

      case RebuildSeq(s1, ρ1)::k =>
        v match {
          case Value(s2) =>
            reify(s2)(σ, ρ1) match {
              case s2 =>
                Co(Residual(Seq(s1, s2)), σ, k)
            }
          case Residual(s2) =>
            Co(Residual(Seq(s1, s2)), σ, k)
        }

      ////////////////////////////////////////////////////////////////
      // Definitions.
      ////////////////////////////////////////////////////////////////

      // case Σ(Residual(Assign(None, y, e)), ρ, σ, RebuildVarDef(x, ρ1)::k) if (x == y) =>
      //   Σ(Residual(VarDef(x, e)), ρ1, σ, k)
      // case Σ(Residual(v), ρ, σ, RebuildVarDef(x, ρ1)::k) if (fv(v) contains x) =>
      //   Σ(Residual(VarDef(x, v)), ρ1, σ, k)
      // case Σ(Residual(v), ρ, σ, RebuildVarDef(x, ρ1)::k) =>
      //   Σ(Residual(v), ρ1, σ, k)
      // case Σ(Value(v), ρ, σ, RebuildVarDef(x, ρ1)::k) =>
      //   Σ(Undefined(), ρ1, σ, k)

      ////////////////////////////////////////////////////////////////
      // Assignment.
      ////////////////////////////////////////////////////////////////

      case EvalAssignRhs(op, rhs, _, ρ1)::k =>
        val lhs = v
        Ev(rhs, ρ1, σ, DoAssign(op, lhs, ρ1)::k)

      case DoAssign(None, lhs: Path, ρ1)::k =>
        v match {
          case Value(rhs) =>
            // Normal assignment... the result is the rhs value
            Co(rhs, σ.assign(lhs, rhs, ρ1), k)

          case Residual(rhs) =>
            // residualize the assignment
            // and update the store with the residual path
            // or maybe just map the lhs to nothing forcing
            // it to get residualized as the path every time?
            Co(Residual(Assign(None, lhs, rhs)), σ.assign(lhs, Residual(lhs.path), ρ1), k)
        }

      case DoAssign(Some(op), lhs: Path, ρ1)::k =>
        v match {
          case Value(rhs) =>
            σ.get(Loc(lhs.address)) match {
              case Some(ValClosure(left)) =>
                val right = rhs
                val v = Eval.evalOp(op, left, right)
                Co(v, σ.assign(lhs, v, ρ1), k)
              case _ =>
                Co(Residual(Assign(Some(op), lhs, rhs)), σ.assign(lhs, Residual(lhs.path), ρ1), k)
            }

          case Residual(rhs) =>
            // residualize the assignment
            // and update the store with the residual path
            // or maybe just map the lhs to nothing forcing
            // it to get residualized as the path every time?
            Co(Residual(Assign(Some(op), lhs, rhs)), σ.assign(lhs, Residual(lhs.path), ρ1), k)
        }

      case DoAssign(op, lhs, ρ1)::k =>
        val rhs = v

        reify(lhs)(σ, ρ1) match {
          case lhs =>
            Co(Residual(Assign(op, lhs, rhs)), Eval.simulateStore(Assign(op, lhs, rhs))(σ, ρ1), k)
        }

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
                val newValue = Eval.evalOp(binOp, oldValue, Num(1))
                val v = op match {
                  case Prefix.++ => newValue
                  case Prefix.-- => newValue
                  case Postfix.++ => oldValue
                  case Postfix.-- => oldValue
                  case _ => ???
                }
                Co(v, σ.assign(loc, newValue, ρ1), k)
              case _ =>
                Co(Residual(IncDec(op, path)), Eval.simulateStore(IncDec(op, path))(σ, ρ1), k)
            }

          case Value(e) =>
            reify(e)(σ, ρ1) match {
              case e =>
                Co(Residual(IncDec(op, e)), Eval.simulateStore(IncDec(op, e))(σ, ρ1), k)
            }

          case Residual(e) =>
            Co(Residual(IncDec(op, e)), Eval.simulateStore(IncDec(op, e))(σ, ρ1), k)
        }


      case LoadCont(ρ1)::k =>
        v match {
          case loc @ Path(addr, path) =>
            σ.get(Loc(addr)) match {
              case Some(LocClosure(Loc(v))) =>
                Co(Path(v, path), σ, k)
              case Some(ValClosure(v)) =>
                Co(v, σ, k)
              case Some(ObjClosure(funObject, ρ2)) =>
                Co(Residual(path), σ, k)
              case Some(UnknownClosure()) =>
                Co(Residual(path), σ, k)
              case None =>
                Co(loc, σ, Fail(s"could not load location $loc")::k)
            }

          case Undefined() =>
            Co(Undefined(), σ, k)

          case Residual(e) =>
            Co(Residual(e), σ, k)

          case e =>
            val v = reify(e)(σ, ρ1)
            Co(v, Eval.simulateStore(v)(σ, ρ1), k)
        }

      case DoTypeof(ρ1)::k =>
        v match {
          case Num(v) =>
            Co(StringLit("number"), σ, k)
          case Bool(v) =>
            Co(StringLit("boolean"), σ, k)
          case StringLit(v) =>
            Co(StringLit("string"), σ, k)
          case Undefined() =>
            Co(StringLit("undefined"), σ, k)
          case Null() =>
            Co(StringLit("object"), σ, k)
          case loc @ Path(addr, path) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, _, _, _, _), _)) =>
                Co(StringLit(typeof), σ, k)
              case Some(ValClosure(v)) =>
                Co(v, σ, DoTypeof(ρ1)::k)
              case Some(LocClosure(Loc(v))) =>
                // The address of an object
                Co(Path(v, path), σ, DoTypeof(ρ1)::k)
              case Some(UnknownClosure()) =>
                Co(Residual(Typeof(path)), σ, k)
              case None =>
                Co(Residual(Typeof(path)), σ, k)
            }
          case e =>
            val v = reify(Typeof(e))(σ, ρ1)
            Co(v, Eval.simulateStore(v)(σ, ρ1), k)
        }

      case DoUnaryOp(op, ρ1)::k =>
        (op, v) match {
          case (Prefix.!, CvtBool(v)) =>
            Co(Bool(!v), σ, k)
          case (Prefix.~, CvtNum(v)) =>
            Co(Num(~v.toLong), σ, k)
          case (Prefix.+, CvtNum(v)) =>
            Co(Num(+v), σ, k)
          case (Prefix.-, CvtNum(v)) =>
            Co(Num(-v), σ, k)
          case (op, Value(v)) =>
            reify(v)(σ, ρ1) match {
              case v =>
                Co(Residual(Unary(op, v)), Eval.simulateStore(Unary(op, v))(σ, ρ1), k)
            }
          case (op, Residual(v)) =>
            Co(Residual(Unary(op, v)), σ, k)
        }

      case EvalBinaryOpRight(op, e2, ρ1)::k =>
        (op, v) match {
          // Short-circuit && and ||
          case (Binary.&&, v @ CvtBool(false)) =>
            Co(v, σ, k)
          case (Binary.||, v @ CvtBool(true)) =>
            Co(v, σ, k)
          case (op, v) =>
            Ev(e2, ρ1, σ, DoBinaryOp(op, v, ρ1)::k)
        }

      case DoBinaryOp(op, v1, ρ1)::k =>
        (op, v1, v) match {
          case (Binary.IN, Value(i), loc @ Path(addr, path)) =>
            // Does the property i exist in loc?
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(_, _)) =>
                Eval.getPropertyAddress(Loc(addr), i, σ) match {
                  case Some(v) =>
                    Co(Bool(true), σ, k)
                  case None =>
                    Co(Bool(false), σ, k)
                }
              case _ =>
                Co(Residual(Binary(Binary.IN, i, path)), σ, k)
            }
          case (Binary.INSTANCEOF, Null(), Path(_, _)) =>
            Co(Bool(false), σ, k)
          case (Binary.INSTANCEOF, Undefined(), Path(_, _)) =>
            Co(Bool(false), σ, k)
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
                Co(Bool(true), σ, k)
              case None =>
                Co(Residual(Binary(Binary.INSTANCEOF, path1, path2)), Eval.simulateStore(v)(σ, ρ1), k)
            }

          case (op, v1, v2) =>
            Co(Eval.evalOp(op, v1, v2), σ, k)
        }


      ////////////////////////////////////////////////////////////////
      // Calls and lambda.
      // FIXME
      // Environment handling is completely broken here.
      // See the old SCSC implementation.
      ////////////////////////////////////////////////////////////////

      case EvalMethodProperty(m, es, ρ1)::k =>
        val thisValue = v
        Ev(m, ρ1, σ, GetProperty(thisValue, ρ1)::EvalArgs(thisValue, es, ρ1)::k)

      case EvalArgs(thisValue, Nil, ρ1)::k =>
        val fun = v
        Co(Undefined(), σ, DoCall(fun, thisValue, Nil, Call(fun, Nil), ρ1)::k)

      case EvalArgs(thisValue, arg::args, ρ1)::k =>
        val fun = v
        Ev(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, Nil, ρ1)::k)

      case EvalMoreArgs(fun, thisValue, arg::args, done, ρ1)::k =>
        Ev(arg, ρ1, σ, EvalMoreArgs(fun, thisValue, args, done :+ v, ρ1)::k)

      case EvalMoreArgs(fun, thisValue, Nil, done, ρ1)::k =>
        Co(Undefined(), σ, DoCall(fun, thisValue, done :+ v, Call(fun, done :+ v), ρ1)::k)

      case DoCall(fun @ Path(addr, path), thisValue, args, residual, ρ1)::k =>
        // HACK
        σ.get(Loc(addr)) match {
          case Some(ObjClosure(FunObject(_, _, xs, Some(e), _), ρ2)) =>
            // Pad the arguments with undefined.
            def pad(params: List[Name], args: List[Exp]): List[Exp] = (params, args) match {
              case (Nil, _) => Nil
              case (_::params, Nil) => Undefined()::pad(params, Nil)
              case (_::params, arg::args) => arg::pad(params, args)
            }
            val args2 = pad(xs, args)
            val seq = (xs zip args2).foldLeft(Assign(None, LocalAddr("this"), thisValue): Exp) {
              case (seq, (x, a)) => Seq(seq, Assign(None, LocalAddr(x), a))
            }
            val ρ2 = ("this"::xs).foldLeft(ρ1) {
              case (ρ, x) => ρ + (x -> FreshLoc())
            }
            val k1 = RebuildLet("this"::xs, (thisValue::args2) map { a => Undefined() }, ρ2)::k
            Ev(Seq(seq, e), ρ2, σ, CallFrame(ρ1)::k1)  // use ρ1 in the call frame.. this is the env we pop to.

          case Some(ValClosure(Prim(fun))) =>
            Eval.evalPrim(fun, args) match {
              case Some(e) =>
                // Use Ev, not Co... the prim might be eval and return the expression to eval.
                Ev(e, ρ1, σ, k)
              case None =>
                Co(reify(residual)(σ, ρ1), σ, k)
            }

          case _ =>
            Co(reify(residual)(σ, ρ1), σ, k)
        }

      // The function is not a lambda. Residualize the call. Clear the store since we have no idea what the function
      // will do to the store.
      case DoCall(fun, thisValue, args, residual, ρ1)::k =>
        Co(reify(residual)(σ, ρ1), σ, k)


      ////////////////////////////////////////////////////////////////
      // Return. Pop the continuations until we hit the caller.
      ////////////////////////////////////////////////////////////////

      case DoReturn()::k =>
        Co(Undefined(), σ, Returning(v)::k)

      // Once we hit the call frame, evaluate the return value.
      // Then pop the call frame using the ValueOrResidual rule.
      case Returning(v)::CallFrame(ρ1)::k =>
        Co(v, σ, k)

      // If we hit a rebuild continuation, we must run it, passing in v
      // (which is either undefined or a residual) to the rebuild continuation
      case Returning(v)::(a: RebuildCont)::k =>
        Co(v, σ, a::FocusCont(v)::DoReturn()::k)

      case Returning(e)::_::k =>
        Co(v, σ, Returning(e)::k)

      // If we run off the end of the function body, act like we returned normally.
      // This also runs after evaluating the return value after a return.
      case CallFrame(ρ1)::k =>
        Co(v, σ, k)


      ////////////////////////////////////////////////////////////////
      // Throw. This is implemented similarly to Return.
      ////////////////////////////////////////////////////////////////

      case DoThrow()::k =>
        Co(Undefined(), σ, Throwing(v)::k)

      // If we're throwing and we hit a try block,
      // evaluate the finally block and rethrow.
      case Throwing(e)::FinallyFrame(fin, ρ1)::k =>
        Ev(fin, ρ1, σ, Throwing(e)::k)

      // If we hit a rebuild continuation, we must run it, passing in v
      // (which is either undefined or a residual) to the rebuild continuation
      case Throwing(e)::(a: RebuildCont)::k =>
        Co(v, σ, a::Throwing(e)::k)

      case Throwing(e)::_::k =>
        Co(v, σ, Throwing(e)::k)

      // Run the finally block, if any. Then restore the value.
      // And pass it to k.
      case FinallyFrame(fin, ρ1)::k =>
        Ev(fin, ρ1, σ, FocusCont(v)::k)


      // Wrap v in a let.
      case RebuildLet(xs, args, ρ1)::k =>
        v match {
          case Value(v) =>
            val ss = (xs zip args) collect {
              case (x, e) if ! v.isInstanceOf[Path] && (fv(v) contains x) => VarDef(x, e)
            }
            if (ss.nonEmpty) {
              reify(v)(σ, ρ1) match {
                case v =>
                  val block = ss.foldRight(v) {
                    case (s1, s2) => Seq(s1, s2)
                  }
                  Co(Residual(block), Eval.simulateStore(block)(σ, ρ1), k)
              }
            }
            else {
              Co(v, σ, k)
            }

          case Residual(v) =>
            val ss = (xs zip args) collect {
              case (x, e) if (fv(v) contains x) => VarDef(x, e)
            }
            if (ss.nonEmpty) {
              val block = ss.foldRight(v) {
                case (s1, s2) => Seq(s1, s2)
              }
              Co(Residual(block), Eval.simulateStore(block)(σ, ρ1), k)
            }
            else {
              Co(Residual(v), Eval.simulateStore(v)(σ, ρ1), k)
            }
        }

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
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, Nil, ρ1)::k)

      case EvalArgsForNew(arg::args, ρ1)::k =>
        val fun = v
        Ev(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, Nil, ρ1)::k)

      case EvalMoreArgsForNew(fun, arg::args, done, ρ1)::k =>
        Ev(arg, ρ1, σ, EvalMoreArgsForNew(fun, args, done :+ v, ρ1)::k)

      case EvalMoreArgsForNew(fun, Nil, done, ρ1)::k =>
        Ev(Index(fun, StringLit("prototype")), ρ1, σ, InitProto(fun, done :+ v, ρ1)::k)

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

            // create a fresh variable for the new object
            // and introduce a residual NewCall
            val x = FreshVar()
            val xloc = FreshLoc()
            val ρ2 = ρ1 + (x -> xloc)

            Co(Undefined(), σ.assign(xloc, loc, ρ2).assign(loc, obj, ρ2), DoCall(fun, Local(x), args, Local(x), ρ2)::SeqCont(Local(x), ρ2)::RebuildLet(x::Nil, reify(loc)(σ, ρ1)::Nil, ρ1)::k)

          case None =>
            Co(reify(loc)(σ, ρ1), Eval.simulateStore(reify(loc)(σ, ρ1))(σ, ρ1), k)
        }

      case EvalPropertyNameForDel(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, DoDeleteProperty(a, ρ1)::k)

      case DoDeleteProperty(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, p), i @ CvtString(istr)) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
                val v = props collectFirst {
                  case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
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
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(a, σ, k)
              case Some(UnknownClosure()) | None =>
                reify(Delete(IndexAddr(a, i)))(σ, ρ1) match {
                  case v =>
                    Co(v, Eval.simulateStore(v)(σ, ρ1), k)
                }
            }

          case (a, i) =>
            reify(Delete(IndexAddr(a, i)))(σ, ρ1) match {
              case v =>
                Co(v, Eval.simulateStore(v)(σ, ρ1), k)
            }
        }
      case EvalPropertyNameForSet(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, GetPropertyAddressOrCreate(a, ρ1)::k)

      case GetPropertyAddressOrCreate(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, path), i @ CvtString(istr)) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
                val v = props collectFirst {
                  case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
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
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(Undefined(), σ, k)
              case Some(UnknownClosure()) | None =>
                reify(IndexAddr(a, i))(σ, ρ1) match {
                  case v =>
                    Co(v, Eval.simulateStore(v)(σ, ρ1), k)
                }
            }
          case (a, i) =>
            reify(IndexAddr(a, i))(σ, ρ1) match {
              case v =>
                Co(v, Eval.simulateStore(v)(σ, ρ1), k)
            }
        }

      case EvalPropertyNameForGet(i, ρ1)::k =>
        val a = v
        Ev(i, ρ1, σ, GetProperty(a, ρ1)::k)

      // restrict the property to values to ensure == during property lookup works correctly
      // otherwise, a[f()] will result in undefined rather than a reified access
      case GetProperty(a, ρ1)::k =>
        (a, v) match {
          case (a @ Path(addr, path), Value(i)) =>
            σ.get(Loc(addr)) match {
              case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), ρ2)) =>
                println(s"looking for $i in $props")
                val propAddr = props collectFirst {
                  case (k, v: Loc) if Eval.evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
                }
                println(s"looking for $i in $props: found $propAddr")
                propAddr match {
                  case Some(propAddr) =>
                    println(s"looking for $i in $props: loading $propAddr")
                    Co(Path(propAddr.address, Index(path, i)), σ, LoadCont(ρ1)::k)
                  case None =>
                    if (body != None && Eval.evalOp(Binary.==, StringLit("length"), i) == Bool(true)) {
                      Co(Num(xs.length), σ, k)
                    }
                    else {
                      // Try the prototype.
                      // If not found, return undefined.
                      Co(i, σ, GetProperty(Path(proto.address, path), ρ1)::k)
                    }
                }
              case Some(ValClosure(_)) | Some(LocClosure(_)) =>
                Co(Undefined(), σ, k)
              case Some(UnknownClosure()) | None =>
                reify(Index(a, i))(σ, ρ1) match {
                  case v =>
                    Co(v, Eval.simulateStore(v)(σ, ρ1), k)
                }
            }
          case (a, i) =>
            reify(Index(a, i))(σ, ρ1) match {
              case v =>
                Co(v, Eval.simulateStore(v)(σ, ρ1), k)
            }
        }

      /////////////////
      // No more cases....
      /////////////////
    }
  }
}
