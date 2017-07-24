package scsc.imp

import scsc.machine

trait Terms extends machine.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }

  import machine._

  type Name = String

  type Term = Exp
  trait Exp extends Product
  trait Jump extends Exp
  trait Value extends Exp
  trait Var extends Exp

  trait Operator

  object Prefix {
    case object -- extends Operator
    case object ++ extends Operator

    case object + extends Operator
    case object ~ extends Operator
    case object - extends Operator
    case object ! extends Operator
  }

  object Postfix {
    case object -- extends Operator
    case object ++ extends Operator
  }

  object Binary {
    case object + extends Operator
    case object && extends Operator
    case object & extends Operator
    case object | extends Operator
    case object ^ extends Operator
    case object / extends Operator
    case object % extends Operator
    case object * extends Operator
    case object >> extends Operator
    case object << extends Operator
    case object >>> extends Operator
    case object - extends Operator
    case object == extends Operator
    case object >= extends Operator
    case object > extends Operator
    case object <= extends Operator
    case object < extends Operator
    case object != extends Operator
    case object || extends Operator

    case object Pair extends Operator
  }

  object Nary {
    case object InitObject extends Operator
    case object InitArray extends Operator
    case object Call extends Operator
  }

  object Array {
    case object Load extends Operator
    case object Address extends Operator
  }

  trait Lit extends Value
  case class BooleanLit(v: Boolean) extends Lit
  case class DoubleLit(v: Double) extends Lit
  case class IntLit(v: Int) extends Lit
  case class StringLit(v: String) extends Lit
  case class Null() extends Lit
  case class Undefined() extends Lit  // the void value

  // Used for method selectors and properties
  case class PairValue(v1: Value, v2: Value) extends Lit

  case class Unary(op: Operator, e: Exp) extends Exp
  case class IncDec(op: Operator, e: Exp) extends Exp
  case class Assign(op: Option[Operator], left: Exp, right: Exp) extends Exp
  case class Binary(op: Operator, left: Exp, right: Exp) extends Exp
  case class Seq(e1: Exp, e2: Exp) extends Exp
  case class Break(label: Option[Name]) extends Jump
  case class Call(f: Exp, args: List[Exp]) extends Exp
  case class Catch(ex: Name, test: Option[Exp], body: Exp) extends Exp
  case class Continue(label: Option[Name]) extends Jump
  case class Empty() extends Exp
  case class For(label: Option[Name], init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp
  case class Lambda(params: List[Name], body: Exp) extends Exp
  case class Scope(body: Exp) extends Exp
  case class Local(x: Name) extends Exp with Var
  case class IfElse(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Index(a: Exp, i: Exp) extends Exp with Var
  case class ArrayLit(es: List[Exp]) extends Exp
  case class ObjectLit(es: List[Exp]) extends Exp
  case class Property(k: Exp, v: Exp) extends Exp
  case class Return(e: Option[Exp]) extends Jump
  case class Cond(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Throw(e: Exp) extends Jump
  case class TryCatch(e: Exp, catches: List[Exp]) extends Exp
  case class TryFinally(e: Exp, fin: Exp) extends Exp
  case class VarDef(x: Name, init: Exp) extends Exp
  case class While(label: Option[Name], cond: Exp, body: Exp) extends Exp
  case class DoWhile(label: Option[Name], body: Exp, cond: Exp) extends Exp

  import stores.Loc
  case class Path(loc: Loc, path: Exp) extends Value with Var

  import envs.Env
  import stores.Store
  import continuations.Cont
  import states.State

  def doCall(op: Operator, operands: List[Value], ρ: Env, σ: Store, k: Cont): Option[State]

  def evalArrayOp(op: Operator, array: Value, index: Value, σ: Store): Option[(Value, Store)]

  def evalUnaryOp(op: Operator, v: Value): Option[Value]
  def evalBinaryShortCircuitOp(op: Operator, v1: Value): Option[Value]
  def evalBinaryOp(op: Operator, v1: Value, v2: Value): Option[Value]

  def evalPredicate(v: Value): Option[Boolean]

  def addDeclarations(e: Exp, ρ: Env, σ: Store): (List[Exp], Env, Store)

  val Loop: Loop
  trait Loop {
    def unapply(loop: Exp): Option[(Option[Name], Exp, Exp)] = loop match {
      case While(label, test, body) =>
        Some((label, body, loop))
      case For(label, _, test, iter, body) =>
        Some((label, body, Seq(iter, loop)))
      case _ =>
        None
    }
  }

  import states._
  import stores._
  import continuations._

  def eval(s: Ev) = s match {
    case Ev(focus, ρ, σ, k) => focus match {
      // For any value, just run the continuation.
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
        val f1: PartialFunction[Value, Exp] = { case BooleanLit(true) => s1 }
        val f2: PartialFunction[Value, Exp] = { case BooleanLit(false) => s2 }
        Some(Ev(e, ρ, σ, BranchCont(f1::f2::Nil, ρ)::k))

      // e ? s1 : s2
      case Cond(e, s1, s2) =>
        val f1: PartialFunction[Value, Exp] = { case BooleanLit(true) => s1 }
        val f2: PartialFunction[Value, Exp] = { case BooleanLit(false) => s2 }
        Some(Ev(e, ρ, σ, BranchCont(f1::f2::Nil, ρ)::k))

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

        // Create an empty object
        case ObjectLit(Nil) => Some {
          val loc = FreshHeapLoc()
          val path = Path(loc, ObjectLit(Nil))
          val blob = ObjectBlob(Nil)
          Co(path, σ.assign(loc, blob, ρ), k)
        }

        // Initialize a non-empty object.
        case ObjectLit(ps) => Some {
          Ev(ObjectLit(Nil), ρ, σ, EvalArgs(Nary.InitObject, ps, ρ)::k)
        }

        case Property(key, value) =>
          Some(Ev(key, ρ, σ, EvalBinaryOpRight(Binary.Pair, value, ρ)::k))

        case ArrayLit(Nil) => Some {
          val loc = FreshHeapLoc()
          val path = Path(loc, ArrayLit(Nil))
          val blob = ArrayBlob(Nil)
          Co(path, σ.assign(loc, blob, ρ), k)
        }

        // Initialize a non-empty object.
        case ArrayLit(es) => Some {
          Ev(ArrayLit(Nil), ρ, σ, EvalArgs(Nary.InitArray, es, ρ)::k)
        }

        // Put a lambda in the heap.
        case lam @ Lambda(xs, e) => Some {
          // x = v
          // x.proto = v2
          val loc = FreshHeapLoc()
          val blob = LambdaBlob(lam)
          Co(Path(loc, lam), σ.assign(loc, blob, ρ), k)
        }

        case e => None
    }
  }
}
