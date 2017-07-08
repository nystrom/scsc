package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Eval {
  import Machine._
  import Continuations._
  import Residualization._
  import Context.{ρempty, σempty}

  def getPrimAddress(p: Prim): Loc = {
    Context.σ0 foreach {
      case (loc, ValClosure(q)) if p == q =>
        return loc
      case _ =>
    }
    assert(false)
    ???
  }

  def getPropertyAddress(loc: Loc, i: Exp, σ: Store) = {
    σ.get(loc) match {
      case Some(ObjClosure(FunObject(typeof, proto, xs, body, props), _)) =>
        props collectFirst {
          case (k, v: Loc) if evalOp(Binary.==, StringLit(k), i) == Bool(true) => v
        }
      case _ => None
    }
  }

  // Fix this! This is too simple and doesn't handle coercions corretctly.
  // Let's look at the spec.
  def evalOp(op: Operator, v1: Exp, v2: Exp): Exp = (op, v1, v2) match {
    case (Binary.+, StringLit(n1), StringLit(n2)) => StringLit(n1 + n2)
    case (Binary.+, StringLit(n1), CvtString(n2)) => StringLit(n1 + n2)
    case (Binary.+, CvtString(n1), StringLit(n2)) => StringLit(n1 + n2)

    case (Binary.+, CvtNum(n1), CvtNum(n2)) => Num(n1 + n2)
    case (Binary.+, CvtString(n1), CvtString(n2)) => StringLit(n1 + n2)

    case (Binary.-, CvtNum(n1), CvtNum(n2)) => Num(n1 - n2)
    case (Binary.*, CvtNum(n1), CvtNum(n2)) => Num(n1 * n2)
    case (Binary./, CvtNum(n1), CvtNum(n2)) => Num(n1 / n2)
    case (Binary.%, CvtNum(n1), CvtNum(n2)) => Num(n1 % n2)

    case (Binary.&, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong & n2.toLong)
    case (Binary.|, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong | n2.toLong)
    case (Binary.^, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong ^ n2.toLong)
    case (Binary.>>, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong >> n2.toLong)
    case (Binary.<<, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong << n2.toLong)
    case (Binary.>>>, CvtNum(n1), CvtNum(n2)) => Num(n1.toLong >>> n2.toLong)

    case (Binary.<, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Bool(n1 < n2)
    case (Binary.<=, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Bool(n1 <= n2)
    case (Binary.>, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Bool(n1 > n2)
    case (Binary.>=, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Bool(n1 >= n2)

    case (Binary.<, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Undefined()
    case (Binary.<=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Undefined()
    case (Binary.>, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Undefined()
    case (Binary.>=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Undefined()

    case (Binary.<, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Bool(n1 < n2)
    case (Binary.<=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Bool(n1 <= n2)
    case (Binary.>, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Bool(n1 > n2)
    case (Binary.>=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Bool(n1 >= n2)

    case (Binary.&&, CvtBool(n1), CvtBool(n2)) => Bool(n1 && n2)
    case (Binary.||, CvtBool(n1), CvtBool(n2)) => Bool(n1 || n2)

    case (Binary.BIND, v1, v2) =>
      println("ERROR: unimplemented ${Binary(op, v1, v2).show}")
      reify(Binary(op, v1, v2))

    case (op, v1, v2 @ Residual(e2)) => reify(Binary(op, v1, v2))
    case (op, v1 @ Residual(e1), v2) => reify(Binary(op, v1, v2))

    case (Binary.COMMALEFT, v1, v2) => v1
    case (Binary.COMMARIGHT, v1, v2) => v2

    // Equality operators should not work on residuals.
    // So match after the above.

    case (Binary.!=, v1, v2) => evalOp(Binary.==, v1, v2) match {
      case Bool(v) => Bool(!v)
      case Residual(Binary(Binary.==, v1, v2)) => reify(Binary(Binary.!=, v1, v2))
      case r => reify(Binary(Binary.!=, v1, v2))
    }

    case (Binary.!==, v1, v2) => evalOp(Binary.===, v1, v2) match {
      case Bool(v) => Bool(!v)
      case Residual(Binary(Binary.===, v1, v2)) => reify(Binary(Binary.!==, v1, v2))
      case r => reify(Binary(Binary.!==, v1, v2))
    }

    case (Binary.==, Null(), Undefined()) => Bool(true)
    case (Binary.==, Undefined(), Null()) => Bool(true)
    case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[StringLit] => Bool(n1 == n2)
    case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[StringLit] => Bool(n1 == n2)
    case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[Bool] => Bool(n1 == n2)
    case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[Bool] => Bool(n1 == n2)

    case (Binary.==, Path(n1, _), Path(n2, _)) if n1 == n2 => Bool(true)
    // We don't handle object literals, so just reify.
    case (Binary.==, v1 @ Path(n1, _), v2) => reify(Binary(Binary.==, v1, v2))
    case (Binary.==, v1, v2 @ Path(n2, _)) => reify(Binary(Binary.==, v1, v2))

    // for other cases, just use ===.
    case (Binary.==, v1, v2) => evalOp(Binary.===, v1, v2) match {
      case Bool(v) => Bool(v)
      case Residual(Binary(Binary.===, v1, v2)) => reify(Binary(Binary.==, v1, v2))
      case r => reify(Binary(Binary.==, v1, v2))
    }

    case (Binary.===, Undefined(), Undefined()) => Bool(true)
    case (Binary.===, Null(), Null()) => Bool(true)
    case (Binary.===, Num(n1), Num(n2)) => Bool(n1 == n2)
    case (Binary.===, StringLit(n1), StringLit(n2)) => Bool(n1 == n2)
    case (Binary.===, Bool(n1), Bool(n2)) => Bool(n1 == n2)
    case (Binary.===, Path(n1, _), Path(n2, _)) => Bool(n1 == n2) // same object
    case (Binary.===, v1, v2) => Bool(false) // all other cases should be false (residuals are handled above)

    // Failure
    case (op, v1, v2) =>
      println("ERROR: cannot apply ${Binary(op, v1, v2).show}")
      reify(Binary(op, v1, v2))
  }

  def evalPrim(fun: String, args: List[Exp]): Option[Exp] = (fun, args) match {
    case ("eval", StringLit(code)::_) => scsc.js.Parser.fromString(code)
    case ("eval", Value(v)::_) => Some(v)
    case ("eval", Nil) => Some(Undefined())
    case ("isNaN", CvtNum(v)::_) => Some(Bool(v.isNaN))
    case ("isNaN", Nil) => Some(Bool(true))
    case ("isFinite", CvtNum(v)::_) => Some(Bool(!v.isInfinite))
    case ("isFinite", Nil) => Some(Bool(false))
    case ("String.indexOf", StringLit(s)::StringLit(c)::Nil) => None
    case ("String.charAt", StringLit(s)::CvtNum(i)::Nil) => None /// Some(StringLit(s(i.toInt).toString))
    case ("Regex.exec", Regex(re, opts)::StringLit(s)::Nil) => None /// Some(StringLit(s(i.toInt).toString))
    case ("Math.abs", CvtNum(v)::_) => Some(Num(v.abs))
    case ("Math.sqrt", CvtNum(v)::_) => Some(Num(math.sqrt(v)))
    case ("Math.floor", CvtNum(v)::_) => None
    case ("Math.ceil", CvtNum(v)::_) => None
    case ("Math.round", CvtNum(v)::_) => None
    case ("Math.exp", CvtNum(v)::_) => Some(Num(math.exp(v)))
    case ("Math.log", CvtNum(v)::_) => None
    case ("Math.sin", CvtNum(v)::_) => Some(Num(math.sin(v)))
    case ("Math.cos", CvtNum(v)::_) => Some(Num(math.cos(v)))
    case ("Math.tan", CvtNum(v)::_) => Some(Num(math.tan(v)))
    case ("Math.asin", CvtNum(v)::_) => Some(Num(math.asin(v)))
    case ("Math.acos", CvtNum(v)::_) => Some(Num(math.acos(v)))
    case ("Math.atan", CvtNum(v)::_) => Some(Num(math.atan(v)))
    case ("Math.pow", CvtNum(v1)::CvtNum(v2)::_) => Some(Num(math.pow(v1, v2)))
    case ("Math.atan2", CvtNum(v1)::CvtNum(v2)::_) => Some(Num(math.atan2(v1, v2)))
    case ("Math.max", es) =>
      val r = es.foldLeft(Option(-1.0/0.0)) {
        case (Some(v1), CvtNum(v2)) => Some(math.max(v1, v2))
        case _ => None
      }
      r map { v => Num(v) }
    case ("Math.min", es) =>
      val r = es.foldLeft(Option(1.0/0.0)) {
        case (Some(v1), CvtNum(v2)) => Some(math.min(v1, v2))
        case _ => None
      }
      r map { v => Num(v) }
    case _ => None
  }

  def simulateStore(e: Exp)(σ0: Store, ρ: Env): Store = {
    object Simulator extends scsc.js.TreeWalk.Rewriter {
      var σ = σ0
      override def rewrite(e: Exp) = e match {
        case Assign(op, left, right) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case IncDec(op, left) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case Delete(left) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case Call(f, args) =>
          σ = invalidateHeap(σ, ρ)
          e
        case NewCall(f, args) =>
          σ = invalidateHeap(σ, ρ)
          e
        case Lambda(params, body) =>
          // do nothing
          e
        case With(exp, body) =>
          σ = invalidateHeap(σ, ρ)
          super.rewrite(e)
        case e =>
          super.rewrite(e)
      }
    }
    Simulator.rewrite(e)
    Simulator.σ
  }

  def invalidateHeap(σ: Store, ρ: Env): Store = {
    σ collect {
      case (loc, v) if ρ.exists { case (x, loc1) => loc == loc1 } => (loc, v)
    }
  }

  def invalidateLocation(e: Exp)(σ: Store, ρ: Env): Store = e match {
    case Residual(e) =>
      invalidateLocation(e)(σ, ρ)

    case Path(address, path) =>
      // Remove the location
      σ + (Loc(address) -> UnknownClosure())

    case Local(x) =>
      ρ.get(x) match {
        case Some(loc) => σ + (loc -> UnknownClosure())
        case None => σ
      }

    case LocalAddr(x) =>
      ρ.get(x) match {
        case Some(loc) => σ + (loc -> UnknownClosure())
        case None => σ
      }

    case Index(a, StringLit(i)) =>
      // Remove all properties named i
      val addrs: Iterable[Loc] = σ flatMap {
        case (_, ObjClosure(FunObject(_, _, _, _, props), _)) =>
          props collect {
            case (k, loc) if k == i => loc
          }
        case _ => Nil
      }

      addrs.foldLeft(σ) {
        case (σ, loc) => σ + (loc -> UnknownClosure())
      }

    case IndexAddr(a, StringLit(i)) =>
      // Remove all properties named i
      val addrs: Iterable[Loc] = σ flatMap {
        case (_, ObjClosure(FunObject(_, _, _, _, props), _)) =>
          props collect {
            case (k, loc) if k == i => loc
          }
        case _ => Nil
      }

      addrs.foldLeft(σ) {
        case (σ, loc) => σ + (loc -> UnknownClosure())
      }

    case IndexAddr(a, i) =>
      // Remove ALL properties in the store
      val addrs: Iterable[Loc] = σ flatMap {
        case (_, ObjClosure(FunObject(_, _, _, _, props), _)) =>
          props map {
            case (k, loc) => loc
          }
        case _ => Nil
      }

      addrs.foldLeft(σ) {
        case (σ, loc) => σ + (loc -> UnknownClosure())
      }

    case _ =>
      σ
  }
}
