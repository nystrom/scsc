package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Eval {
  import Machine._
  import Continuations._
  import Residualization._
  import Context.{ρempty, σempty}

  def getPropertyAddress(loc: Loc, i: Exp, σ: Store) = {
    σ.get(loc) match {
      case Some(Closure(FunObject(typeof, proto, xs, body, props), _)) =>
        val v = props collectFirst {
          case Property(k, v: Loc, g, s) if evalOp(Binary.==, k, i) == Bool(true) => v
        }
        v match {
          case Some(v) => Some(v)
          case None => None
        }
      case _ => None
    }
  }

  // Fix this! This is too simple and doesn't handle coercions corretctly.
  // Let's look at the spec.
  def evalOp(op: Operator, v1: Exp, v2: Exp): Exp = (op, v1, v2) match {
    case (Binary.+, CvtNum(n1), CvtNum(n2)) => Num(n1 + n2)
    case (Binary.-, CvtNum(n1), CvtNum(n2)) => Num(n1 - n2)
    case (Binary.*, CvtNum(n1), CvtNum(n2)) => Num(n1 * n2)
    case (Binary./, CvtNum(n1), CvtNum(0)) =>
      println("ERROR: div by 0: ${Binary(op, v1, v2).show}")
      reify(Binary(op, v1, v2))(σempty, ρempty)
    case (Binary.%, CvtNum(n1), CvtNum(0)) =>
      println("ERROR: mod by 0: ${Binary(op, v1, v2).show}")
      reify(Binary(op, v1, v2))(σempty, ρempty)
    case (Binary./, CvtNum(n1), CvtNum(n2)) => Num(n1 / n2)
    case (Binary.%, CvtNum(n1), CvtNum(n2)) => Num(n1 % n2)

    case (Binary.+, CvtString(n1), CvtString(n2)) => StringLit(n1 + n2)

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
      reify(Binary(op, v1, v2))(σempty, ρempty)

    case (op, v1, v2 @ Residual(e2)) => reify(Binary(op, v1, v2))(σempty, ρempty)
    case (op, v1 @ Residual(e1), v2) => reify(Binary(op, v1, v2))(σempty, ρempty)

    case (Binary.COMMALEFT, v1, v2) => v1
    case (Binary.COMMARIGHT, v1, v2) => v2

    // Equality operators should not work on residuals.
    // So match after the above.

    case (Binary.!=, v1, v2) => evalOp(Binary.==, v1, v2) match {
      case Bool(v) => Bool(!v)
      case Residual(Binary(Binary.==, v1, v2)) => reify(Binary(Binary.!=, v1, v2))(σempty, ρempty)
      case r => reify(Binary(Binary.!=, v1, v2))(σempty, ρempty)
    }

    case (Binary.!==, v1, v2) => evalOp(Binary.===, v1, v2) match {
      case Bool(v) => Bool(!v)
      case Residual(Binary(Binary.===, v1, v2)) => reify(Binary(Binary.!==, v1, v2))(σempty, ρempty)
      case r => reify(Binary(Binary.!==, v1, v2))(σempty, ρempty)
    }

    case (Binary.==, Null(), Undefined()) => Bool(true)
    case (Binary.==, Undefined(), Null()) => Bool(true)
    case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[StringLit] => Bool(n1 == n2)
    case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[StringLit] => Bool(n1 == n2)
    case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[Bool] => Bool(n1 == n2)
    case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[Bool] => Bool(n1 == n2)

    case (Binary.==, Loc(n1), Loc(n2)) if n1 == n2 => Bool(true)
    // We don't handle object literals, so just reify.
    case (Binary.==, v1 @ Loc(n1), v2) => reify(Binary(Binary.==, v1, v2))(σempty, ρempty)
    case (Binary.==, v1, v2 @ Loc(n2)) => reify(Binary(Binary.==, v1, v2))(σempty, ρempty)

    // for other cases, just use ===.
    case (Binary.==, v1, v2) => evalOp(Binary.===, v1, v2) match {
      case Bool(v) => Bool(v)
      case Residual(Binary(Binary.===, v1, v2)) => reify(Binary(Binary.==, v1, v2))(σempty, ρempty)
      case r => reify(Binary(Binary.==, v1, v2))(σempty, ρempty)
    }

    case (Binary.===, Undefined(), Undefined()) => Bool(true)
    case (Binary.===, Null(), Null()) => Bool(true)
    case (Binary.===, Num(n1), Num(n2)) => Bool(n1 == n2)
    case (Binary.===, StringLit(n1), StringLit(n2)) => Bool(n1 == n2)
    case (Binary.===, Bool(n1), Bool(n2)) => Bool(n1 == n2)
    case (Binary.===, Loc(n1), Loc(n2)) => Bool(n1 == n2) // same object
    case (Binary.===, v1, v2) => Bool(false) // all other cases should be false (residuals are handled above)

    // Failure
    case (op, v1, v2) =>
      println("ERROR: cannot apply ${Binary(op, v1, v2).show}")
      reify(Binary(op, v1, v2))(σempty, ρempty)
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
