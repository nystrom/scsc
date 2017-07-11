package scsc.js

// Adapters for Nashorn AST nodes

object Trees {
  type Node = Exp

  sealed trait Exp extends Product

  implicit class PP(n: Exp) {
    def show: String = pretty
    def pretty: String = {
      n.toString
    }
  }

  object CvtPrim {
    def unapply(e: Exp) = e match {
      case e: Undefined => Some(e)
      case e: Null => Some(e)
      case e: Bool => Some(e)
      case e: Num => Some(e)
      case e: StringLit => Some(e)
      // TODO: call toString and valueOf methods if they exist.
      // case e: ObjectLit => Some(e)
      // case e: ArrayLit => Some(e)
      case _ => None
    }
  }

  object CvtBool {
    def unapply(e: Exp): Option[Boolean] = e match {
      case Bool(v) => Some(v)
      case Undefined() => Some(false)
      case Null() => Some(false)
      case Num(v) => Some(v != 0 && ! v.isNaN)
      case StringLit(v) => Some(v != "")
      case Path(_, _) => Some(true)
      case XML(_) => Some(true)
      case Regex(_, _) => Some(true)
      case v => None
    }
  }

  object CvtNum {
    def unapply(e: Exp): Option[Double] = e match {
      case Num(v) => Some(v)
      case Undefined() => Some(Double.NaN)
      case Null() => Some(0)
      case Bool(false) => Some(0)
      case Bool(true) => Some(1)

      // same as CvtStrictNum but more returns NaN more often
      case StringLit(v) =>
        try {
          Some(java.lang.Double.parseDouble(v))
        }
        catch {
          case ex: java.lang.NumberFormatException =>
            Some(Double.NaN)
        }
      case Path(_, _) => Some(Double.NaN)
      case v => None
    }
  }

  object CvtString {
    def unapply(e: Exp) = e match {
      case XML(v) => Some(v)
      case Regex(v, opts) => Some(s"/$v/$opts")
      case StringLit(v) => Some(v)
      case ObjectLit(es) => Some(es.map(_.show).mkString("{", ",", "}"))
      case ArrayLit(es) => Some(es.map(_.show).mkString("[", ",", "]"))
      case Lambda(xs, e) => Some("<function>")
      case Value(e) => Some(scsc.js.PP.pretty(e))
      case _ => None
    }
  }

  object Value {
    def unapply(e: Val) = e match {
      case v if v.isValue => Some(v)
      case _ => None
    }
  }

  object ValueOrResidual {
    def unapply(e: Val) = e match {
      case v if v.isValueOrResidual => Some(v)
      case _ => None
    }
  }

  def fv(n: Exp): Set[Name] = {
    import scsc.js.TreeWalk._

    class FV() extends Rewriter {
      import scala.collection.mutable.HashSet

      val vars = HashSet.empty[Name]
      def getVars = vars.toSet
      val defs = HashSet.empty[Name]
      def getDefs = defs.toSet

      override def rewrite(t: Exp): Exp = t match {
        case t @ Local(x) =>
          vars += x
          t
        case t @ Lambda(xs, e) =>
          vars ++= (fv(e) -- xs)
          t
        case t @ Scope(e) =>
          vars ++= fv(e)
          t
        case t @ VarDef(x, _) =>
          defs += x
          super.rewrite(t)
        case t =>
          super.rewrite(t)
      }
    }

    val t = new FV()
    t.rewrite(n)
    t.getVars -- t.getDefs
  }

  // FIXME: FunObject and Loc should not be expressions.
  // They live only in the heap

  // FIXME: Prim("foo.bar") should just be Residual(Index(Local("foo"), StringLit("bar")))
  sealed trait Val extends Exp
  case class Prim(name: String) extends Lit
  case class Path(address: Int, path: Exp) extends Val
  case class Residual(name: String) extends Val

  type Name = String

  implicit class IV(e: Exp) {
    // JavaScript values (no control-flow, no residuals)
    // Locations are the values for objects and functions.
    def isValue: Boolean = e match {
      case StringLit(_) => true
      case XML(_) => true
      case Regex(_, _) => true
      case Bool(_) => true
      case Num(_) => true
      case Undefined() => true
      case Null() => true
      case Path(_, _) => true
      // Empty is the void value
      case Empty() => true
      // Primitives are values as far as we're concerned
      case Prim(_) => true
      case _ => false
    }

    def isValueOrResidual: Boolean = e match {
      case Residual(_) => true
      case Prim(_) => true
      case v => v.isValue
    }
  }

  object Sequence {
    def apply(s1: Exp, s2: Exp): Exp = s1 match {
      case Undefined() => s2
      case s1 => s2 match {
        case Undefined() => s1
        case s2 => Seq(s1, s2)
      }
    }
  }

  sealed trait Operator

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
    case object BIND extends Operator
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
    case object COMMALEFT extends Operator
    case object COMMARIGHT extends Operator
    case object == extends Operator
    case object === extends Operator
    case object >= extends Operator
    case object > extends Operator
    case object IN extends Operator
    case object INSTANCEOF extends Operator
    case object <= extends Operator
    case object < extends Operator
    case object != extends Operator
    case object !== extends Operator
    case object || extends Operator
  }

  sealed trait Lit extends Val
  case class Bool(v: Boolean) extends Lit
  case class Num(v: Double) extends Lit
  case class StringLit(v: String) extends Lit
  case class XML(v: String) extends Lit
  case class Regex(v: String, opts: String) extends Lit
  case class Null() extends Lit
  case class Undefined() extends Lit

  case class Unary(op: Operator, e: Exp) extends Exp
  case class IncDec(op: Operator, e: Exp) extends Exp
  case class Delete(e: Exp) extends Exp // HACKED
  case class New(e: Exp) extends Exp // HACKED
  case class Typeof(e: Exp) extends Exp // HACKED (does not handle prototypes)
  case class Void(e: Exp) extends Exp
  case class Assign(op: Option[Operator], left: Exp, right: Exp) extends Exp
  case class Binary(op: Operator, left: Exp, right: Exp) extends Exp  // HACKED: many operators wrong
  case class Seq(e1: Exp, e2: Exp) extends Exp
  case class Break(label: Option[Name]) extends Exp
  case class Call(f: Exp, args: List[Exp]) extends Exp
  case class NewCall(f: Exp, args: List[Exp]) extends Exp        // MISSING
  case class Case(test: Option[Exp], body: Exp) extends Exp // MISSING
  case class Catch(ex: Name, test: Option[Exp], body: Exp) extends Exp  // UNTESTED
  case class Continue(label: Option[Name]) extends Exp
  case class Empty() extends Exp
  case class For(label: Option[Name], init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp
  case class ForIn(label: Option[Name], init: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class ForEach(label: Option[Name], init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class Lambda(params: List[Name], body: Exp) extends Exp
  case class Scope(body: Exp) extends Exp
  case class Local(x: Name) extends Exp
  case class IfElse(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Index(a: Exp, i: Exp) extends Exp
  case class ArrayLit(es: List[Exp]) extends Exp  // HACKED (prototype missing)

  case class ObjectLit(es: List[Exp]) extends Exp // HACKED (prototype missing)
  case class Property(k: Exp, v: Exp, getter: Option[Exp], setter: Option[Exp]) extends Exp // HACKED, no getter, setter
  case class Return(e: Option[Exp]) extends Exp
  case class Yield(e: Option[Exp]) extends Exp  // MISSING
  case class Switch(e: Exp, cases: List[Exp]) extends Exp // MISSING
  case class Cond(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Throw(e: Exp) extends Exp
  case class TryCatch(e: Exp, catches: List[Exp]) extends Exp
  case class TryFinally(e: Exp, fin: Exp) extends Exp
  case class VarDef(x: Name, init: Exp) extends Exp
  case class While(label: Option[Name], cond: Exp, body: Exp) extends Exp
  case class DoWhile(label: Option[Name], body: Exp, cond: Exp) extends Exp
  case class With(exp: Exp, body: Exp) extends Exp  // MISSING
}
