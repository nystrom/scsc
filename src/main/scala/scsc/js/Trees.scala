package scsc.js

// Adapters for Nashorn AST nodes

object Trees {
  type Node = Exp
  type Stm = Exp

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
      case Loc(_) => Some(true)
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
      case v => None
    }
  }

  object CvtString {
    def unapply(e: Exp) = e match {
      case StringLit(v) => Some(v)
      case ObjectLit(es) => Some(es.map(_.show).mkString("{", ",", "}"))
      case ArrayLit(es) => Some(es.map(_.show).mkString("[", ",", "]"))
      case Lambda(xs, e) => Some("<function>")
      case e => Some(e.show)
    }
  }

  object Value {
    def unapply(e: Exp) = e match {
      case v if v.isValue => Some(v)
      case _ => None
    }
  }

  object HeapValue {
    def unapply(e: Exp) = e match {
      case v if v.isHeapValue => Some(v)
      case _ => None
    }
  }

  object ValueOrResidual {
    def unapply(e: Exp) = e match {
      case v if v.isValueOrResidual => Some(v)
      case _ => None
    }
  }

  object NormalForm {
    def unapply(e: Exp) = e match {
      case v if v.isNormalForm => Some(v)
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
        case t @ Ident(x) =>
          vars += x
          t
        case t @ Lambda(xs, e) =>
          vars ++= (fv(e) -- xs)
          t
        case t @ LetDef(x, _) =>
          defs += x
          super.rewrite(t)
        case t @ VarDef(x, _) =>
          defs += x
          super.rewrite(t)
        case t @ ConstDef(x, _) =>
          defs += x
          super.rewrite(t)
        case t @ Block(ss) =>
          val v = new FV()
          v.rewrite(ss)
          vars ++= (v.getVars -- v.getDefs)
          t
        case t =>
          super.rewrite(t)
      }
    }

    val t = new FV()
    t.rewrite(n)
    t.getVars
  }


  case class Loc(address: Int) extends Exp
  case class Residual(e: Exp) extends Exp

  import org.bitbucket.inkytonik.kiama.util.Counter

  object FreshLoc extends Counter {
    def apply(): Loc = Loc(next())
  }

  type Name = String

  implicit class IV(e: Exp) {
    def isPure: Boolean = {
      import scsc.js.TreeWalk._
      object Purity extends Rewriter {
        var pure = true

        override def rewrite(e: Exp): Exp = e match {
          case _: Call | _: NewCall =>
            pure = false
            e
          case _: While | _: DoWhile | _: For | _: ForIn | _: ForEach =>
            pure = false
            e
          case _: Assign | _: IncDec =>
            pure = false
            e
          case _: Return | _: Yield | _: Throw | _: Catch | _: Try =>
            pure = false
            e
          case _: VarDef | _: LetDef | _: ConstDef =>
            pure = false
            e
          case _: Break | _: Continue =>
            pure = false
            e
          case _: Delete | _: New =>
            pure = false
            e
          case e if pure => super.rewrite(e)
          case e => e
        }
      }

      Purity.rewrite(e)
      Purity.pure
    }

    // JavaScript values (no control-flow, no residuals)
    // Locations are the values for object and array literals.
    def isValue: Boolean = e match {
      case StringLit(_) => true
      case Bool(_) => true
      case Num(_) => true
      case Undefined() => true
      case Null() => true
      case Loc(_) => true
      case _ => false
    }

    def isValueOrResidual: Boolean = e match {
      case Residual(_) => true
      case v => v.isValue
    }

    def isNormalForm: Boolean = e match {
      // control-flow values
      case Break(_) => true
      case Continue(_) => true
      case Return(v) => v forall { _.isNormalForm }
      case Yield(v) => v forall { _.isNormalForm }
      case Throw(v) => v.isNormalForm
      case Empty() => true

      case v => v.isHeapValue
    }

    def isHeapValue: Boolean = e match {
      case Lambda(_, _) => true
      case ArrayLit(es) => es.forall(_.isHeapValue)
      case ObjectLit(es) => es.forall(_.isHeapValue)
      case Property(k, v, g, s) => k.isHeapValue && v.isHeapValue && g.forall(_.isHeapValue) && s.forall(_.isHeapValue)
      case v => v.isValueOrResidual
    }

    def costZero: Boolean = e match {
      case Ident(_) => true
      case LocalAddr(_) => true
      case Residual(e) => e.costZero
      case ArrayLit(es) => es.forall(_.costZero)
      case ObjectLit(es) => es.forall(_.costZero)
      case Property(k, v, g, s) => k.costZero && v.costZero && g.forall(_.costZero) && s.forall(_.costZero)
      case v => v.isValue
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

  sealed trait Lit extends Exp
  case class Unary(op: Operator, e: Exp) extends Exp
  case class IncDec(op: Operator, e: Exp) extends Exp
  case class Delete(e: Exp) extends Exp // HACKED
  case class New(e: Exp) extends Exp // HACKED
  case class Typeof(e: Exp) extends Exp // HACKED (does not handle prototypes)
  case class Void(e: Exp) extends Exp
  case class Assign(op: Option[Operator], left: Exp, right: Exp) extends Exp
  case class Binary(op: Operator, left: Exp, right: Exp) extends Exp  // HACKED: many operators wrong
  case class Block(es: List[Exp]) extends Exp
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
  case class Program(body: Exp) extends Exp
  case class Ident(x: Name) extends Exp
  case class LocalAddr(x: Name) extends Exp
  case class IfElse(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Index(a: Exp, i: Exp) extends Exp
  case class IndexAddr(a: Exp, i: Exp) extends Exp
  case class ArrayLit(es: List[Exp]) extends Exp  // HACKED (prototype missing)
  case class Bool(v: Boolean) extends Lit
  case class Num(v: Double) extends Lit
  case class StringLit(v: String) extends Lit
  case class Null() extends Lit
  case class Undefined() extends Lit
  case class ObjectLit(es: List[Exp]) extends Exp // HACKED (prototype missing)
  case class Property(k: Exp, v: Exp, getter: Option[Exp], setter: Option[Exp]) extends Exp // HACKED, no getter, setter
  case class Return(e: Option[Exp]) extends Exp
  case class Yield(e: Option[Exp]) extends Exp  // MISSING
  case class Switch(e: Exp, cases: List[Exp]) extends Exp // MISSING
  case class Cond(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Throw(e: Exp) extends Exp
  case class Try(e: Exp, catches: List[Exp], fin: Option[Exp]) extends Exp
  case class VarDef(x: Name, init: Exp) extends Exp
  case class LetDef(x: Name, init: Exp) extends Exp  // MISSING
  case class ConstDef(x: Name, init: Exp) extends Exp  // MISSING
  case class While(label: Option[Name], cond: Exp, body: Exp) extends Exp
  case class DoWhile(label: Option[Name], body: Exp, cond: Exp) extends Exp
  case class With(exp: Exp, body: Exp) extends Exp  // MISSING
}
