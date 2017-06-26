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
    def isTrue = e.isRealValue && ! e.isFalse

    def isFalse: Boolean = e match {
      case StringLit("") => true
      case Bool(false) => true
      case Num(0) => true
      case Undefined() => true
      case Null() => true
      case n => false
    }

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
          case _: Delete =>
            pure = false
            e
          case e if pure => super.rewrite(e)
          case e => e
        }
      }

      Purity.rewrite(e)
      Purity.pure
    }

    def isRealValue: Boolean = e match {
      case StringLit(_) => true
      case Bool(_) => true
      case Num(_) => true
      case Undefined() => true
      case Null() => true
      case Empty() => true
      case v: Lambda => true
      case v: Loc => true
      case ArrayLit(vs) => vs.forall(_.isRealValue)
      case ObjectLit(vs) => vs.forall(_.isRealValue)
      case Property(k, Some(v), None, None) => k.isRealValue && v.isRealValue
      case Property(k, None, None, None) => k.isRealValue
      case _ => false
    }

    def isValue: Boolean = e match {
      case StringLit(_) => true
      case Bool(_) => true
      case Num(_) => true
      case Undefined() => true
      case Null() => true
      case Empty() => true
      case v: Lambda => true
      case v: Loc => true
      case v: Residual => true
      case ArrayLit(vs) => vs.forall(_.isValue)
      case ObjectLit(vs) => vs.forall(_.isValue)
      case Property(k, Some(v), None, None) => k.isValue && v.isValue
      case Property(k, None, None, None) => k.isValue
      case _ => false
    }

    def costZero: Boolean = e match {
      case Ident(_) => true
      case Residual(e) => e.costZero
      case ArrayLit(es) => es.forall(_.costZero)
      case ObjectLit(es) => es.forall(_.costZero)
      case Property(k, Some(v), None, None) => k.costZero && v.costZero
      case Property(k, None, None, None) => k.costZero
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
  case class Delete(e: Exp) extends Exp
  case class New(e: Exp) extends Exp
  case class Typeof(e: Exp) extends Exp
  case class Void(e: Exp) extends Exp
  case class Assign(op: Option[Operator], left: Exp, right: Exp) extends Exp
  case class Binary(op: Operator, left: Exp, right: Exp) extends Exp
  case class Access(base: Exp, prop: Name) extends Exp
  case class Block(es: List[Exp]) extends Exp
  case class Break(label: Option[Name]) extends Exp
  case class Call(f: Exp, args: List[Exp]) extends Exp
  case class NewCall(f: Exp, args: List[Exp]) extends Exp
  case class Case(test: Option[Exp], body: Exp) extends Exp
  case class Catch(ex: Name, test: Option[Exp], body: Exp) extends Exp
  case class Continue(label: Option[Name]) extends Exp
  case class Empty() extends Exp
  case class For(init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp
  case class ForIn(init: Exp, modify: Exp, body: Exp) extends Exp
  case class ForEach(init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp
  case class Lambda(params: List[Name], body: Exp) extends Exp
  case class Program(body: Exp) extends Exp
  case class Ident(x: Name) extends Exp
  case class IfElse(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Index(a: Exp, i: Exp) extends Exp
  case class Label(label: Name, body: Exp) extends Exp
  case class ArrayLit(es: List[Exp]) extends Exp
  case class Bool(v: Boolean) extends Lit
  case class Num(v: Double) extends Lit
  case class StringLit(v: String) extends Lit
  case class Null() extends Lit
  case class Undefined() extends Lit
  case class ObjectLit(es: List[Exp]) extends Exp
  case class Property(k: Exp, v: Option[Exp], getter: Option[Exp], setter: Option[Exp]) extends Exp
  case class Return(e: Option[Exp]) extends Exp
  case class Yield(e: Option[Exp]) extends Exp
  case class Switch(e: Exp, cases: List[Exp]) extends Exp
  case class Cond(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Throw(e: Exp) extends Exp
  case class Try(e: Exp, catches: List[Exp], fin: Option[Exp]) extends Exp
  case class VarDef(x: Name, init: Exp) extends Exp
  case class LetDef(x: Name, init: Exp) extends Exp
  case class ConstDef(x: Name, init: Exp) extends Exp
  case class While(cond: Exp, body: Exp) extends Exp
  case class DoWhile(body: Exp, cond: Exp) extends Exp
  case class With(exp: Exp, body: Exp) extends Exp
}
