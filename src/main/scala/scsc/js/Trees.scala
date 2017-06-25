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

  def fv(n: Exp): Set[Name] = n match {
    case _ => Set()
  }

  case class Loc(address: Int) extends Exp
  case class Residual(e: Exp) extends Exp

  type Name = String

  implicit class IV(n: Exp) {
    def isValue = n match {
      case Num(_) => true
      case Bool(_) => true
      case StringLit(_) => true
      case _ => false
    }
    def costZero = n match {
      case Ident(_) => true
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

  case class Unary(op: Operator, e: Exp) extends Exp
  case class IncDec(op: Operator, e: Exp) extends Exp
  case class Delete(e: Exp) extends Exp
  case class New(e: Exp) extends Exp
  case class Typeof(e: Exp) extends Exp
  case class Void(e: Exp) extends Exp
  case class Assign(op: Operator, left: Exp, right: Exp) extends Exp
  case class Binary(op: Operator, left: Exp, right: Exp) extends Exp

  object Assign {
    case object := extends Operator
    case object += extends Operator
    case object &= extends Operator
    case object |= extends Operator
    case object ^= extends Operator
    case object /= extends Operator
    case object %= extends Operator
    case object *= extends Operator
    case object >>= extends Operator
    case object <<= extends Operator
    case object >>>= extends Operator
    case object -= extends Operator
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

  case class Access(base: Exp, prop: Name) extends Exp
  case class Block(es: List[Exp]) extends Exp
  case class Break(label: Option[Name]) extends Exp
  case class Call(f: Exp, args: List[Exp]) extends Exp
  case class Case(test: Exp, body: Exp) extends Exp
  case class Catch(ex: Exp, test: Exp, body: Exp) extends Exp
  case class Continue(label: Option[Name]) extends Exp
  case class Empty() extends Exp
  case class Eval(e: Exp) extends Exp
  case class For(init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp
  case class FunDef(name: Name, params: List[Name], body: Exp) extends Exp
  case class Lambda(params: List[Name], body: Exp) extends Exp
  case class Ident(x: Name) extends Exp
  case class IfThen(test: Exp, pass: Exp) extends Exp
  case class IfElse(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Index(a: Exp, i: Exp) extends Exp
  case class Label(label: Name, body: Exp) extends Exp
  case class ArrayLit(es: List[Exp]) extends Exp
  case class Bool(v: Boolean) extends Exp
  case class Num(v: Double) extends Exp
  case class StringLit(v: String) extends Exp
  case class Null() extends Exp
  case class Undefined() extends Exp
  case class ObjectLit(es: List[Exp]) extends Exp
  case class Property(k: Exp, v: Exp) extends Exp
  case class Return(e: Option[Exp]) extends Exp
  case class Yield(e: Option[Exp]) extends Exp
  case class Switch(e: Exp, cases: List[Exp]) extends Exp
  case class Cond(test: Exp, pass: Exp, fail: Exp) extends Exp
  case class Throw(e: Exp) extends Exp
  case class Try(e: Exp, catches: List[Exp], fin: Option[Exp]) extends Exp
  case class VarDef(x: Name, init: Option[Exp]) extends Exp
  case class LetDef(x: Name, init: Option[Exp]) extends Exp
  case class ConstDef(x: Name, init: Option[Exp]) extends Exp
  case class While(cond: Exp, body: Exp) extends Exp
  case class DoWhile(body: Exp, cond: Exp) extends Exp
  case class With(exp: Exp, body: Exp) extends Exp
}
