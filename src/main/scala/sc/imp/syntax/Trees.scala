package sc.imp.syntax

trait Trees {
  private type Name = String

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

}
