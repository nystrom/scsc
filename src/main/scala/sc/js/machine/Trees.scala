package sc.js.machine

trait Trees extends sc.imp.machine.Trees {
  private type Name = String

  val PP: PP[this.type]

  implicit class PPDecorate3(n: Exp) {
    def pretty: String = PP.pretty(n)
    def ugly: String = PP.ugly(n)
  }

  // New operators
  object JSArray {
    case object Delete extends Operator
    case object MethodAddress extends Operator
  }

  object JSUnary {
    case object TYPEOF extends Operator
  }

  object JSBinary {
    case object BIND extends Operator
    case object COMMALEFT extends Operator
    case object COMMARIGHT extends Operator
    case object === extends Operator
    case object IN extends Operator
    case object INSTANCEOF extends Operator
    case object !== extends Operator
  }

  object JSNary {
    case object NewCall extends Operator
    case object MethodCall extends Operator
  }

  // JS-specific expressions.

  type Bool = BooleanLit
  val Bool = BooleanLit
  type Num = DoubleLit
  val Num = DoubleLit

  case class XML(v: String) extends Lit
  case class Regex(v: String, opts: String) extends Lit
  case class Prim(name: String) extends Lit

  case class Delete(e: Exp) extends Exp
  case class Typeof(e: Exp) extends Exp
  case class Void(e: Exp) extends Exp
  case class NewCall(f: Exp, args: List[Exp]) extends Exp        // MISSING
  case class ForIn(label: Option[Name], init: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class ForEach(label: Option[Name], init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class Yield(e: Option[Exp]) extends Exp  // MISSING
  case class Case(test: Option[Exp], body: Exp) extends Exp // MISSING
  case class Switch(e: Exp, cases: List[Exp]) extends Exp // MISSING
  case class With(exp: Exp, body: Exp) extends Exp  // MISSING

  case class Residual(x: Name) extends Value with Var

}
