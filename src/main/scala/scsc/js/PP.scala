package scsc.js

object PP {
  import Trees._

  object P extends org.bitbucket.inkytonik.kiama.output.PrettyPrinter

  def pretty(t: Exp): String = P.layout(show(t))
  def ugly(t: Exp): String = P.layout(P.any(t))

  implicit def cvt(e: List[Exp]): List[P.Doc] = e.map(show)

  private def show(t: Exp): P.Doc = {
    import P._

    t match {
      case Prim(name) =>
        text(name)
      case Residual(e) =>
        text("/**/") <+> show(e) <+> text("/**/")
      case Unary(op, e) =>
        text(op.toString) <> parens(show(e))
      case IncDec(Prefix.++, e) =>
        text("++") <> show(e)
      case IncDec(Prefix.--, e) =>
        text("--") <> show(e)
      case IncDec(Postfix.++, e) =>
        show(e) <> text("++")
      case IncDec(Postfix.--, e) =>
        show(e) <> text("--")
      case Delete(e) =>
        text("delete") <> parens(show(e))
      case New(e) =>
        text("new") <> parens(show(e))
      case Typeof(e) =>
        text("typeof") <> parens(show(e))
      case Void(e) =>
        text("void") <> parens(show(e))
      case Assign(None, left, right) =>
        show(left) <+> text("=") <+> show(right)
      case Assign(Some(op), left, right) =>
        show(left) <+> text(s"$op=") <+> show(right)
      case Binary(op, left, right) =>
        show(left) <+> text(op.toString) <+> parens(show(right))
      case Seq(e1, e2) =>
        show(e1) <> semi <+> show(e2)
      case Break(Some(label)) =>
        text("break") <+> text(label) <> semi
      case Break(None) =>
        text("break") <> semi
      case Continue(Some(label)) =>
        text("continue") <+> text(label) <> semi
      case Continue(None) =>
        text("continue") <> semi
      case Call(f, args) =>
        show(f) <> parens(hsep(args, ","))
      case NewCall(f, args) =>
        text("new") <+> show(f) <> parens(hsep(args, ","))
      case Case(Some(test), body) =>
        text("case") <+> show(test) <> colon <> line <> nest(show(body)) <> line
      case Case(None, body) =>
        text("default") <> colon <> line <> nest(show(body)) <> line
      case Catch(ex, Some(test), body) =>
        text("catch") <+> text(ex) <+> show(test) <> colon <> line <> nest(show(body)) <> line
      case Catch(ex, None, body) =>
        text("catch") <+> text(ex) <> colon <> line <> nest(show(body)) <> line
      case Empty() =>
        emptyDoc
      case For(label, init, test, modify, body) =>
        text("for") <+> parens(show(init) <> semi <+> show(test) <> semi <+> show(modify)) <> line <> nest(show(body))
      case ForIn(label, element, collection, body) =>
        text("for") <+> parens(show(element) <+> text("in") <+> show(collection)) <> line <> nest(show(body))
      case ForEach(label, init, test, modify, body) =>
        text("for each") <+> parens(show(init) <> semi <+> show(test) <> semi <+> show(modify)) <> line <> nest(show(body))
      case Lambda(params, body) =>
        text("function") <+> parens(hsep(params.map(text), comma)) <> nest(show(body))
      case Scope(body) =>
        show(body)
      case Local(x) =>
        text(x)
      case LocalAddr(x) =>
        text(x)
      case IfElse(test, pass, fail) =>
        text("if") <+> parens(show(test)) <> line <> nest(braces(show(pass))) <> line <> text("else") <> line <> nest(braces(show(fail))) <> line
      case Index(a, i) =>
        show(a) <> brackets(show(i))
      case IndexAddr(a, i) =>
        show(a) <> brackets(show(i))
      case ArrayLit(es) =>
        text("Array") <> parens(hsep(es, comma))
      case Bool(false) =>
        text("false")
      case Bool(true) =>
        text("true")
      case Num(v) =>
        if (v.toInt == v) {
          text(v.toInt.toString)
        }
        else {
          text(v.toString)
        }
      case StringLit(v) =>
        squotes(text(v))
      case XML(v) =>
        text(v)
      case Regex(v, opts) =>
        text("/") <> text(v) <> text("/") <> text(opts)
      case Null() =>
        text("null")
      case Undefined() =>
        text("undefined")
      case ObjectLit(es) =>
        braces(hsep(es, comma))
      case Property(k, v, getter, setter) =>
        show(k) <> colon <+> show(v)
      case Return(Some(e)) =>
        text("return") <+> show(e)
      case Return(None) =>
        text("return")
      case Yield(Some(e)) =>
        text("yield") <+> show(e)
      case Yield(None) =>
        text("yield")
      case Switch(e, cases) =>
        text("switch") <+> parens(show(e)) <+> braces(vsep(cases, line))
      case Cond(test, pass, fail) =>
        show(test) <+> question <+> show(pass) <+> colon <+> show(fail)
      case Throw(e) =>
        text("throw") <+> show(e)
      case TryCatch(body, catches) =>
        text("try") <+> nest(braces(show(body))) <+> text("catch") <+> vsep(catches, line)
      case TryFinally(body, fin) =>
        text("try") <+> nest(braces(show(body))) <+> text("finally") <+> show(fin)
      case VarDef(x, init) =>
        text("var") <+> text(x) <+> text("=") <+> show(init)
      case LetDef(x, init) =>
        text("let") <+> text(x) <+> text("=") <+> show(init)
      case ConstDef(x, init) =>
        text("const") <+> text(x) <+> text("=") <+> show(init)
      case While(label, cond, body) =>
        text("while") <+> parens(show(cond)) <+> nest(braces(show(body)))
      case DoWhile(label, body, cond) =>
        text("do") <+> nest(braces(show(body))) <+> parens(show(cond))
      case With(exp, body) =>
        text("with") <+> parens(show(exp)) <+> show(body)
      case t =>
        value(t)
    }
  }
}