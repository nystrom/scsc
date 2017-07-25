package sc.js.machine

class PP[M <: Machine](m: M) extends sc.imp.machine.PP[M](m) {
  import machine._
  import terms._

  private implicit def cvt(e: List[Exp]): List[P.Doc] = e.map(show)

  override protected def show(t: Exp): P.Doc = {
    import P._

    t match {
      case Prim(name) =>
        text(name)
      case Residual(name) =>
        text(name)
      case Delete(e) =>
        text("delete") <> parens(show(e))
      case Typeof(e) =>
        text("typeof") <> parens(show(e))
      case Void(e) =>
        text("void") <> parens(show(e))
      case NewCall(f, args) =>
        text("new") <+> show(f) <> parens(hsep(args, ","))
      case Case(Some(test), body) =>
        text("case") <+> show(test) <> colon <> line <> nest(show(body)) <> line
      case Case(None, body) =>
        text("default") <> colon <> line <> nest(show(body)) <> line
      case ForIn(label, element, collection, body) =>
        text("for") <+> parens(show(element) <+> text("in") <+> show(collection)) <> line <> nest(show(body))
      case ForEach(label, init, test, modify, body) =>
        text("for each") <+> parens(show(init) <> semi <+> show(test) <> semi <+> show(modify)) <> line <> nest(show(body))
      case Num(v) =>
        if (v.toInt == v) {
          text(v.toInt.toString)
        }
        else {
          text(v.toString)
        }
      case XML(v) =>
        text(v)
      case Regex(v, opts) =>
        text("/") <> text(v) <> text("/") <> text(opts)
      case Yield(Some(e)) =>
        text("yield") <+> show(e)
      case Yield(None) =>
        text("yield")
      case Switch(e, cases) =>
        text("switch") <+> parens(show(e)) <+> braces(vsep(cases, line))
      case VarDef(x, Undefined()) =>
        text("var") <+> text(x)
      case VarDef(x, Lambda(params, body)) =>
        text("function") <+> text(x) <> parens(hsep(params.map(text), comma)) <> nest(braces(show(body)))
      case VarDef(x, init) =>
        text("var") <+> text(x) <+> text("=") <+> show(init)
      case With(exp, body) =>
        text("with") <+> parens(show(exp)) <+> show(body)
      case t =>
        super.show(t)
    }
  }
}
