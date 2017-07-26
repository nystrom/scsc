package sc.imp.machine

trait Terms extends sc.core.machine.Terms with sc.imp.syntax.Trees {
  this: Stores =>

  type Term = Exp
  private type Name = String

  case class Path(loc: Loc, path: Exp) extends Value with Var

  val PP: PP[this.type]

  implicit class PPDecorate(n: Exp) {
    def pretty: String = PP.pretty(n)
    def ugly: String = PP.ugly(n)
  }


  // Extractor for loops with conditionals at the entry.
  val Loop: Loop
  trait Loop {
    def unapply(loop: Exp): Option[(Option[Name], Exp, Exp)] = loop match {
      case While(label, test, body) =>
        Some((label, body, loop))
      case For(label, _, test, iter, body) =>
        Some((label, body, Seq(iter, loop)))
      case _ =>
        None
    }
  }
}
