package sc.imp.machine

class PPStates[S <: States](val states: S) {
  import states._

  protected object P extends org.bitbucket.inkytonik.kiama.output.PrettyPrinter

  // HACK: we should take a state here but the Scala compiler complains with,
  // essentially:
  // found   : sc.js.sc.JS.states.State
  // required: sc.js.sc.JS.states.State
  // and I'm tired and want to move on, so: use StateLike
  def pretty(t: State): String = t match {
    case s: State => P.layout(show(s))
    case _ => ???
  }
  def ugly(t: State): String = P.layout(P.any(t))

  protected def show(t: State): P.Doc = {
    import P._
    t match {
      case Ev(e, ρ, σ, k) =>
        text("Ev") <>
          nest(
            line <> text("e") <+> text("=") <+> any(e) <>
            line <> text("ρ") <+> text("=") <+> any(ρ) <>
            line <> text("σ") <+> text("=") <+> any(σ) <>
            line <> text("k") <+> text("=") <+> any(k)
        )
      case Co(v, σ, k) =>
        text("Co") <>
          nest(
            line <> text("v") <+> text("=") <+> any(v) <>
            line <> text("σ") <+> text("=") <+> any(σ) <>
            line <> text("k") <+> text("=") <+> any(k)
          )
      case Unwinding(j, σ, k) =>
        text("Unwinding") <>
          nest(
            line <> text("j") <+> text("=") <+> any(j) <>
            line <> text("σ") <+> text("=") <+> any(σ) <>
            line <> text("k") <+> text("=") <+> any(k)
          )
      case s => any(s) <> line
    }
  }
}
