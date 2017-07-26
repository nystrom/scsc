package sc.util

object PPAny {
  protected object P extends org.bitbucket.inkytonik.kiama.output.PrettyPrinter
  def ugly(t: Any): String = P.layout(P.any(t))
}
