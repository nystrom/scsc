package sc.js.machine

import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}

object Main extends REPL {
  import JS._

  val banner = "Welcome to the Superconducting Supercompiler (JavaScript edition)!"

  object Posns extends Positions

  override val prompt = "\nJS> "

  def processline(source: Source, console: Console, config: REPLConfig): Option[REPLConfig] = {
    val input = source.content.trim
    input match {
      case "" =>
      case input =>
        val result = Parser.fromString(input)
        result match {
          case Some(t) =>
            config.output().emitln(t)
            process(source, t, config)
          case None =>
            config.output().emitln("could not parse")
        }
    }

    Some(config)
  }

  def process(source: Source, e: Exp, config: REPLConfig) {
    val result = Eval.eval(e)
    config.output().emitln(result)
    config.output().emitln(PP.pretty(result))
  }
}
