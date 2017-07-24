package scsc.js

import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}

object Main extends REPL {
  import JS._
  import terms._
  import states._

  val banner = "Welcome to the Superconducting Supercompiler (JavaScript edition)!"

  object Posns extends Positions

  override val prompt = "\nJSSC> "

  def processline(source: Source, console: Console, config: REPLConfig): Option[REPLConfig] = {
    if (config.processWhitespaceLines() || (source.content.trim.length != 0)) {
      val result = Parser.fromString(source.content)
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
