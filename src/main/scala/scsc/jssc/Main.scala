package scsc.jssc

import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}
import scsc.js.Trees._
import scsc.js.PP

object Main extends REPL {
  val banner = "Welcome to the Superconducting Supercompiler (JavaScript edition)!"

  object Posns extends Positions

  override val prompt = "\nJSSC> "

  def processline(source: Source, console: Console, config: REPLConfig): Option[REPLConfig] = {
    if (config.processWhitespaceLines() || (source.content.trim.length != 0)) {
      val result = scsc.js.Parser.fromString(source.content)

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
    val result = e match {
      case e: Program =>
        CESK.evalProgram(e, 100)
      case e =>
        CESK.eval(e, 100)
    }
    config.output().emitln(result)
    config.output().emitln(PP.pretty(result))
  }
}
