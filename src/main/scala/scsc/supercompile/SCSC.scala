package scsc.supercompile

import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}
import scsc.syntax.LambdaSyntax.ASTNode
import scsc.syntax.LambdaSyntax.Exp
import scsc.syntax.Lambda
import scsc.syntax.LambdaPrettyPrinter

object SCSC extends REPL {
  val banner = "Welcome to the Superconducting Supercompiler!"

  object Posns extends Positions

  override val prompt = "\nSCSC> "

  def processline(source: Source, console: Console, config: REPLConfig): Option[REPLConfig] = {
    if (config.processWhitespaceLines() || (source.content.trim.length != 0)) {
      val p = new Lambda(source, Posns)
      val result = p.pRoot(0)

      if (result.hasValue) {
        result.semanticValue[ASTNode] match {
          case t: Exp =>
            config.output().emitln(LambdaPrettyPrinter.show(t))
            config.output().emitln(t)
            process(source, t, config)
          case _ =>
            config.output().emitln(p.formatParseError(result.parseError, true))
        }
      }
      else {
        config.output().emitln(p.formatParseError(result.parseError, true))
      }
    }

    Some(config)
  }

  def process(source: Source, e: Exp, config: REPLConfig) {
    val result = CEK.eval(e, 1000)
    config.output().emitln(LambdaPrettyPrinter.show(result))
  }
}
