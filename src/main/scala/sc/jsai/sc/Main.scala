package sc.jsai.sc

import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}
import notjs.syntax._

object Main extends REPL {
  val banner = "Welcome to the Superconducting Supercompiler (JavaScript edition)!"

  override val prompt = "\nJSSC> "

  object Parser {
    import org.mozilla.javascript.ast.{AstNode => RhinoAST, AstRoot}

    def fromFile(file: String) = {
      import notjs.translator._
      import java.io.File

      val node = RunTranslator.parseJavaScript(new File(file))
      translate(node)
    }

    def translate(node: RhinoAST) = {
      import notjs.translator._
      import notjs.syntax._
      val prog = RunTranslator.translateAST(node, true) // we always convert print statements
      Topo.order(prog) // topologically order the Merge nodes
      prog
    }

    def fromString(input: String) = {
      import org.mozilla.javascript._
      import java.io.StringReader

      val reader = new StringReader(input)
      try {
        val node = new Parser().parse(reader, "(input)", 1)
        translate(node)
      } finally {
        reader.close()
      }
    }
  }

  def processline(source: Source, console: Console, config: REPLConfig): Option[REPLConfig] = {
    val input = source.content.trim
    input match {
      case "" =>
      case input =>
        val t = Parser.fromString(input)
        config.output().emitln(t)
        process(source, t, config)
    }

    Some(config)
  }

  def process(source: Source, s: Stmt, config: REPLConfig) {
    object SC extends sc.jsai.sc.Supercompiler
    val result = SC.supercompile(s)
    config.output().emitln(result)
    config.output().emitln(sc.util.PPAny.ugly(result))
  }
}
