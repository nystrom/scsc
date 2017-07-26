package sc.js.syntax

import jdk.nashorn.internal.ir._
import jdk.nashorn.internal.parser.{Parser => JSParser}

// JS Parser using Nashorn
class Parser[T <: Trees](val trees: T) {
  import jdk.nashorn.internal.runtime.Context
  import jdk.nashorn.internal.runtime.ErrorManager
  import jdk.nashorn.internal.runtime.Source
  import jdk.nashorn.internal.runtime.options.Options

  import trees._

  object MakeTrees extends MakeTrees[trees.type](trees)

  lazy val options = {
    val o = new Options("nashorn")
    o.set("anon.functions", true)
    o.set("parse.only", true)
    o.set("scripting", true)
    o
  }

  lazy val errors = new ErrorManager()
  lazy val context = new Context(options, errors, Thread.currentThread.getContextClassLoader)

  def fromString(input: String): Option[Scope] = {
    val source = Source.sourceFor("(input)", input)
    val parser = new JSParser(context.getEnv, source, errors)
    parser.parse match {
      case null => None
      case n => MakeTrees.make(n)
    }
  }

  // support multiple files.
  def fromFile(paths: String*): Option[Scope] = {
    val trees = paths map {
      path =>
        val source = Source.sourceFor(path, new java.io.File(path))
        val parser = new JSParser(context.getEnv, source, errors)
        parser.parse
    }
    trees match {
      case trees if trees.exists(_ == null) => None
      case trees =>
        val n = trees.foldLeft(Some(Undefined()): Option[Exp]) {
          case (Some(result), tree) =>
            val n = MakeTrees.make(tree)
            n match {
              case Some(Scope(p)) => Some(Seq(result, p))
              case None => None
            }
          case (None, _) => None
        }
        n map {
          n => MakeTrees.desugar(Scope(n))
        }
    }
  }
}
