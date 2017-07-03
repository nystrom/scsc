package scsc.js

import jdk.nashorn.internal.ir._
import jdk.nashorn.internal.parser.{Parser => JSParser}

// JS Parser using Nashorn
object Parser {
  import jdk.nashorn.internal.runtime.Context
  import jdk.nashorn.internal.runtime.ErrorManager
  import jdk.nashorn.internal.runtime.Source
  import jdk.nashorn.internal.runtime.options.Options

  import Trees._

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

  def fromFile(path: String): Option[Scope] = {
    val source = Source.sourceFor(path, new java.io.File(path))
    val parser = new JSParser(context.getEnv, source, errors)
    parser.parse match {
      case null => None
      case n => MakeTrees.make(n)
    }
  }
}
