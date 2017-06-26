package scsc.js

import scsc.jssc.CESK

object Main {
  def main(args: Array[String]) = {
    if (args.length > 0) {
      val filename = args(0)
      val program = Parser.fromFile(filename)
      program match {
        case Some(e) =>
          println(s"node $e")
          val result = CESK.eval(e, 100)
          println(s"result $result")
        case None =>
          println("parse failed")
      }
    }
    else {
      println("usage: Main file.js")
    }
  }
}
