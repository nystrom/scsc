package scsc.js

import java.io._

object Main {
  def main(args: Array[String]) = {
    if (args.length > 0) {
      val filename = args(0)
      val astRoot = Parser.fromFile(filename)
      astRoot match {
        case Some(e) => println(s"node $e")
        case None => println("parse failed")
      }
    }
    else {
      println("usage: Main file.js")
    }
  }
}
