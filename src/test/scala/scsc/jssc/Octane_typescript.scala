package scsc.jssc

import org.scalatest._

class Octane_typescript extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test14 = s"$dir/typescript-compiler.js"
  val test15 = s"$dir/typescript-input.js"
  val test16 = s"$dir/typescript.js"

  "JSSC" should "eval typescript-compiler.js" in {
    val e = Parser.fromFile(test14)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval typescript-input.js" in {
    val e = Parser.fromFile(test15)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval typescript.js" in {
    val e = Parser.fromFile(test16)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
