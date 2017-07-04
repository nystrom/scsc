package scsc.jssc

import org.scalatest._

class Octane_zlib extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test16 = s"$dir/zlib-data.js"
  val test17 = s"$dir/zlib.js"

  "JSSC" should "eval zlib-data.js" in {
    val e = Parser.fromFile(test16)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval zlib.js" in {
    val e = Parser.fromFile(test17)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
