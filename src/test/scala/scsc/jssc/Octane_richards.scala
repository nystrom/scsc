package scsc.jssc

import org.scalatest._

class Octane_richards extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test12 = s"$dir/richards.js"

  "JSSC" should "eval richards.js" in {
    val e = Parser.fromFile(test12)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
