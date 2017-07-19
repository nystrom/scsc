package scsc.jssc

import org.scalatest._

class Octane_deltablue extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test3 = s"$dir/deltablue.js"

  "JSSC" should "eval deltablue.js" in {
    val e = Parser.fromFile(test3)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
