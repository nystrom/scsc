package scsc.jssc

import org.scalatest._

class Octane_raytrace extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test10 = s"$dir/raytrace.js"

  "JSSC" should "eval raytrace.js" in {
    val e = Parser.fromFile(test10)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
