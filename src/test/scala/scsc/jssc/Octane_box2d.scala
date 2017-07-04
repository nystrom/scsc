package scsc.jssc

import org.scalatest._

class Octane_box2d extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test1 = s"$dir/box2d.js"

  "JSSC" should "eval box2d.js" in {
    val e = Parser.fromFile(test1)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
