package scsc.jssc

import org.scalatest._

class Octane_mandreel extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test7 = s"$dir/mandreel.js"

  "JSSC" should "eval mandreel.js" in {
    val e = Parser.fromFile(test7)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
