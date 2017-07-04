package scsc.jssc

import org.scalatest._

class Octane_crypto extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test2 = s"$dir/crypto.js"

  "JSSC" should "eval crypto.js" in {
    val e = Parser.fromFile(test2)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
