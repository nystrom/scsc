package scsc.jssc

import org.scalatest._

class Octane_earley_boyer extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test4 = s"$dir/earley-boyer.js"

  "JSSC" should "eval earley-boyer.js" in {
    val e = Parser.fromFile(test4)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
