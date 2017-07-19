package scsc.jssc

import org.scalatest._

class Octane_regexp extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test11 = s"$dir/regexp.js"

  "JSSC" should "eval regexp.js" in {
    val e = Parser.fromFile(test11)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
