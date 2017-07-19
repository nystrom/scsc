package scsc.jssc

import org.scalatest._

class Octane_gbemu extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test5 = s"$dir/gbemu-part1.js"
  val test6 = s"$dir/gbemu-part2.js"

  "JSSC" should "eval gbemu-part1.js" in {
    val e = Parser.fromFile(test5)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval gbemu-part2.js" in {
    val e = Parser.fromFile(test6)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
