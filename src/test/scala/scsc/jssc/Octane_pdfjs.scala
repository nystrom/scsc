package scsc.jssc

import org.scalatest._

class Octane_pdfjs extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test9 = s"$dir/pdfjs.js"

  "JSSC" should "eval pdfjs.js" in {
    val e = Parser.fromFile(test9)
    e match {
      case Some(e) => SC.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
