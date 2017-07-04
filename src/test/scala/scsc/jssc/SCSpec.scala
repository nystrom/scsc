package scsc.jssc

import org.scalatest._

class JSSCSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  "JSSC" should "eval number literals" in {
    val e = Parser.fromString("1")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(1.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval arithmetic" in {
    val e = Parser.fromString("1+2")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval object literals" in {
    val e = Parser.fromString("{ var o = {x:3}; o.x }")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }
}
