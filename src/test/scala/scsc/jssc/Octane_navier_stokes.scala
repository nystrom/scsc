package scsc.jssc

import org.scalatest._

class Octane_navier_stokes extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test8 = s"$dir/navier-stokes.js"

  "JSSC" should "eval navier-stokes.js" in {
    val e = Parser.fromFile(test8)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
