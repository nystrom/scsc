package scsc.jssc

import org.scalatest._

class Octane_splay extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test13 = s"$dir/splay.js"

  "JSSC" should "eval splay.js" in {
    val e = Parser.fromFile(s"$dir/base.js", test13, s"$dir/run.js")
    e match {
      case Some(e) =>
        val r = CESK.eval(e, 100)
        println(scsc.js.PP.pretty(r))
        r shouldBe (Undefined())
      case None => fail
    }
  }
}
