package scsc.jssc

import org.scalatest._

class JSSCSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  "JSSC" should "eval number literals" in {
    val e = Parser.fromString("1")
    e match {
      case Some(Program(e)) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(1.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval arithmetic" in {
    val e = Parser.fromString("1+2")
    e match {
      case Some(Program(e)) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval objects" in {
    val e = Parser.fromString("var o = {x:3}; o.x")
    e match {
      case Some(Program(e)) =>
        val result = CESK.eval(e, 100)
        result should matchPattern {
          case Residual(Block(List(Block(List(VarDef("o", _), Undefined())), Num(3.0)))) =>
          case Residual(Block(List(VarDef("o", _), Undefined(), Num(3.0)))) =>
          case Residual(Block(List(VarDef("o", _), Num(3.0)))) =>
          case Residual(Block(List(Num(3.0)))) =>
          case Residual(Num(3.0)) =>
          case Num(3.0) =>
        }
      case None =>
        fail
    }
  }
}
