package scsc.jssc

import org.scalatest._

class Octane extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  val dir = s"${System.getProperty("user.dir")}/benchmarks/octane"

  val test1 = s"$dir/box2d.js"
  val test2 = s"$dir/crypto.js"
  val test3 = s"$dir/deltablue.js"
  val test4 = s"$dir/earley-boyer.js"
  val test5 = s"$dir/gbemu-part1.js"
  val test6 = s"$dir/gbemu-part2.js"
  val test7 = s"$dir/mandreel.js"
  val test8 = s"$dir/navier-stokes.js"
  val test9 = s"$dir/pdfjs.js"
  val test10 = s"$dir/raytrace.js"
  val test11 = s"$dir/regexp.js"
  val test12 = s"$dir/richards.js"
  val test13 = s"$dir/splay.js"
  val test14 = s"$dir/typescript-compiler.js"
  val test15 = s"$dir/typescript-input.js"
  val test16 = s"$dir/zlib-data.js"
  val test17 = s"$dir/zlib.js"

  "JSSC" should "eval box2d.js" in {
    val e = Parser.fromFile(test1)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval crypto.js" in {
    val e = Parser.fromFile(test2)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval deltablue.js" in {
    val e = Parser.fromFile(test3)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval earley-boyer.js" in {
    val e = Parser.fromFile(test4)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval gbemu-part1.js" in {
    val e = Parser.fromFile(test5)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval gbemu-part2.js" in {
    val e = Parser.fromFile(test6)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval mandreel.js" in {
    val e = Parser.fromFile(test7)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval navier-stokes.js" in {
    val e = Parser.fromFile(test8)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval pdfjs.js" in {
    val e = Parser.fromFile(test9)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval raytrace.js" in {
    val e = Parser.fromFile(test10)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval regexp.js" in {
    val e = Parser.fromFile(test11)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval richards.js" in {
    val e = Parser.fromFile(test12)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval splay.js" in {
    val e = Parser.fromFile(test13)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval typescript-compiler.js" in {
    val e = Parser.fromFile(test14)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval typescript-input.js" in {
    val e = Parser.fromFile(test15)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }

  "JSSC" should "eval zlib-data.js" in {
    val e = Parser.fromFile(test16)
    e match {
      case Some(e) => CESK.eval(e, 100) shouldBe (Undefined())
      case None => fail
    }
  }
}
