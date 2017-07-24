package scsc.js

import org.scalatest._

class EvalSpec extends FlatSpec with Matchers {
  import scsc.js.JS._
  import scsc.js.Eval
  import terms._

  "JS" should "eval number literals" in {
    val e = Parser.fromString("8")
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "eval arithmetic" in {
    val e = Parser.fromString("1*2-3+4+5")
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "eval object literals" in {
    val e = Parser.fromString("var o = {x:8}; o.x")
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "eval fact(4) / fact(3) * fact(2)" in {
    val e = Parser.fromString("""{
      function f(n) { if (n==0) return 1; else return n*f(n-1); }
      f(4) * f(2) / f(3)
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "eval new objects" in {
    val e = Parser.fromString("""{
      function f() { this.x = 8 } ;
      (new f()).x
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "eval new objects with prototypes" in {
    val e = Parser.fromString("""{
      function f() { this.x = 8 } ;
      f.prototype.get = function () { return this.x } ;
      (new f()).get()
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "optimize pow(2,3) to 8" in {
    val e = Parser.fromString("""{
      function pow(x,n) { if (n==0) return 1; else return x*pow(x,n-1) }
      pow(2,3)
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate try/catch" in {
    val e = Parser.fromString("""{
      try { throw 8 } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate try/catch with conditional catch" in {
    val e = Parser.fromString("""{
      try { throw 1 } catch (e if e == 1) { 8 }
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate nested try/catch with failing conditional catch" in {
    val e = Parser.fromString("""{
      try { try { throw 8 } catch (e if e == 1) { 999 } } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate try/catch with failing conditional catch" in {
    val e = Parser.fromString("""{
      try { throw 8 } catch (e if e == 1) { 999 } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }


  "JS" should "evaluate try/finally with return" in {
    val e = Parser.fromString("""{
      function f() { try { return 1 } finally { return 8 } }
      f()
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate try/finally with throw" in {
    val e = Parser.fromString("""{
      function f() { try { throw 1 } finally { return 8 } }
      f()
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate break" in {
    val e = Parser.fromString("""{
      while (true) break; 8
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate for loops" in {
    val e = Parser.fromString("""{
      for (var i = 0; i < 8; i++) { } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate for loops with continue" in {
    val e = Parser.fromString("""{
      for (var i = 0; i < 8; i++) { if (i < 8) continue; i = 999 } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate while loops" in {
    val e = Parser.fromString("""{
      var i = 0; while (i < 8) { i++; } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate do-while loops" in {
    val e = Parser.fromString("""{
      var i = 16; do { i-- } while (i != 8); i
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate do-while loops with break" in {
    val e = Parser.fromString("""{
      var i = 9; do { i--; break } while (i); i
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate if true" in {
    val e = Parser.fromString("""{
      true ? 8 : 999
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate if false" in {
    val e = Parser.fromString("""{
      false ? 999 : 8
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JS" should "evaluate if constant cond" in {
    val e = Parser.fromString("""{
      (999 < 8) ? 999 : 8
    }
    """)
    e match {
      case Some(e) =>
        val result = Eval.eval(e)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }
}
