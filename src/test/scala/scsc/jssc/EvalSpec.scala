package scsc.jssc

import org.scalatest._

class EvalSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  "JSSC" should "eval number literals" in {
    val e = Parser.fromString("8")
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval arithmetic" in {
    val e = Parser.fromString("1*2-3+4+5")
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval object literals" in {
    val e = Parser.fromString("var o = {x:8}; o.x")
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval new objects prototypes" in {
    val e = Parser.fromString("""{
      function f() { this.x = 8 } ;
      (new f()).x
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval new objects with prototypes" in {
    val e = Parser.fromString("""{
      function f() { this.x = 8 } ;
      f.prototype.get = function () { return this.x } ;
      (new f()).get()
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "optimize pow(2,3) to 8" in {
    val e = Parser.fromString("""{
      function pow(x,n) { if (n==0) return 1; else return x*pow(x,n-1) }
      pow(2,3)
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "optimize pow(a,3) to a*a*a" in {
    val e = Parser.fromString("""{
      function pow(x,n) { if (n==0) return 1; else return x*pow(x,n-1) }
      pow(a,3)
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe {
          Seq(
            VarDef("_v0",Undefined()),
            Seq(
              VarDef("_v1",Undefined()),
              Seq(
                VarDef("_v2",Undefined()),
                Seq(
                  VarDef("_v3",Undefined()),
                  Seq(
                    Seq(
                      Seq(
                        Seq(
                          Assign(None,Residual("_v0"),Local("a")),
                          Assign(None,Residual("_v1"),Binary(Binary.*,Residual("_v0"),Num(1.0)))),
                        Assign(None,Residual("_v2"),Binary(Binary.*,Residual("_v0"),Residual("_v1")))),
                      Assign(None,Residual("_v3"),Binary(Binary.*,Residual("_v0"),Residual("_v2")))),
                    Residual("_v3"))))))
        }

      case None =>
        fail
    }
  }

  "JSSC" should "evaluate try/catch" in {
    val e = Parser.fromString("""{
      try { throw 8 } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate try/catch with conditional catch" in {
    val e = Parser.fromString("""{
      try { throw 1 } catch (e if e == 1) { 8 }
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate nested try/catch with failing conditional catch" in {
    val e = Parser.fromString("""{
      try { try { throw 8 } catch (e if e == 1) { 999 } } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate try/catch with failing conditional catch" in {
    val e = Parser.fromString("""{
      try { throw 8 } catch (e if e == 1) { 999 } catch (e) { e }
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }


  "JSSC" should "evaluate try/finally with return" in {
    val e = Parser.fromString("""{
      function f() { try { return 1 } finally { return 8 } }
      f()
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate try/finally with throw" in {
    val e = Parser.fromString("""{
      function f() { try { throw 1 } finally { return 8 } }
      f()
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate break" in {
    val e = Parser.fromString("""{
      while (true) break; 8
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate for loops" in {
    val e = Parser.fromString("""{
      for (var i = 0; i < 8; i++) { } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate for loops with continue" in {
    val e = Parser.fromString("""{
      for (var i = 0; i < 8; i++) { if (i < 8) continue; i = 999 } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate while loops" in {
    val e = Parser.fromString("""{
      var i = 0; while (i < 8) { i++; } ; i
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate do-while loops" in {
    val e = Parser.fromString("""{
      var i = 16; do { i-- } while (i != 8); i
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate do-while loops with break" in {
    val e = Parser.fromString("""{
      var i = 9; do { i--; break } while (i); i
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate if true" in {
    val e = Parser.fromString("""{
      true ? 8 : 999
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate if false" in {
    val e = Parser.fromString("""{
      false ? 999 : 8
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate if constant cond" in {
    val e = Parser.fromString("""{
      (999 < 8) ? 999 : 8
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate if residual with merge" in {
    val e = Parser.fromString("""{
      x ? 8 : 8
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "evaluate if residual with non-merge" in {
    val e = Parser.fromString("""{
      x ? 8 : 999
    }
    """)
    e match {
      case Some(e) =>
        val result = SC.eval(e, 1000)
        result should matchPattern {
          case Seq(
            VarDef(x1,Undefined()),
            Seq(
              VarDef(y1,Undefined()),
              Seq(
                Seq(
                  Assign(None,Residual(x2),Local("x")),
                  IfElse(
                    Residual(x3),
                    Assign(None,Residual(y2),Num(8.0)),
                    Assign(None,Residual(y3),Num(999.0)))),
                Residual(y4)))) if x1 == x2 && x2 == x3 && y1 == y2 && y2 == y3 && y3 == y4 && x1 != y1 =>
        }
      case None =>
        fail
    }
  }
}
