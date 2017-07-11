package scsc.jssc

import org.scalatest._

class SCSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  "JSSC" should "eval number literals" in {
    val e = Parser.fromString("8")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval arithmetic" in {
    val e = Parser.fromString("1*2-3+4+5")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval object literals" in {
    val e = Parser.fromString("var o = {x:8}; o.x")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
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
        val result = CESK.eval(e, 100)
        result shouldBe (Num(8.0))
      case None =>
        fail
    }
  }

  "JSSC" should "supercompile map inc" ignore {
    val e = Parser.fromString("""{
      function cons(head, tail) {
          this.head = head;
          this.tail = tail;
      }
      function map(f, xs) {
          if (xs == null)
            return null
          else
            cons(f(xs.head), map(f, xs.tail))
      }
      function inc(x) {
          return x+1;
      }
      map(inc, ys)
    }
    """)
    val expected = Parser.fromString("""{
      function map1(xs) {
          if (xs == null)
            return null
          else
            cons(xs.head + 1, map1(xs.tail))
      }
      map1(ys)
    }
    """)
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (expected)
      case None =>
        fail
    }
  }

  "JSSC" should "supercompile append append" ignore {
    val e = Parser.fromString("""{
      function cons(head, tail) {
          this.head = head;
          this.tail = tail;
      }
      function append(xs, ys) {
          if (xs == null)
            return ys
          else
            cons(xs.head, append(xs.tail, ys))
      }
      append(append(as, bs), cs)
    }
    """)
    val expected = Parser.fromString("""{
      function append3(xs, ys, zs) {
          if (xs == null)
            return append(ys, zs)
          else
            cons(xs.head, append3(xs.tail, ys, zs))
      }
      append3(as, bs, cs)
    }
    """)
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (expected)
      case None =>
        fail
    }
  }
}
