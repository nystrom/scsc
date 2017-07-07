package scsc.jssc

import org.scalatest._

class JSSCSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

  "JSSC" should "eval number literals" in {
    val e = Parser.fromString("3")
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
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

  "JSSC" should "eval new objects prototypes" in {
    val e = Parser.fromString("""{
      function f() { this.x = 3 } ;
      (new f()).x
    }
    """)
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }

  "JSSC" should "eval new objects with prototypes" in {
    val e = Parser.fromString("""{
      function f() { this.x = 3 } ;
      f.prototype.get = function () { return this.x } ;
      (new f()).get()
    }
    """)
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }

  "JSSC" should "supercompile map inc" in {
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
    e match {
      case Some(e) =>
        val result = CESK.eval(e, 100)
        result shouldBe (Num(3.0))
      case None =>
        fail
    }
  }
}
