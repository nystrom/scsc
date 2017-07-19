package scsc.jssc

import org.scalatest._

class SCSpec extends FlatSpec with Matchers {

  import scsc.js._
  import scsc.js.Trees._
  import scsc.jssc._

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
        val result = SC.eval(e, 1000)
        result shouldBe (expected)
      case None =>
        fail
    }
  }

  "JSSC" should "supercompile append append" in {
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
        val result = SC.eval(e, 1000)
        result shouldBe (expected)
      case None =>
        fail
    }
  }
}
