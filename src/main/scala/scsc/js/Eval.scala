package scsc.js

object Eval {
  import JS._
  import terms._
  import states._

  def eval(e: Exp): Exp = {
    val s = inject(e)
    drive(s) match {
      case Co(v, _, _) => v
      case Ev(e, _, _, _) => e
      case Unwinding(j, _, _) => j
      case _ => e
    }
  }

  @scala.annotation.tailrec
  final def drive(s: State): State = {
    println(s"DRIVE ${PP.pretty(s)}")
    states.step(s) match {
      case Some(s1) =>
        drive(s1)
      case None =>
        s
    }
  }
}
