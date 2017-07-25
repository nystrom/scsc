package sc.imp.machine

import sc.core.machine

trait States extends machine.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import continuations._

  val PP: PPStates[this.type]

  implicit class PPDecorate(n: State) {
    def pretty: String = PP.pretty(n)
    def ugly: String = PP.ugly(n)
  }

  trait State extends StateLike
  trait Ev extends State with EvalLike {
    def step = eval(this)
  }
  trait Co extends State with ContinueLike {
    def step = k match {
      case Nil => None
      case frame::k => frame.step(this)
    }
  }
  trait Unwinding extends State with UnwindingLike {
    def step = k match {
      case Nil => None
      case frame::k => frame.unwind(this)
    }
  }
}
