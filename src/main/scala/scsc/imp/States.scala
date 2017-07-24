package scsc.imp

import scsc.machine

trait States extends machine.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import continuations._

  def step(s: State) = s.step

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
  trait Re extends State with ResidualLike {
    def step = None
  }
}
