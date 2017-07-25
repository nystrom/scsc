package sc.imp.machine

import sc.core.machine

trait States extends machine.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import continuations._

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
