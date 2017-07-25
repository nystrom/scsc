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

  abstract override def step(s: State) = s match {
    case s @ Ev(_, _, _, _) => eval(s)
    case s @ Co(_, _, k) => k match {
      case Nil => None
      case frame::k => frame.step(s)
    }
    case s @ Unwinding(_, _, k) => k match {
      case Nil => None
      case frame::k => frame.unwind(s)
    }
  }
}
