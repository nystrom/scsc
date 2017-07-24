package scsc.machine

trait Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
  val machine: MachineType

  import machine._
  import states._

  final type Cont = List[Frame]

  type Frame
}
