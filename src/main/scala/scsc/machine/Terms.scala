package scsc.machine

trait Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
  val machine: MachineType

  type Name

  type Term
  type Value <: Term
  type Jump <: Term
}