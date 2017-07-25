package sc.core.machine

trait Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
  val machine: MachineType

  type Term
  type Value <: Term
  type Jump <: Term
}
