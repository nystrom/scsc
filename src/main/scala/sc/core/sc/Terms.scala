package sc.core.sc

trait Terms extends sc.core.machine.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
