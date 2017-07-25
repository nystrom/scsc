package sc.js.sc

trait Terms extends sc.js.machine.Terms with sc.imp.sc.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
