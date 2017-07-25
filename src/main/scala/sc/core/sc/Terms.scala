package sc.core.sc

import sc.core.machine

trait Terms extends machine.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
