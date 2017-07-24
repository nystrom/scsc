package scsc.sc

import scsc.machine

trait Terms extends machine.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
