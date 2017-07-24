package scsc.js.sc

import scsc.machine

trait Terms extends scsc.js.Terms with scsc.imp.sc.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
