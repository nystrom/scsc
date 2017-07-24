package scsc.imp.sc

import scsc.imp

trait Terms extends imp.Terms with scsc.sc.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }
}
