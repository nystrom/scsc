package sc.imp.sc

trait Terms extends sc.imp.machine.Terms with sc.core.sc.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }

  def reify(e: Exp): Exp
}
