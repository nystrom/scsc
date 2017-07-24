package scsc.machine

trait Machine {
  type StatesType <: States { type MachineType = Machine.this.type }
  type EnvsType <: Envs { type MachineType = Machine.this.type }
  type StoresType <: Stores { type MachineType = Machine.this.type }
  type ContinuationsType <: Continuations { type MachineType = Machine.this.type }
  type TermsType <: Terms { type MachineType = Machine.this.type }

  val states: StatesType
  val envs: EnvsType
  val stores: StoresType
  val continuations: ContinuationsType
  val terms: TermsType

  import envs.Env
  import stores.Store
  import continuations.Cont
  import terms.Term
  import states.{State, Ev}

  val ρ0: Env
  val σ0: Store
  val k0: Cont = Nil

  // Inject a term into the machine.
  def inject(e: Term): State = Ev(e, ρ0, σ0, k0)
}
