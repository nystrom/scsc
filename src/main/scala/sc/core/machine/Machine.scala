package sc.core.machine

trait Machine {
  this: Terms with States with Envs with Stores with Continuations =>

  val ρ0: Env
  val σ0: Store
  val k0: Cont = Nil

  // Inject a term into the machine.
  def inject(e: Term): State = Ev(e, ρ0, σ0, k0)
}
