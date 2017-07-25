package sc.core.machine

trait States {
  type MachineType <: Machine { type StatesType = States.this.type }
  val machine: MachineType

  import machine._
  import continuations.Cont
  import stores.Store
  import envs.Env
  import terms.{Term, Value, Jump}

  trait State

  // For simplicity, we write the step function
  // here rather than as a method of State.
  // This lets us define the states as case classes here
  // rather than using horrible extractors and factories.
  def step(s: State): Option[State] = None

  // Evaluate a term
  case class Ev(focus: Term, ρ: Env, σ: Store, k: Cont) extends State
  // Continue with a value (or apply)
  case class Co(focus: Value, σ: Store, k: Cont) extends State
  // Unwind the stack
  case class Unwinding(jump: Jump, σ: Store, k: Cont) extends State
}
