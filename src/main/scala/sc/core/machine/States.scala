package sc.core.machine

trait States {
  this: Terms with Envs with Stores with Continuations =>

  trait State

  // Evaluate a term
  case class Ev(focus: Term, ρ: Env, σ: Store, k: Cont) extends State
  // Continue with a value (or apply)
  case class Co(focus: Value, σ: Store, k: Cont) extends State
  // Unwind the stack
  case class Unwinding(jump: Jump, σ: Store, k: Cont) extends State


  // For simplicity, we write the step function
  // here rather than as a method of State.
  // This lets us define the states as case classes here
  // rather than using horrible extractors and factories.
  def step(s: State) = s match {
    case s @ Ev(_, _, _, _) => eval(s)
    case s @ Co(_, _, k) => continue(s)
    case s @ Unwinding(_, _, k) => unwind(s)
    case _ => None
  }

  // Default implementations of the step function for each kind of state.
  def eval(s: Ev): Option[State] = s match {
    case Ev(e, ρ, σ, k) => None
  }

  def continue(s: Co): Option[State] = s match {
    case Co(v, σ, k) => None
  }

  def unwind(s: Unwinding): Option[State] = s match {
    // The default implementation of unwinding is to pop the frame.
    case Unwinding(jump, σ, _::k) => Some(Unwinding(jump, σ, k))
    case Unwinding(jump, σ, Nil) => None
  }
}
