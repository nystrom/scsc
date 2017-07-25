package scsc.machine

trait States {
  type MachineType <: Machine { type StatesType = States.this.type }
  val machine: MachineType

  import machine._
  import continuations.Frame
  import stores.Store
  import envs.Env
  import terms.{Term, Value, Jump}

  def step(s: State): Option[State] = s.step

  type State <: StateLike

  trait StateLike {
    def step: Option[State]
  }

  // Evaluate a term
  trait EvalLike extends StateLike {
    def focus: Term
    def ρ: Env
    def σ: Store
    def k: List[Frame]
  }

  trait ContinueLike extends StateLike {
    def focus: Value
    def σ: Store
    def k: List[Frame]
  }

  // The Unwinding state just pops continuations until hitting a call or loop or catch.
  trait UnwindingLike extends StateLike {
    def jump: Term
    def σ: Store
    def k: List[Frame]
  }

  import terms.Term
  import continuations.Cont

  type Ev <: State with EvalLike
  val Ev: EvFactory
  trait EvFactory {
    def apply(focus: Term, ρ: Env, σ: Store, k: Cont): Ev
    def unapply(s: Ev): Option[(Term, Env, Store, Cont)]
  }

  type Co <: State with ContinueLike
  val Co: CoFactory
  trait CoFactory {
    def apply(focus: Value, σ: Store, k: Cont): Co
    def unapply(s: Co): Option[(Value, Store, Cont)]
  }

  type Unwinding <: State with UnwindingLike
  val Unwinding: UnwindingFactory
  trait UnwindingFactory {
    def apply(focus: Jump, σ: Store, k: Cont): Unwinding
    def unapply(s: Unwinding): Option[(Jump, Store, Cont)]
  }
}
