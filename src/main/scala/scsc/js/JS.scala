package scsc.js

// concrete implementation of the machine
// this is just to ensure everything compiles
object JS extends Machine {
  type StatesType = JSStates.type
  type EnvsType = JSEnvs.type
  type StoresType = JSStores.type
  type ContinuationsType = JSContinuations.type
  type TermsType = JSTerms.type

  val states = JSStates
  val envs = JSEnvs
  val stores = JSStores
  val continuations = JSContinuations
  val terms = JSTerms

  object JSStates extends States {
    type MachineType = JS.type
    val machine = JS

    import terms._
    import envs._
    import stores._
    import continuations._

    object Ev extends EvFactory
    object Co extends CoFactory
    object Unwinding extends UnwindingFactory
    object Re extends ResidualFactory
    case class Ev(focus: Term, ρ: Env, σ: Store, k: Cont) extends super.Ev
    case class Co(focus: Value, σ: Store, k: Cont) extends super.Co
    case class Unwinding(jump: Jump, σ: Store, k: Cont) extends super.Unwinding
    case class Re(residual: Term, σ: Store, k: Cont) extends super.Re
  }

  object JSTerms extends Terms {
    type MachineType = JS.type
    val machine = JS
  }

  object JSContinuations extends Continuations {
    type MachineType = JS.type
    val machine = JS
  }

  object JSEnvs extends Envs {
    type MachineType = JS.type
    val machine = JS
  }

  object JSStores extends Stores {
    type MachineType = JS.type
    val machine = JS
  }
}
