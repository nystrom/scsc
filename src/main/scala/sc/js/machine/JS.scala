package sc.js.machine

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

  object Parser extends Parser[this.type](this)
  object TreeWalk extends TreeWalk[this.type](this)
  object Globals extends Globals[this.type](this)

  // Set up the initial environment and store.
  // lazy val ρ0: envs.Env = Globals.ρ0
  // lazy val σ0: stores.Store = Globals.σ0

  lazy val ρ0: envs.Env = Globals.ρMin
  lazy val σ0: stores.Store = Globals.σMin

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
    case class Ev(focus: Term, ρ: Env, σ: Store, k: Cont) extends super.Ev
    case class Co(focus: Value, σ: Store, k: Cont) extends super.Co
    case class Unwinding(jump: Jump, σ: Store, k: Cont) extends super.Unwinding

    object PP extends sc.imp.machine.PPStates[this.type](this)
  }

  object JSTerms extends Terms {
    type MachineType = JS.type
    val machine = JS

    object PP extends PP[this.type](this)
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
