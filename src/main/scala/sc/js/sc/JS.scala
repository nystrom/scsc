package sc.js.sc

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

  object Parser extends sc.js.machine.Parser[JS.type](JS)
  object TreeWalk extends sc.js.machine.TreeWalk[JS.type](JS)
  object Globals extends sc.js.machine.Globals[JS.type](JS)

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

    object ReStep extends ResidualStep[machine.type](machine)
    object CoSplit extends CoSplit[machine.type](machine)
    object EvSplit extends EvSplit[machine.type](machine)
    object Rollback extends Rollback[machine.type](machine)

    object PP extends sc.imp.machine.PPStates[this.type](this)
  }

  object JSTerms extends Terms {
    type MachineType = JS.type
    val machine = JS

    object PP extends sc.js.machine.PP[this.type](this)
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
