package sc.imp.machine

// concrete implementation of the machine
// this is just to ensure everything compiles
object Imp extends Machine {
  type StatesType = ImpStates.type
  type EnvsType = ImpEnvs.type
  type StoresType = ImpStores.type
  type ContinuationsType = ImpContinuations.type
  type TermsType = ImpTerms.type

  val states = ImpStates
  val envs = ImpEnvs
  val stores = ImpStores
  val continuations = ImpContinuations
  val terms = ImpTerms

  val ρ0 = envs.ρempty
  val σ0 = stores.σempty

  object ImpStates extends States {
    type MachineType = Imp.type
    val machine = Imp

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

    object PP extends PPStates[this.type](this)
  }

  object ImpTerms extends Terms {
    type MachineType = Imp.type
    val machine = Imp

    import envs.Env
    import stores.Store
    import continuations.Cont
    import states.State

    def doCall(op: Operator, operands: List[Value], ρ: Env, σ: Store, k: Cont): Option[State] = None

    def evalUnaryOp(op: Operator, v: Value): Option[Value] = None
    def evalBinaryShortCircuitOp(op: Operator, v1: Value): Option[Value] = None
    def evalBinaryOp(op: Operator, v1: Value, v2: Value): Option[Value] = None

    def evalArrayOp(op: Operator, array: Value, index: Value, σ: Store): Option[(Value, Store)] = None

    def evalPredicate(v: Value): Option[Boolean] = None

    def addDeclarations(e: Exp, ρ: Env, σ: Store): (List[Exp], Env, Store) = (Nil, ρ, σ)

    object Loop extends Loop

    object PP extends PP[this.type](this)
  }

  object ImpContinuations extends Continuations {
    type MachineType = Imp.type
    val machine = Imp
  }

  object ImpEnvs extends Envs {
    type MachineType = Imp.type
    val machine = Imp
  }

  object ImpStores extends Stores {
    type MachineType = Imp.type
    val machine = Imp
  }
}
