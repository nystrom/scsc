package sc.core.sc

trait States extends sc.core.machine.States with Split {
  this: sc.core.machine.Terms with Envs with Stores with sc.core.machine.Continuations =>

  // Like a Continue, but with a residual expression in the focus.
  case class Re(residual: Term, σ: Store, k: List[Frame]) extends State

  override def step(s: State): Option[State] = s match {
    case s: Re => rebuild(s)
    case s => super.step(s)
  }

  def rebuild(s: Re): Option[State] = None
}
