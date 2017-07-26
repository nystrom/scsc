package sc.core.sc

trait States extends sc.core.machine.States {
  this: sc.core.machine.Terms with Envs with Stores with Continuations =>

  // Like a Continue, but with a residual expression in the focus.
  case class Re(residual: Term, σ: Store, k: List[Frame]) extends State

  // split a state. Like step we don't define it as a member of State
  import sc.core.sc.Unsplit.Unsplitter

  type History = List[State]

  def split(s: State): Option[(List[State], Unsplitter[State])] = s match {
    case s @ Ev(_, _, _, _) => evsplit(s)
    case s @ Co(_, _, _) => cosplit(s)
    case s @ Unwinding(_, _, _) => None
    case s @ Re(_, _, _) => None
  }

  def evsplit(s: Ev): Option[(List[State], Unsplitter[State])] = None
  def cosplit(s: Co): Option[(List[State], Unsplitter[State])] = None

  override def step(s: State): Option[State] = s match {
    case s: Re => rebuild(s)
    case s => super.step(s)
  }

  def rebuild(s: Re): Option[State] = None
}
