package sc.core.sc

trait Split {
  this: States =>

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
}
