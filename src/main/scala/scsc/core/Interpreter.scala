package scsc.core

trait Interpreter[State] {
  private type History = List[State]

  // Step to the next state
  def step(s: State): Option[State]

  // Check if we should stop driving.
  def whistle(h: History): Boolean

  // Fold the last element of the current history with a previous element, truncating
  // the history. The new last element of the history generalizes the old last element
  // and the previous element.
  // FIXME: other SC algorithms aren't restricted to folding with ancestors.
  def fold(h: History): Option[History]

  // Construct a new state from the current history.
  // This is not allowed to fail!
  // Since states in the history are all equivalent, we can just reutrn
  // any state in the history, but clearly the first (newest) state is best.
  def rebuild(h: History): State

  // Rebuild the c
  // Replace the history with a new history. Returns Nil on failure.
  def rollback(h: History): History

  // split the current state, return None on failure
  def split(s: State): Option[(List[State], Unsplit)]

  // reassemble a split using the root state and the histories of the
  // split states
  type Unsplit = List[List[State]] => Either[List[State], State]
}
