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
  def rebuild(h: History): State

  // Reassemble the root with new children.
  // This can either merge split states or generate a new split.
  // If a new split, then we resume driving, otherwise we rebuild.
  def reassemble(root: State, children: List[History]): Either[List[State], State]

  // split the current state, return Nil on failure
  def split(s: State): List[State]
}
