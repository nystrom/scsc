package scsc.core

object Unsplit {
  type Unsplitter[State] = List[List[State]] => UnsplitResult[State]

  sealed trait UnsplitResult[State]
  case class Resplit[State](ss: List[State], unsplit: Unsplitter[State]) extends UnsplitResult[State] {
    require(ss.nonEmpty)
  }
  case class UnsplitOk[State](s: State) extends UnsplitResult[State]
  case class UnsplitFail[State]() extends UnsplitResult[State]
}
