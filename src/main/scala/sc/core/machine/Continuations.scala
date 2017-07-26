package sc.core.machine

trait Continuations {
  type Frame
  final type Cont = List[Frame]
}
