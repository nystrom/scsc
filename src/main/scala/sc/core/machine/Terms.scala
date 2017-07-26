package sc.core.machine

trait Terms {
  type Term
  type Value <: Term
  type Jump <: Term
}
