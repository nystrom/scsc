package scsc.core

trait Terms {
  type Term
  type Value <: Term
  type Residual <: Term
}
