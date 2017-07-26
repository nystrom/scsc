package sc.imp.sc

trait Rollback {
  this: States with Terms with Envs with Stores with Continuations =>

  // Rollback converts an active state to a residual state.
  // This happens either when splitting fails or when
  // the (meta) whistle blows, preventing a split.
  // Because some states cannot be residualized, it may
  // actually rollback the history. This is why it takes
  // a history and returns a new history.
  // Rollback can fail if the initial state of the history
  // is a split state. In this case, the split fails entirely
  // and the root of the split has to be rolled back.
  // In the worst case we rollback the entire history
  // to the initial state and residualize that.
  // This is safe, but clearly not desirable: a lot of work
  // for no gain.
  def rollback(hist: List[State]): Option[List[State]] = hist match {
    case Ev(e, ρ, σ, k)::tail =>
      Some(rebuildEv(e, ρ, σ, k)::tail)

    case Co(v, σ, k)::tail =>
      v match {
        case Path(loc, path) =>
          // cannot safely residualize a location
          tail match {
            // if this is the last state in the history, fail.
            case Nil => None
            case tail => rollback(tail)
          }
        case v =>
          Some(rebuildCo(v, σ, k)::tail)
      }

    case Unwinding(j, σ, k)::tail =>
      // OK, this is a problem too.
      // We need to ensure the landing pad is in
      // the continuation before rolling back
      // and ensure that ReStep reconstructs
      // the landing pad.
      // This prevents break and continue from
      // appearing outside a loop, or return outside
      // a function body.
      Some(rebuildUnwinding(j, σ, k)::tail)

    case _ =>
      None
  }

  def rebuildEv(e: Exp, ρ: Env, σ: Store, k: Cont): Re = e match {
    case For(label, Empty(), test, Empty(), body) =>
      rebuildEv(While(label, test, body), ρ, σ, k)

    case e =>
      println(s"simulating $e")
      println(s"initial σ = $σ")
      println(s"  final σ = ${simulateStore(e)(σ, ρ)}")
      Re(e, simulateStore(e)(σ, ρ), k)
  }

  def rebuildCo(v: Value, σ: Store, k: Cont): Re = {
    Re(v, σ, k)
  }

  def rebuildUnwinding(j: Jump, σ: Store, k: Cont): Re = {
    Re(j, σ, k)
  }
}
