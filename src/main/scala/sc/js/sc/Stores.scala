package sc.js.sc

trait Stores extends sc.js.machine.Stores with sc.imp.sc.Stores {
  this: sc.js.machine.Terms with Envs =>

  import scala.collection.mutable.ListBuffer

  // FIXME: extend to handle residuals, which ARE Not in the store!
  // But they can be if we extend σ to have arbitrary constraints.
  // Which we should do to handle the Bool vs. CvtBool problem.
  override def extendWithCond(test: Exp, σAfterTest: Store, ρ: Env, result: Boolean): Store = {
    test match {
      case Binary(Binary.&&, e1, e2) if result =>
        extendWithCond(e2, extendWithCond(e1, σAfterTest, ρ, true), ρ, true)
      case Binary(Binary.||, e1, e2) if ! result =>
        extendWithCond(e2, extendWithCond(e1, σAfterTest, ρ, false), ρ, false)
      case Unary(Prefix.!, e) =>
        extendWithCond(e, σAfterTest, ρ, ! result)

      case Binary(JSBinary.===, Local(x), v: Value) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(Binary.==, Local(x), v: Value) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(JSBinary.!==, Local(x), v: Value) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(Binary.!=, Local(x), v: Value) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }

      case Binary(JSBinary.===, v: Value, Local(x)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(Binary.==, v: Value, Local(x)) if result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(JSBinary.!==, v: Value, Local(x)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }
      case Binary(Binary.!=, v: Value, Local(x)) if ! result =>
        ρ.get(x) match {
          case Some(loc) => σAfterTest.assign(loc, v)
          case None => σAfterTest
        }

      case Local(x) =>
        ρ.get(x) match {
          case Some(loc) =>
            // FIXME should't do this... x is not true, it's something that can
            // be coerced to true.
            σAfterTest.assign(loc, Bool(result))
          case None =>
            σAfterTest
        }

      case Residual(x) =>
        ρ.get(x) match {
          case Some(loc) =>
            // FIXME should't do this... x is not true, it's something that can
            // be coerced to true.
            σAfterTest.assign(loc, Bool(result))
          case None =>
            σAfterTest
        }

      case _ =>
        σAfterTest
    }
  }

  override def simulateStore(e: Exp)(σ0: Store, ρ: Env): Store = {
    import sc.js.syntax.TreeWalk
    object T extends TreeWalk[this.type](this)

    object Simulator extends T.Rewriter {
      var σ = σ0
      override def rewrite(e: Exp) = e match {
        case Assign(op, left, right) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case IncDec(op, left) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case Delete(left) =>
          σ = invalidateLocation(left)(σ, ρ)
          super.rewrite(e)
        case Call(f, args) =>
          σ = invalidateHeap(σ, ρ)
          e
        case NewCall(f, args) =>
          σ = invalidateHeap(σ, ρ)
          e
        case Lambda(params, body) =>
          // do nothing
          e
        case With(exp, body) =>
          σ = invalidateHeap(σ, ρ)
          super.rewrite(e)
        case e =>
          super.rewrite(e)
      }
    }
    Simulator.rewrite(e)
    Simulator.σ
  }

  def invalidateHeap(σ: Store, ρ: Env): Store = {
    σ collect {
      case (loc, v) if (σ0 contains loc) => (loc, v)
      case (loc, v) if ρ.exists { case (x, loc1) => loc == loc1 } => (loc, v)
    }
  }

  def invalidateLocation(e: Exp)(σ: Store, ρ: Env): Store = e match {
    case Residual(x) =>
      invalidateLocation(Local(x))(σ, ρ)

    case Path(loc, path) =>
      // Remove the location
      σ + (loc -> UnknownClosure())

    case Local(x) =>
      ρ.get(x) match {
        case Some(loc) => σ + (loc -> UnknownClosure())
        case None => σ
      }

    case Index(a, StringLit(i)) =>
      // Remove all properties named i
      val addrs: Iterable[Loc] = σ flatMap {
        case (_, BlobClosure(JSBlob(_, _, _, props), _)) =>
          props collect {
            case (k, loc) if k == i => loc
          }
        case _ => Nil
      }

      addrs.foldLeft(σ) {
        case (σ, loc) => σ + (loc -> UnknownClosure())
      }

    case Index(a, i) =>
      // Remove ALL properties in the store
      val addrs: Iterable[Loc] = σ flatMap {
        case (_, BlobClosure(JSBlob(_, _, _, props), _)) =>
          props map {
            case (k, loc) => loc
          }
        case _ => Nil
      }

      addrs.foldLeft(σ) {
        case (σ, loc) => σ + (loc -> UnknownClosure())
      }

    case _ =>
      σ
  }
}
