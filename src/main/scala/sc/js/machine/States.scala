package sc.js.machine

trait States extends sc.imp.machine.States {
  this: Terms with Envs with Stores with Continuations with JSSemantics =>

  // override the step function for JS specific semantics
  override abstract def step(s: State) = s match {
    case Ev(focus, ρ, σ, k) =>
      focus match {
        case Typeof(e) =>
          Some(Ev(e, ρ, σ, DoTypeof(ρ)::k))
        case Void(e) =>
          // void(e) just evaluates e and discards it
          Some(Ev(e, ρ, σ, FocusCont(Undefined())::k))
        case Call(Index(e, m), args) =>
          // Method call
          // We need to capture the receiver as well as the method address
          Some(Ev(e, ρ, σ, EvalIndex(JSArray.MethodAddress, m, ρ)::EvalArgs(JSNary.MethodCall, args, ρ)::k))
        case NewCall(fun, args) =>
          Some(Ev(fun, ρ, σ, EvalProto(args, ρ)::k))

        case lam @ Lambda(xs, e) =>
          // Put the lambda in the heap.

          // Make a prototype object for the function.
          val protoBlobLoc = FreshHeapLoc()
          val protoPropLoc = FreshHeapLoc()
          val protoBlob = JSBlob("object", getPrimAddress(Prim("Object.prototype")), None, Nil)

          // Functions also have a length property (the function arity).
          val lengthPropLoc = FreshHeapLoc()
          val lengthBlobLoc = FreshHeapLoc()
          val lengthValue = Num(xs.length)

          // Make the function blob itself.
          val loc = FreshHeapLoc()
          val blob = JSBlob("function", getPrimAddress(Prim("Function.prototype")), Some(lam), ("prototype", protoPropLoc)::("length", lengthPropLoc)::Nil)

          Some(Co(Path(loc, lam), σ.assign(loc, blob, ρ).assign(protoPropLoc, protoBlobLoc).assign(protoBlobLoc, protoBlob, ρ).assign(lengthPropLoc, lengthBlobLoc).assign(lengthBlobLoc, lengthValue), k))

        case _ =>
          super.step(s)
      }

    case Co(v, σ, DoBinaryOp(op, v1, ρ)::k) =>
      // The imp semantics ignore the store, which we need!
      val result: Option[Value] = (op, v1, v) match {
        case (JSBinary.IN, i, Path(loc: HeapLoc, path)) =>
          // Does the property i exist in loc?
          σ.get(loc) match {
            case Some(BlobClosure(_, _)) =>
              getPropertyAddress(loc, i, σ) match {
                case Some(v) =>
                  Some(Bool(true))
                case None =>
                  Some(Bool(false))
              }
            case _ =>
              None
          }
        case (JSBinary.INSTANCEOF, Null(), _) =>
          Some(Bool(false))
        case (JSBinary.INSTANCEOF, Undefined(), _) =>
          Some(Bool(false))
        case (JSBinary.INSTANCEOF, v1 @ Path(addr1, path1), v2 @ Path(addr2: HeapLoc, path2)) =>
          // x instanceof y
          // ==
          // x.__proto__ === y.prototype
          val result = for {
            BlobClosure(JSBlob(_, v1protoLoc, _, _), _) <- σ.get(addr1)
            v2protoLoc <- getPropertyAddress(addr2, StringLit("prototype"), σ)
          } yield (v1protoLoc, v2protoLoc)

          result map {
            case (proto1, proto2) => Bool(proto1 == proto2)
          }
        case _ =>
          None
      }

      result match {
        case Some(v) => Some(Co(v, σ, k))
        case None => super.step(s)
      }

    case _ =>
      super.step(s)
  }
}
