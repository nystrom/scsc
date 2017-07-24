package scsc.js

import scsc.imp

trait Terms extends imp.Terms {
  type MachineType <: Machine { type TermsType = Terms.this.type }

  import machine._

  import envs.Env
  import stores._
  import states._
  import continuations._

  def reify(e: Exp): Exp = {
    import TreeWalk._

    object Reify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Path(_, path) => super.rewrite(path)
        case e => super.rewrite(e)
      }
    }

    Reify.rewrite(e)
  }

  def unreify(e: Exp): Exp = {
    import TreeWalk._

    object Unreify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(x) => Local(x)
        case e => super.rewrite(e)
      }
    }

    Unreify.rewrite(e)
  }

  def doCall(op: Operator, operands: List[Value], ρ: Env, σ: Store, k: Cont): Option[State] = {
    // Pad the arguments with undefined.
    def pad(params: List[Name], args: List[Value]): List[Value] = (params, args) match {
      case (Nil, _) => Nil
      case (_::params, Nil) => Undefined()::pad(params, Nil)
      case (_::params, arg::args) => arg::pad(params, args)
    }

    println(s"doCall $op $operands")

    op match {
      case Nary.InitObject =>
        // Arguments should be PairValues all. Create a new object.
        val locs = operands map { _ => FreshHeapLoc() }
        val props = (operands zip locs) collect {
          case (PairValue(CvtString(key), value), loc) => (key, loc)
        }
        if (props.length == operands.length) {
          val propValues = operands collect {
            case PairValue(_, value) => value
          }
          val σ2 = (locs zip propValues).foldLeft(σ) {
            case (σ, (loc, v)) => σ.assign(loc, v)
          }

          val loc = FreshHeapLoc()
          val blob = JSBlob("object", getPrimAddress(Prim("Object.prototype")), None, props)
          Some(Co(Path(loc, ObjectLit(operands)), σ2.assign(loc, blob, ρ), k))
        }
        else {
          None
        }

      case Nary.InitArray =>
        // Arguments are the array elements.
        val locs = operands map { _ => FreshHeapLoc() }
        val props = locs.zipWithIndex collect {
          case (loc, i) => (i.toString, loc)
        }
        val lengthLoc = FreshHeapLoc()
        val σ2 = (locs zip operands).foldLeft(σ.assign(lengthLoc, Num(operands.length))) {
          case (σ, (loc, v)) => σ.assign(loc, v)
        }

        val loc = FreshHeapLoc()
        val blob = JSBlob("object", getPrimAddress(Prim("Array.prototype")), None, ("length", lengthLoc)::props)
        Some(Co(Path(loc, ArrayLit(operands)), σ2.assign(loc, blob, ρ), k))

      case Nary.Call =>
        operands match {
          case Path(loc, path)::args =>
            val thisValue = Prim("window")

            σ.get(loc) match {
              case Some(BlobClosure(JSBlob(_, _, Some(Lambda(xs, body)), _), ρ1)) =>
                val xthis = "this"

                val formals = xthis::xs
                val actuals: List[Value] = thisValue::pad(xs, args)

                // Make the stack slots for the parameters
                val locs = formals map { x => FreshStackLoc() }

                // Extend the environment from the closure (not the current environment).
                val ρ2 = (formals zip locs).foldLeft(ρ1) {
                  case (ρ1, (x, loc)) => ρ1 + (x -> loc)
                }

                // Initialize the parameters.
                val σ2 = (locs zip actuals).foldLeft(σ) {
                  case (σ, (loc, v)) => σ.assign(loc, v)
                }

                // Evaluate the body.
                Some(Ev(body, ρ2, σ2, CallFrame(ρ)::k))

              case Some(ValueClosure(Prim(fun))) =>
                // The function is primitive.
                evalPrim(fun, args, ρ, σ) map {
                  // Use Ev, not Co... the prim might be eval and return the expression to eval.
                  case (e, σ1) => Ev(e, ρ, σ1, k)
                }
              case _ =>
                None
            }

          case Prim(fun)::args =>
            evalPrim(fun, args, ρ, σ) map {
              case (e, σ1) => Ev(e, ρ, σ1, k)
            }
          case _ =>
            None
        }

      case JSNary.MethodCall =>
        operands match {
          case PairValue(thisValue, Path(loc, path))::args =>
            σ.get(loc) match {
              case Some(BlobClosure(JSBlob(_, _, Some(Lambda(xs, body)), _), ρ1)) =>
                val xthis = "this"

                val formals = xthis::xs
                val actuals: List[Value] = thisValue::pad(xs, args)

                // Make the stack slots for the parameters
                val locs = formals map { x => FreshStackLoc() }

                // Extend the environment from the closure (not the current environment).
                val ρ2 = (formals zip locs).foldLeft(ρ1) {
                  case (ρ1, (x, loc)) => ρ1 + (x -> loc)
                }

                // Initialize the parameters.
                val σ2 = (locs zip actuals).foldLeft(σ) {
                  case (σ, (loc, v)) => σ.assign(loc, v)
                }

                // Evaluate the body.
                Some(Ev(body, ρ2, σ2, CallFrame(ρ)::k))

              case Some(ValueClosure(Prim(fun))) =>
                // The function is primitive.
                evalPrim(fun, args, ρ, σ) map {
                  // Use Ev, not Co... the prim might be eval and return the expression to eval.
                  case (e, σ1) => Ev(e, ρ, σ1, k)
                }
              case _ =>
                None
            }
          case _ =>
            None
        }

      case JSNary.NewCall =>
        operands match {
          case Path(loc, path)::Path(protoLoc: HeapLoc, protoPath)::args =>
            σ.get(loc) match {
              case Some(BlobClosure(JSBlob(_, _, Some(Lambda(xs, body)), _), ρ1)) =>
                // Create a new blob with no properties
                val newObj = FreshHeapLoc()
                val newBlob = JSBlob("object", protoLoc, None, Nil)
                val σ1 = σ.assign(newObj, newBlob, ρ)

                val xthis = "this"

                val formals = xthis::xs
                val actuals: List[Value] = Path(newObj, NewCall(path, args))::pad(xs, args)

                // Make the stack slots for the parameters
                val locs = formals map { x => FreshStackLoc() }

                // Extend the environment from the closure (not the current environment).
                val ρ2 = (formals zip locs).foldLeft(ρ1) {
                  case (ρ1, (x, loc)) => ρ1 + (x -> loc)
                }

                // Initialize the parameters.
                val σ2 = (locs zip actuals).foldLeft(σ1) {
                  case (σ, (loc, v)) => σ.assign(loc, v)
                }

                // Evaluate the body.
                // But shift the focus after to return the new object.
                Some(Ev(body, ρ2, σ2, CallFrame(ρ)::FocusCont(Path(newObj, NewCall(path, args)))::k))

              case _ =>
                None
            }
          case _ =>
            None
        }

    }
  }

  object JSArray {
    case object Delete extends Operator
    case object MethodAddress extends Operator
  }

  // override def doCall(funAndArgs: List[Value], ρ: Env, σ: Store, k: Cont): Option[State]

  def evalPrim(prim: Name, args: List[Value], ρ: Env, σ: Store): Option[(Exp, Store)] = {
    val r = (prim, args) match {
      case ("eval", StringLit(code)::_) => Parser.fromString(code)
      case ("eval", Value(v)::_) => Some(v)
      case ("eval", Nil) => Some(Undefined())
      case ("isNaN", CvtNum(v)::_) => Some(Bool(v.isNaN))
      case ("isNaN", Nil) => Some(Bool(true))
      case ("isFinite", CvtNum(v)::_) => Some(Bool(!v.isInfinite))
      case ("isFinite", Nil) => Some(Bool(false))
      case ("String.indexOf", StringLit(s)::StringLit(c)::Nil) => None
      case ("String.charAt", StringLit(s)::CvtNum(i)::Nil) => None /// Some(StringLit(s(i.toInt).toString))
      case ("Regex.exec", Regex(re, opts)::StringLit(s)::Nil) => None /// Some(StringLit(s(i.toInt).toString))
      case ("Math.abs", CvtNum(v)::_) => Some(Num(v.abs))
      case ("Math.sqrt", CvtNum(v)::_) => Some(Num(math.sqrt(v)))
      case ("Math.floor", CvtNum(v)::_) => Some(Num(math.floor(v)))
      case ("Math.ceil", CvtNum(v)::_) => Some(Num(math.ceil(v)))
      case ("Math.round", CvtNum(v)::_) => None
      case ("Math.trunc", CvtNum(v)::_) => None
      case ("Math.exp", CvtNum(v)::_) => Some(Num(math.exp(v)))
      case ("Math.log", CvtNum(v)::_) => Some(Num(math.log(v)))
      case ("Math.sin", CvtNum(v)::_) => Some(Num(math.sin(v)))
      case ("Math.cos", CvtNum(v)::_) => Some(Num(math.cos(v)))
      case ("Math.tan", CvtNum(v)::_) => Some(Num(math.tan(v)))
      case ("Math.asin", CvtNum(v)::_) => Some(Num(math.asin(v)))
      case ("Math.acos", CvtNum(v)::_) => Some(Num(math.acos(v)))
      case ("Math.atan", CvtNum(v)::_) => Some(Num(math.atan(v)))
      case ("Math.pow", CvtNum(v1)::CvtNum(v2)::_) => Some(Num(math.pow(v1, v2)))
      case ("Math.atan2", CvtNum(v1)::CvtNum(v2)::_) => Some(Num(math.atan2(v1, v2)))
      case ("Math.max", es) =>
        val r = es.foldLeft(Option(-1.0/0.0)) {
          case (Some(v1), CvtNum(v2)) => Some(math.max(v1, v2))
          case _ => None
        }
        r map { v => Num(v) }
      case ("Math.min", es) =>
        val r = es.foldLeft(Option(1.0/0.0)) {
          case (Some(v1), CvtNum(v2)) => Some(math.min(v1, v2))
          case _ => None
        }
        r map { v => Num(v) }
      case _ => None
    }

    // Add the store to the result
    r map { r => (r, σ) }
  }

  def getPrimAddress(p: Prim): HeapLoc = {
    machine.σ0 foreach {
      case (loc: HeapLoc, ValueClosure(q)) if p == q =>
        return loc
      case _ =>
    }
    throw new RuntimeException(s"missing primitive $p")
  }

  def getPropertyAddress(loc: stores.HeapLoc, i: Value, σ: Store) = {
    import stores._

    σ.get(loc) match {
      case Some(BlobClosure(JSBlob(typeof, proto, lambda, props), _)) =>
        props collectFirst {
          case (k, v) if evalBinaryOp(Binary.==, StringLit(k), i) == Some(Bool(true)) => v
        }
      case _ => None
    }
  }

  def evalArrayOp(op: Operator, array: Value, index: Value, σ: Store): Option[(Value, Store)] = {
    import stores._

    println(s"ARRAY OP $op $array[$index]")

    (array, index) match {
      case (array @ Path(arrayLoc: HeapLoc, arrayPath), index @ CvtString(indexString)) =>
        σ.get(arrayLoc) match {
          case Some(ValueClosure(_)) | Some(LocClosure(_)) =>
            // the array address does not store a blob.
            // Return undefined (for all ops!)
            Some((Undefined(), σ))

          case Some(BlobClosure(JSBlob(typeof, proto, lambda, props), ρ)) =>
            val propLoc = props collectFirst {
              case (k, v) if evalBinaryOp(Binary.==, StringLit(k), index) == Some(Bool(true)) => v
            }
            propLoc match {
              case Some(propLoc) =>
                println(s"propLoc = $propLoc")
                // found
                val path = Path(propLoc, Index(arrayPath, index))
                op match {
                  case Array.Address =>
                    // return the property location
                    Some((path, σ))
                  case JSArray.MethodAddress =>
                    // Load the property, which should be an address.
                    σ.get(propLoc) match {
                      case Some(LocClosure(loc)) =>
                        println(s"*propLoc = $loc")
                        Some((PairValue(array, Path(loc, Index(path, index))), σ))
                      case _ =>
                        None
                    }
                  case Array.Load =>
                    // return the contents of the property location
                    σ.get(propLoc) match {
                      case Some(LocClosure(loc)) =>
                        Some((Path(loc, Index(path, index)), σ))
                      case Some(ValueClosure(v)) =>
                        Some((v, σ))
                      case _ =>
                        None
                    }
                  case JSArray.Delete =>
                    // remove the property from the blob
                    val removed = props filter {
                      case (k, v) if v == propLoc => false
                      case _ => true
                    }
                    Some((array, σ.assign(arrayLoc, JSBlob(typeof, proto, lambda, removed), ρ)))
                  case _ => None
                }
              case None =>
                // The property is missing.
                op match {
                  case Array.Address =>
                    // Create it.
                    val propLoc = FreshHeapLoc()
                    val σ1 = σ.assign(arrayLoc, JSBlob(typeof, proto, lambda, props :+ (indexString, propLoc)), ρ)
                    val σ2 = σ1.assign(propLoc, Undefined())
                    val path = Path(propLoc, Index(arrayPath, index))
                    Some((path, σ2))
                  case Array.Load =>
                    // Try the prototype.
                    val path = Path(proto, Index(arrayPath, index))
                    evalArrayOp(op, path, index, σ)
                  case JSArray.Delete =>
                    // Nothing to delete, just return the original array.
                    Some((array, σ))
                  case JSArray.MethodAddress =>
                    // Try the prototype.
                    val path = Path(proto, Index(arrayPath, index))
                    evalArrayOp(op, path, index, σ) map {
                      // if we get a result, adjust the receiver
                      case (PairValue(_, m), σ1) => (PairValue(array, m), σ1)
                      case (v, σ1) => (v, σ1)
                    }

                  case _ => None
                }
            }
          case _ =>
            // the array address is missing from the heap
            None
      }
      case (array, index) =>
        // The array (object) is not an object!
        // Return undefined.
        // This usually happens when array is a Prim.
        Some((Undefined(), σ))
    }
  }

  def evalUnaryOp(op: Operator, v: Value): Option[Value] = {
    (op, v) match {
      case (Prefix.!, CvtBool(v)) => Some(Bool(!v))
      case (Prefix.~, CvtNum(v)) => Some(Num(~v.toLong))
      case (Prefix.+, CvtNum(v)) => Some(Num(+v))
      case (Prefix.-, CvtNum(v)) => Some(Num(-v))
      case _ => None
    }
  }

  def evalBinaryShortCircuitOp(op: Operator, v1: Value): Option[Value] = {
    (op, v1) match {
      case (Binary.&&, CvtBool(false)) => Some(v1)
      case (Binary.||, CvtBool(true)) => Some(v1)
      case _ => None
    }
  }

  def evalBinaryOp(op: Operator, v1: Value, v2: Value): Option[Value] = {
    (op, v1, v2) match {
      case (Binary.+, StringLit(n1), StringLit(n2)) => Some(StringLit(n1 + n2))
      case (Binary.+, StringLit(n1), CvtString(n2)) => Some(StringLit(n1 + n2))
      case (Binary.+, CvtString(n1), StringLit(n2)) => Some(StringLit(n1 + n2))

      case (Binary.+, CvtNum(n1), CvtNum(n2)) => Some(Num(n1 + n2))
      case (Binary.+, CvtString(n1), CvtString(n2)) => Some(StringLit(n1 + n2))

      case (Binary.-, CvtNum(n1), CvtNum(n2)) => Some(Num(n1 - n2))
      case (Binary.*, CvtNum(n1), CvtNum(n2)) => Some(Num(n1 * n2))
      case (Binary./, CvtNum(n1), CvtNum(n2)) => Some(Num(n1 / n2))
      case (Binary.%, CvtNum(n1), CvtNum(n2)) => Some(Num(n1 % n2))

      case (Binary.&, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong & n2.toLong))
      case (Binary.|, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong | n2.toLong))
      case (Binary.^, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong ^ n2.toLong))
      case (Binary.>>, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong >> n2.toLong))
      case (Binary.<<, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong << n2.toLong))
      case (Binary.>>>, CvtNum(n1), CvtNum(n2)) => Some(Num(n1.toLong >>> n2.toLong))

      case (Binary.<, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Some(Bool(n1 < n2))
      case (Binary.<=, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Some(Bool(n1 <= n2))
      case (Binary.>, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Some(Bool(n1 > n2))
      case (Binary.>=, CvtPrim(StringLit(n1)), CvtPrim(StringLit(n2))) => Some(Bool(n1 >= n2))

      case (Binary.<, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Some(Undefined())
      case (Binary.<=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Some(Undefined())
      case (Binary.>, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Some(Undefined())
      case (Binary.>=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) if n1.isNaN || n2.isNaN => Some(Undefined())

      case (Binary.<, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Some(Bool(n1 < n2))
      case (Binary.<=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Some(Bool(n1 <= n2))
      case (Binary.>, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Some(Bool(n1 > n2))
      case (Binary.>=, CvtPrim(Num(n1)), CvtPrim(Num(n2))) => Some(Bool(n1 >= n2))

      case (Binary.&&, CvtBool(n1), CvtBool(n2)) => Some(Bool(n1 && n2))
      case (Binary.||, CvtBool(n1), CvtBool(n2)) => Some(Bool(n1 || n2))

      case (JSBinary.BIND, v1, v2) =>
        println("ERROR: unimplemented ${Binary(op, v1, v2).pretty}")
        None

      case (JSBinary.COMMALEFT, v1, v2) => Some(v1)
      case (JSBinary.COMMARIGHT, v1, v2) => Some(v2)

      // Equality operators should not work on residuals.
      // So match after the above.

      case (Binary.!=, v1, v2) => evalBinaryOp(Binary.==, v1, v2) collect {
        case Bool(v) => Bool(!v)
      }

      case (JSBinary.!==, v1, v2) => evalBinaryOp(JSBinary.===, v1, v2) collect {
        case Bool(v) => Bool(!v)
      }

      case (Binary.==, Null(), Undefined()) => Some(Bool(true))
      case (Binary.==, Undefined(), Null()) => Some(Bool(true))
      case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[StringLit] => Some(Bool(n1 == n2))
      case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[StringLit] => Some(Bool(n1 == n2))
      case (Binary.==, Num(n1), v2 @ CvtNum(n2)) if v2.isInstanceOf[Bool] => Some(Bool(n1 == n2))
      case (Binary.==, v1 @ CvtNum(n1), Num(n2)) if v1.isInstanceOf[Bool] => Some(Bool(n1 == n2))

      case (Binary.==, Path(n1, _), Path(n2, _)) if n1 == n2 => Some(Bool(true))

      // We don't handle object literals, so just reify.
      case (Binary.==, v1 @ Path(n1, _), v2) => None
      case (Binary.==, v1, v2 @ Path(n2, _)) => None

      // Residual values can be compared for equality too
      case (Binary.==, Residual(x1), Residual(x2)) if x1 == x2 => Some(Bool(true))
      case (Binary.==, v1, v2 @ Residual(x2)) => None
      case (Binary.==, v1 @ Residual(x1), v2) => None

      // for other cases, just use ===.
      case (Binary.==, v1, v2) => evalBinaryOp(JSBinary.===, v1, v2)

      case (JSBinary.===, Undefined(), Undefined()) => Some(Bool(true))
      case (JSBinary.===, Null(), Null()) => Some(Bool(true))
      case (JSBinary.===, Num(n1), Num(n2)) => Some(Bool(n1 == n2))
      case (JSBinary.===, StringLit(n1), StringLit(n2)) => Some(Bool(n1 == n2))
      case (JSBinary.===, Bool(n1), Bool(n2)) => Some(Bool(n1 == n2))
      case (JSBinary.===, Path(n1, _), Path(n2, _)) => Some(Bool(n1 == n2)) // same object

      // Residual values can be compared for equality too
      case (JSBinary.===, Residual(x1), Residual(x2)) if x1 == x2 => Some(Bool(true))
      case (JSBinary.===, v1, v2 @ Residual(x2)) => None
      case (JSBinary.===, v1 @ Residual(x1), v2) => None

      case (JSBinary.===, v1, v2) => Some(Bool(false)) // all other cases should be false

      // Failure
      case (op, v1, v2) =>
        println(s"ERROR: cannot apply ${Binary(op, v1, v2).pretty}")
        None
    }
  }

  case class Residual(x: Name) extends Value with Var

  def evalPredicate(v: Value): Option[Boolean] = v match {
    case CvtBool(b) => Some(b)
    case _ => None
  }

  def addDeclarations(e: Exp, ρ: Env, σ: Store): (List[Exp], Env, Store) = {
    import stores._

    // Go through all the bindings in the block and add them to the environment
    // as `undefined`. As we go thorugh the block, we'll initialize the variables.
    object CollectBindings extends TreeWalk.Rewriter {
      var bindings: Vector[(Name, Exp)] = Vector()
      override def rewrite(e: Exp) = e match {
        case VarDef(x, e) =>
          bindings = bindings :+ ((x, e))
          super.rewrite(e)
        case _: Scope =>
          // don't recurse on nested scopes
          e
        case e =>
          super.rewrite(e)
      }
    }
    CollectBindings.rewrite(e)
    val bindings = CollectBindings.bindings

    val locs = bindings map { case (x, e) => FreshStackLoc() }
    val ρ1 = (bindings zip locs).foldLeft(ρ) {
      case (ρ, ((x, _), loc)) => ρ + (x -> loc)
    }
    val σ1 = locs.foldLeft(σ) {
      case (σ, loc) => σ.assign(loc, Undefined())
    }

    val defs = bindings map {
      case (x, e @ Lambda(xs, body)) => VarDef(x, e)
      case (x, e) => VarDef(x, Undefined())
    }

    // MakeTrees ensures builds the tree so that function bindings
    // are evaluated first, so we don't have to initialize them explicitly.
    // Also all bindings should be either to lambdas or to undefined.
    (defs.toList, ρ1, σ1)
  }

  object Loop extends Loop

  import states._
  import stores._
  import continuations._

  implicit class PPDecorate(n: Exp) {
    def pretty: String = PP.pretty(n)
    def ugly: String = PP.ugly(n)
  }

  object CvtPrim {
    def unapply(e: Exp) = e match {
      case e: Undefined => Some(e)
      case e: Null => Some(e)
      case e: Bool => Some(e)
      case e: Num => Some(e)
      case e: IntLit => Some(e)
      case e: StringLit => Some(e)
      // TODO: call toString and valueOf methods if they exist.
      // case e: ObjectLit => Some(e)
      // case e: ArrayLit => Some(e)
      case _ => None
    }
  }

  object CvtBool {
    def unapply(e: Exp): Option[Boolean] = e match {
      case Bool(v) => Some(v)
      case Undefined() => Some(false)
      case Null() => Some(false)
      case Num(v) => Some(v != 0 && ! v.isNaN)
      case IntLit(v) => Some(v != 0)
      case StringLit(v) => Some(v != "")
      case Path(_, _) => Some(true)
      case XML(_) => Some(true)
      case Regex(_, _) => Some(true)
      case v => None
    }
  }

  object CvtNum {
    def unapply(e: Exp): Option[Double] = e match {
      case Num(v) => Some(v)
      case IntLit(v) => Some(v.toDouble)
      case Undefined() => Some(Double.NaN)
      case Null() => Some(0)
      case Bool(false) => Some(0)
      case Bool(true) => Some(1)

      // same as CvtStrictNum but more returns NaN more often
      case StringLit(v) =>
        try {
          Some(java.lang.Double.parseDouble(v))
        }
        catch {
          case ex: java.lang.NumberFormatException =>
            Some(Double.NaN)
        }
      case Path(_, _) => Some(Double.NaN)
      case v => None
    }
  }

  object CvtString {
    def unapply(e: Exp) = e match {
      case XML(v) => Some(v)
      case Regex(v, opts) => Some(s"/$v/$opts")
      case StringLit(v) => Some(v)
      case ObjectLit(es) => Some(es.map(_.pretty).mkString("{", ",", "}"))
      case ArrayLit(es) => Some(es.map(_.pretty).mkString("[", ",", "]"))
      case Lambda(xs, e) => Some("<function>")
      case Value(e) => Some(e.pretty)
      case _ => None
    }
  }

  object Value {
    def unapply(e: Value) = Some(e)
  }

/*
  def fv(n: Exp): Set[Name] = {
    import scsc.js.TreeWalk._

    class FV() extends Rewriter {
      import scala.collection.mutable.HashSet

      val vars = HashSet.empty[Name]
      def getVars = vars.toSet
      val defs = HashSet.empty[Name]
      def getDefs = defs.toSet

      override def rewrite(t: Exp): Exp = t match {
        case t @ Local(x) =>
          vars += x
          t
        case t @ Lambda(xs, e) =>
          vars ++= (fv(e) -- xs)
          t
        case t @ Scope(e) =>
          vars ++= fv(e)
          t
        case t @ VarDef(x, _) =>
          defs += x
          super.rewrite(t)
        case t =>
          super.rewrite(t)
      }
    }

    val t = new FV()
    t.rewrite(n)
    t.getVars -- t.getDefs
  }
  */

  // JS-specific binary operators.

  object JSUnary {
    case object TYPEOF extends Operator
  }

  object JSBinary {
    case object BIND extends Operator
    case object COMMALEFT extends Operator
    case object COMMARIGHT extends Operator
    case object === extends Operator
    case object IN extends Operator
    case object INSTANCEOF extends Operator
    case object !== extends Operator
  }

  object JSNary {
    case object NewCall extends Operator
    case object MethodCall extends Operator
  }

  // JS-specific expressions.

  type Bool = BooleanLit
  val Bool = BooleanLit
  type Num = DoubleLit
  val Num = DoubleLit

  case class XML(v: String) extends Lit
  case class Regex(v: String, opts: String) extends Lit
  case class Prim(name: String) extends Lit

  case class Delete(e: Exp) extends Exp
  case class Typeof(e: Exp) extends Exp
  case class Void(e: Exp) extends Exp
  case class NewCall(f: Exp, args: List[Exp]) extends Exp        // MISSING
  case class ForIn(label: Option[Name], init: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class ForEach(label: Option[Name], init: Exp, test: Exp, modify: Exp, body: Exp) extends Exp // MISSING
  case class Yield(e: Option[Exp]) extends Exp  // MISSING
  case class Case(test: Option[Exp], body: Exp) extends Exp // MISSING
  case class Switch(e: Exp, cases: List[Exp]) extends Exp // MISSING
  case class With(exp: Exp, body: Exp) extends Exp  // MISSING
}
