package sc.js.machine

class Globals[M <: Machine](val machine: M) {
  import machine._
  import terms._
  import stores._
  import envs._

  lazy val ρ0: Env = globalEnv._1
  lazy val σ0: Store = globalEnv._2
  lazy val globalEnv = makeEnv(ρempty, σempty, globalValues, globalObjects)

  lazy val ρMin: Env = minEnv._1
  lazy val σMin: Store = minEnv._2
  lazy val minEnv = makeEnv(ρempty, σempty, minValues, minObjects)

  def makeEnv(ρ0: Env, σ0: Store, globalValues: Map[Name, Value], globalObjects: Map[Name, Map[Name, Value]]): (Env, Store) = {
    val functionPrototypeAddress = FreshHeapLoc()

    val (ρ1, σ1) = globalValues.foldLeft((ρ0, σ0)) {
      case ((ρ, σ), (name, value @ Prim(_))) =>
        val loc = FreshStackLoc()
        val primLoc = FreshHeapLoc()

        val ρ1 = ρ + (name -> loc)
        val σ1 = σ.assign(loc, primLoc)

        val ρ2 = ρ1
        val σ2 = σ1.assign(primLoc, value)

        (ρ2, σ2)
      case ((ρ, σ), (name, value)) =>
        val loc = FreshStackLoc()

        val ρ1 = ρ + (name -> loc)
        val σ1 = σ.assign(loc, value)

        (ρ1, σ1)
    }

    val (ρ2, σ2) = globalObjects.foldLeft((ρ1, σ1)) {
      case ((ρ, σ), (k0, propMap0)) =>
        val localLoc = FreshStackLoc()
        val blobLoc = FreshHeapLoc()
        val propMap = propMap0.toList
        val props = propMap map {
          case (x, v) => (x, FreshHeapLoc())
        }

        val ρ1 = ρ
        val σ1 = (props zip propMap).foldLeft(σ) {
          case (σ, ((k, propLoc: Loc), (x, v @ Prim("Function.prototype")))) =>
            val vloc = functionPrototypeAddress
            σ.assign(propLoc, vloc).assign(vloc, v)
          case (σ, ((k, propLoc: Loc), (x, v))) =>
            val vloc = FreshHeapLoc()
            σ.assign(propLoc, vloc).assign(vloc, v)
        }

        val blob = JSBlob("function", functionPrototypeAddress, None, props)
        val ρ2 = ρ1 + (k0 -> localLoc)
        val σ2 = σ1.assign(localLoc, blobLoc).assign(blobLoc, blob, ρempty)

        (ρ2, σ2)
    }

    (ρ2, σ2)
  }

  lazy val minValues = Map(
    "undefined" -> Undefined()
  )

  lazy val minObjects = Map(
    "Array" -> Map("prototype" -> Prim("Array.prototype")),
    "Function" -> Map("prototype" -> Prim("Function.prototype")),
    "Object" -> Map("prototype" -> Prim("Object.prototype"))
  )

  // Prims are the functions implemented by the partial evaluator.
  // This does not include all the built-in objects, which just get
  // reified.
  lazy val globalValues = minValues ++ Map(
    "eval" -> Prim("eval"),
    "isFinite" -> Prim("isFinite"),
    "isNaN" -> Prim("isNaN"),
    "parseFloat" -> Prim("parseFloat"),
    "parseInt" -> Prim("parseInt"),
    "Infinity" -> Num(Double.PositiveInfinity),
    "NaN" -> Num(Double.NaN)
  )

  lazy val globalObjects = minObjects ++ mathObject

  lazy val mathObject = Map(
    "Math" -> Map("min" -> Prim("Math.min"),
                    "max" -> Prim("Math.max"),
                    "sin" -> Prim("Math.sin"),
                    "cos" -> Prim("Math.cos"),
                    "tan" -> Prim("Math.tan"),
                    "sqrt" -> Prim("Math.sqrt"),
                    "abs" -> Prim("Math.abs"),
                    "trunc" -> Prim("Math.trunc"),
                    "floor" -> Prim("Math.floor"),
                    "ceil" -> Prim("Math.ceil"),
                    "round" -> Prim("Math.round"),
                    "exp" -> Prim("Math.exp"),
                    "log" -> Prim("Math.log"),
                    "asin" -> Prim("Math.asin"),
                    "acos" -> Prim("Math.acos"),
                    "atan" -> Prim("Math.atan"),
                    "atan2" -> Prim("Math.atan2"),
                    "pow" -> Prim("Math.pow"),
                    "E" -> Prim("Math.E"),
                    "PI" -> Prim("Math.PI"),
                    "LN2" -> Prim("Math.LN2"),
                    "LN10" -> Prim("Math.LN10"),
                    "LOG10E" -> Prim("Math.LOG10E"),
                    "LOG2E" -> Prim("Math.LOG2E"),
                    "SQRT2" -> Prim("Math.SQRT2"),
                    "SQRT1_2" -> Prim("Math.SQRT1_2")
                    )
                  )
}
