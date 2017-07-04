package scsc.jssc

object Context {
  import Machine._
  import scsc.js.Trees._

  val ρempty: Env = Map()
  val σempty: Store = Map()

  lazy val ρ0: Env = globalEnv._1
  lazy val σ0: Store = globalEnv._2

  lazy val globalEnv: (Env, Store) = defs.foldLeft((ρempty, σempty)) {
    case ((ρ, σ), ("", propMap0)) =>
      val ρ1 = ρ
      val σ2 = σ

      val propMap = propMap0.toList
      val locs = propMap map { _ => FreshLoc() }
      val ρ2 = (propMap zip locs).foldLeft(ρ1) {
        case (ρ, ((x, v), loc)) =>
          ρ + (x -> loc)
      }
      val σ3 = (propMap zip locs).foldLeft(σ2) {
        case (σ, ((x, v), loc)) =>
          σ.assign(loc, v, ρempty)
      }

      (ρ2, σ3)

    case ((ρ, σ), (k, propMap0)) =>
      val localLoc = FreshLoc()
      val objLoc = FreshLoc()
      val propMap = propMap0.toList
      val props = propMap map {
        case (x, v) =>
          val xloc = FreshLoc()
          Property(StringLit(x), xloc, None, None)
      }
      val σ1 = (props zip propMap).foldLeft(σ) {
        case (σ, (Property(k, vloc: Loc, None, None), (x, v))) =>
          σ.assign(vloc, v, ρempty)
      }
      val obj = FunObject("function", Prim("Function.prototype"), Nil, None, props)

      val ρ1 = ρ + (k -> localLoc)
      val σ2 = σ1.assign(localLoc, objLoc, ρempty).assign(objLoc, obj, ρempty)

      (ρ1, σ2)
  }

  // Prims are the functions implemented by the partial evaluator.
  // This does not include all the built-in objects, which just get
  // reified.
  lazy val defs = Map(
    "" -> Map("eval" -> Prim("eval"),
                    "isFinite" -> Prim("isFinite"),
                    "isNaN" -> Prim("isNaN"),
                    "parseFloat" -> Prim("parseFloat"),
                    "parseInt" -> Prim("parseInt"),
                    "Infinity" -> Num(Double.PositiveInfinity),
                    "NaN" -> Num(Double.NaN)
                  ),
    "String" -> Map("indexOf" -> Prim("String.indexOf"),
                    "charAt" -> Prim("String.charAt")
    ),
    "Math" -> Map("min" -> Prim("Math.min"),
                    "max" -> Prim("Math.max"),
                    "sin" -> Prim("Math.sin"),
                    "cos" -> Prim("Math.cos"),
                    "tan" -> Prim("Math.tan"),
                    "sqrt" -> Prim("Math.sqrt"),
                    "abs" -> Prim("Math.abs"),
                    "floor" -> Prim("Math.floor"),
                    "ceil" -> Prim("Math.ceil"),
                    "round" -> Prim("Math.round"),
                    "exp" -> Prim("Math.exp"),
                    "log" -> Prim("Math.log"),
                    "asin" -> Prim("Math.asin"),
                    "acos" -> Prim("Math.acos"),
                    "atan" -> Prim("Math.atan"),
                    "atan2" -> Prim("Math.atan2"),
                    "pow" -> Prim("Math.pow")
                    )
  )
}
