package scsc.js.sc

import scala.collection.mutable.ListBuffer

class Rollback[M <: Machine](m: M) extends scsc.imp.sc.Rollback[M](m)
