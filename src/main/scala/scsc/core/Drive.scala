package scsc.core

import scala.collection.mutable.ListBuffer

trait Drive[St, VarDef] {
  type Memo = List[(St, VarDef)]
  def drive(above: List[St], memo: Memo, whistle: Boolean)(initialState: St): (St, Memo)
}
