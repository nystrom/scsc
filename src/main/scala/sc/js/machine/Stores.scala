package sc.js.machine

trait Stores extends sc.imp.machine.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }

  import machine._
  import machine.terms._

  case class JSBlob(typeof: String, proto: HeapLoc, lambda: Option[Lambda], props: List[(Name, HeapLoc)]) extends Blob

  override def scan(blob: Blob) = blob match {
    case JSBlob(typeof, proto, lambda, props) => proto :: props.sortBy(_._1).map(_._2)
    case _ => super.scan(blob)
  }

}
