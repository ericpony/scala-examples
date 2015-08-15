import leon.lang._
import leon.annotation._

object ListSize {

  sealed abstract class List

  case class Cons (head: BigInt, tail: List) extends List

  case object Nil extends List

  def size (l: List): BigInt = (l match {
    case Nil        => BigInt(0)
    case Cons(_, t) => 1 + size(t)
  }) ensuring (_ >= 0)
}
