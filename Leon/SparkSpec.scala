import leon.annotation._
import leon.collection._
import leon.lang._

object SparkSpec extends App {

  @library
  def additiveFoldLeft (z: BigInt, list: List[BigInt]): BigInt = {
    list match {
      case Nil()      => z
      case Cons(h, t) => additiveFoldLeft(z + h, t)
    }
  }

  @library
  def additiveFoldLeft_loop (z: BigInt, list: List[BigInt], pos: BigInt): BigInt = {
    require(list != Nil[BigInt]())
    //require(list.size > 0)
    //require(pos < list.size && pos >= 0)
    var ret = z
    var l = list.tail
    val e1 = list.head
    var e2 = list.head
    var ptr = BigInt(0)
    while (l != Nil[BigInt]()) {
      val Cons(h, t) = l
      if (ptr == pos) {
        ret = ret + e1
        e2 = h
      } else
        ret = ret + h
      ptr = ptr + 1
      l = t
    }
    e2 + ret
  }

  @library
  def foldLeft[A, B] (z: B, f: (B, A) => B, list: List[A]): B =
    list match {
      case Nil()      => z
      case Cons(h, t) => foldLeft(f(z, h), f, t)
    }

  @library
  def aggregate[A, B] (list: List[A], zero: B, seq: (B, A) => B, comb: (B, B) => B): B = {
    foldLeft(zero, seq, list)
  }

  @library
  def reduce[B] (list: List[B], op: (B, B) => B): B = {
    require(list != Nil[B]())
    val Cons(head, tail) = list
    foldLeft(head, op, list)
  }

  @induct
  def isAssociasive[B] (list: List[B], op: (B, B) => B): Boolean = {
    require(list != Nil[B]())
    val Cons(first, t1) = list
    if (t1 == Nil[B]()) true
    else {
      val Cons(second, t2) = t1
      if (t2 == Nil[B]()) true
      else {
        val Cons(third, _) = t2
        op(op(first, second), third) == op(first, op(second, third)) && isAssociasive(t1, op)
      }
    }
  }

  @induct
  def isCommutative[B] (list: List[B], op: (B, B) => B): Boolean = {
    require(list != Nil[B]())
    val Cons(first, t1) = list
    if (t1 == Nil[B]()) true
    else {
      val Cons(second, _) = t1
      op(first, second) == op(second, first) && isCommutative(t1, op)
    }
  }

  def reduce_lemma[B] (list: List[B], list2: List[B], op: (B, B) => B): Boolean = {
    require(list != Nil[B]() && list2 != Nil[B]())
    require(list.content == list2.content)
    require(isAssociasive(list, op) && isCommutative(list, op))
    require(isAssociasive(list2, op) && isCommutative(list2, op))
    reduce(list, op) == reduce(list2, op)
  }.holds

  def additive_reduce_lemma (list: List[BigInt], list2: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]() && list2 != Nil[BigInt]())
    require(list.content == list2.content)
    def op (a: BigInt, b: BigInt) = a + b
    reduce(list, op) == reduce(list2, op)
  }.holds

  def additive_reduce_lemma_2 (list: List[BigInt], shift: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    //reduce(list, op) == reduce(list.rotate(shift), op)
    //list.foldLeft(BigInt(0))(op) == list2.foldLeft(BigInt(0))(op)
    foldLeft(BigInt(0), op, list) == foldLeft(BigInt(0), op, list.rotate(shift))
  }.holds

  def finite_additive_reduce_lemma (list: List[BigInt], shift: BigInt): Boolean = {
    require(list.size == 3)
    require(0 < shift && shift < 3)
    def op (a: BigInt, b: BigInt) = a + b
    //reduce(list, op) == reduce(list.rotate(shift), op)
    //list.foldLeft(BigInt(0))(op) == list2.foldLeft(BigInt(0))(op)
    foldLeft(BigInt(0), op, list) == foldLeft(BigInt(0), op, list.rotate(shift))
  }.holds

  def finite_additive_reduce_lemma_2 (list: List[BigInt], shift: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    //reduce(list, op) == reduce(list.rotate(shift), op)
    //list.foldLeft(BigInt(0))(op) == list2.foldLeft(BigInt(0))(op)
    foldLeft(BigInt(0), op, list) == foldLeft(BigInt(0), op, list.rotate(1))
  }.holds

  def finite_additive_reduce_lemma_3 (list: List[BigInt], shift: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    additiveFoldLeft_loop(0, list, 0) == additiveFoldLeft_loop(0, list, shift)
  }.holds
}