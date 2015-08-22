import leon.annotation._
import leon.collection._
import leon.lang._

object ScalaAggrSpec extends App {

  @library
  def foldLeft[A, B] (list: List[A], z: B, f: (B, A) => B): B =
    list match {
      case Nil()      => z
      case Cons(h, t) => foldLeft(t, f(z, h), f)
    }

  @library
  def aggregate[A, B] (list: List[A], zero: B, seq: (B, A) => B, comb: (B, B) => B): B = {
    foldLeft(list, zero, seq)
  }

  @library
  def reduce[B] (list: List[B], op: (B, B) => B): B = {
    require(list != Nil[B]())
    foldLeft(list.tail, list.head, op)
  }

  def checkAddition (a1: BigInt, a2: BigInt, a3: BigInt, a4: BigInt, a5: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5)
  }.holds

  def reduce_swap_lemma[B] (list: List[B], op: (B, B) => B): Boolean = {
    if (list == Nil[B]()) true
    else {
      val Cons(h, tail) = list.tail
      tail match {
        case Nil() => op(list.head, h) == op(h, list.head)
        case _     =>
          val t = reduce(tail, op)
          op(op(list.head, h), t) == op(op(h, list.head), t)
      }
    }
  }

  def rotate_lemma[B] (list: List[B], op: (B, B) => B, combinator: (List[B], (B, B) => B) => B): Boolean = {
    if (list == Nil[B]()) true
    else {
      list.tail match {
        case Nil() => true
        case _     =>
          val t = combinator(list.tail, op)
          op(t, list.head) == op(list.head, t)
        // timeouts for op(t, list.head) == reduce(list, op)
      }
    }
  }

  def swap_lemma[B] (list: List[B], op: (B, B) => B, combinator: (List[B], (B, B) => B) => B): Boolean = {
    if (list == Nil[B]()) true
    else {
      val Cons(h, tail) = list.tail
      tail match {
        case Nil() => op(list.head, h) == op(h, list.head)
        case _     =>
          val t = combinator(tail, op)
          op(op(list.head, h), t) == op(op(h, list.head), t)
      }
    }
  }

  /**
   * Note that {(1 2), (1 2 ... n)} generates S_n.
   */
  def determinism_lemma[B] (list: List[B], op: (B, B) => B, combinator: (List[B], (B, B) => B) => B): Boolean =
    rotate_lemma(list, op, combinator) && swap_lemma(list, op, combinator)

  def reduce_lemma[B] (list: List[B], op: (B, B) => B): Boolean = {
    require(list != Nil[B]())
    def combinator = (list: List[B], op: (B, B) => B) => reduce[B](list, op)
    determinism_lemma(list, op, combinator)
  }

  def foldl_lemma[B] (list: List[B], op: (B, B) => B, zero: B): Boolean = {
    require(list != Nil[B]())
    def combinator = (list: List[B], op: (B, B) => B) => foldLeft[B, B](list, zero, op)
    determinism_lemma(list, op, combinator)
  }

  def add_reduce_lemma (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    def op (a: BigInt, b: BigInt) = a + b
    def combinator = (list: List[BigInt], op: (BigInt, BigInt) => BigInt) => reduce(list, op)
    determinism_lemma(list, op, combinator)
    //reduce_lemma(list, op)
  }.holds

  def union_reduce_lemma (list: List[Set[BigInt]]): Boolean = {
    require(list != Nil[Set[BigInt]]())
    def op (a: Set[BigInt], b: Set[BigInt]) = a ++ b
    def combinator = (list: List[BigInt], op: (BigInt, BigInt) => BigInt) => reduce(list, op)
    determinism_lemma(list, op, combinator)
    //reduce_lemma(list, op)
  }.holds

  def append_reduce_lemma (list: List[List[BigInt]]): Boolean = {
    require(list != Nil[List[BigInt]]())
    def op (a: List[BigInt], b: List[BigInt]) = a ++ b
    def combinator = (list: List[BigInt], op: (BigInt, BigInt) => BigInt) => reduce(list, op)
    determinism_lemma(list, op, combinator)
    //reduce_lemma(list, op)
  }.holds

  def add_foldl_lemma (list: List[BigInt], zero: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    def op (a: BigInt, b: BigInt) = a + b
    def combinator = (list: List[BigInt], op: (BigInt, BigInt) => BigInt) => foldLeft[BigInt, BigInt](list, zero, op)
    determinism_lemma(list, op, combinator)
    //foldl_lemma(list, op, zero)
  }.holds
}