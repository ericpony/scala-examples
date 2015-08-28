import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._
import ScalaCombinators._

object ScalaCombinators {
  @library
  def foldl[A, B] (list: List[A], zero: B, op: (B, A) => B): B =
    list match {
      case Nil()      => zero
      case Cons(h, t) => foldl(t, op(zero, h), op)
    }

  @library
  def reducel[B] (list: List[B], op: (B, B) => B): B = {
    require(list != Nil[B]())
    foldl(list.tail, list.head, op)
  }

  @library
  def aggregate[A, B] (list: List[A], zero: B, seq: (B, A) => B, comb: (B, B) => B): B = {
    foldl(list, zero, seq)
  }
}

object ScalaCombinatorSpec extends App {
  /**
   * Check that the result of the combinator is not changed by list rotation.
   */
  def rotate_lemma[B] (list: List[B], op: (B, B) => B, combinator: (List[B], (B, B) => B) => B): Boolean = {
    if (list == Nil[B]()) true
    else {
      list.tail match {
        case Nil() => true
        case _     =>
          val t = combinator(list.tail, op)
          op(t, list.head) == op(list.head, t)
        // timeouts for op(t, list.head) == reducel(list, op)
      }
    }
  }

  /**
   * Check that the result of the combinator w.r.t. op is not changed
   * by swapping the first two elements in the list.
   */
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
   * Check that a combinator is deterministic w.r.t. op modulo permutation.
   * Note that {(1 2), (1 2 ... n)} generates S_n.
   */
  def determinism_lemma[B] (list: List[B], op: (B, B) => B, combinator: (List[B], (B, B) => B) => B): Boolean =
    rotate_lemma(list, op, combinator) && swap_lemma(list, op, combinator)

  /**
   * Check that a reducel operation is deterministic modulo permutation.
   */
  def reducel_lemma[B] (list: List[B], op: (B, B) => B): Boolean = {
    require(list != Nil[B]())
    def combinator = (list: List[B], op: (B, B) => B) => reducel[B](list, op)
    determinism_lemma(list, op, combinator)
  }

  /**
   * Check that a foldl operation is deterministic modulo permutation.
   */
  def foldl_lemma[B] (list: List[B], op: (B, B) => B, zero: B): Boolean = {
    require(list != Nil[B]())
    def combinator = (list: List[B], op: (B, B) => B) => foldl[B, B](list, zero, op)
    determinism_lemma(list, op, combinator)
  }

  def reducel_add_lemma (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    def op (a: BigInt, b: BigInt) = a + b
    def combinator = reducel[BigInt] _
    determinism_lemma(list, op, combinator)
    //reducel_lemma(list, op)
  }.holds /* verified by Leon */

  def reducel_union_lemma[B] (list: List[Set[B]]): Boolean = {
    require(list != Nil[Set[B]]())
    def op (a: Set[B], b: Set[B]) = a ++ b
    def combinator = reducel[Set[B]] _
    determinism_lemma(list, op, combinator)
    //determinism_lemma(list, op, reducel[Set[B]] _)
    //reducel_lemma(list, op)
  }.holds /* verified by Leon */

  @ignore
  def reducel_append_lemma[B] (list: List[List[B]]): Boolean = {
    require(list != Nil[List[B]]())
    def op (a: List[B], b: List[B]) = a ++ b
    def combinator = reducel[List[B]] _
    determinism_lemma(list, op, combinator)
    //reducel_lemma[List[B]](list, op)
  }.holds /* Leon finds a counterexample */

  def foldl_add_lemma (list: List[BigInt], zero: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    def op (a: BigInt, b: BigInt) = a + b
    def combinator (list: List[BigInt], op: (BigInt, BigInt) => BigInt) = foldl[BigInt, BigInt](list, zero, op)
    determinism_lemma(list, op, combinator)
    //foldl_lemma(list, op, zero)
  }.holds /* verified by Leon */
}