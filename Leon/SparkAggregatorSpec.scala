import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._

object SparkAggregatorSpec extends App {

  @library
  def foldl[A, B] (zero: B, op: (B, A) => B, list: List[A]): B =
    list match {
      case Nil()      => zero
      case Cons(h, t) => foldl(op(zero, h), op, t)
    }

  @library
  def reducel[B] (list: List[B], op: (B, B) => B): B = {
    require(list != Nil[B]())
    foldl(list.head, op, list.tail)
  }

  @library
  def foldl_v2[B] (zero: B, op: (B, B) => B, list: List[B]): B = {
    if (list.size == 0) zero
    else op(zero, list.tail match {
      case Nil() => list.head
      case _     => op(list.head, reducel_v2(list.tail, op))
    })
  }

  @library
  def reducel_v2[B] (list: List[B], op: (B, B) => B): B = {
    require(list != Nil[B]())
    list.tail match {
      case Nil() => list.head
      case _     => op(list.head, reducel_v2(list.tail, op))
    }
  }

  @library
  def map[A, B] (list: List[A], op: A => B): List[B] =
    list match {
      case Nil()      => Nil[B]()
      case Cons(h, t) => op(h) :: map(t, op)
    }

  @library
  def fold[B] (zero: B, op: (B, B) => B, list: List[List[B]]): B =
    list match {
      case Nil()      => zero
      case Cons(h, t) =>
        val tmpL = map[List[B], B](list, foldl(zero, op, _))
        foldl(zero, op, tmpL)
    }

  @library
  def reduce[B] (list: List[List[B]], op: (B, B) => B): B = {
    require(list != Nil[List[B]]())
    val tmpL = map[List[B], B](list, reducel(_, op))
    reducel(tmpL, op)
  }

  /**
   * relation between foldl and reducel
   */
  def foldl_to_reducel_lemma[B] (zero: B, op: (B, B) => B, list: List[B]): Boolean = {
    if (list.size == 0) trivial
    else foldl(zero, op, list) == op(zero, reducel(list, op))
  }

  def foldl_to_reducel_lemma_int (list: List[BigInt]): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    foldl_to_reducel_lemma(BigInt(0), op, list)
  }.holds /* verified */

  /**
   * List in foldl can be decomposed into list.head and list.tail.
   */
  def foldl_head_lemma[B] (zero: B, op: (B, B) => B, list: List[B]): Boolean = {
    if (list.size <= 1) trivial
    else foldl_v2(zero, op, list) == op(op(zero, list.head), reducel_v2(list.tail, op))
  }

  def foldl_head_lemma_int (list: List[BigInt]): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    foldl_head_lemma(BigInt(0), op, list)
  }.holds /* verified */

  /**
   * List in foldl can be decomposed into two sub-lists.
   */
  def foldl_concat_lemma[B] (zero: B, op: (B, B) => B, list1: List[B], list2: List[B]): Boolean = {
    if (list1 == Nil[B]()) trivial
    else foldl_v2(zero, op, list1 ++ list2) == op(foldl_v2(zero, op, list1), reducel_v2(list2, op)) because {
      list1.tail match {
        case Nil() => foldl_head_lemma(zero, op, list1.head :: list2) &&
          op(zero, list1.head) == foldl_v2(zero, op, list1)
        case _     => foldl_concat_lemma(zero, op, list1.tail, list2)
      }
    }
  }

  def foldl_concat_lemma_int_1 (list1: List[BigInt], list2: List[BigInt]): Boolean = {
    if (list1 == Nil[BigInt]() || list2 == Nil[BigInt]()) trivial
    else {
      def op (a: BigInt, b: BigInt) = a + b
      val zero = BigInt(0)
      val Cons(h2, t2) = list2
      t2 match {
        case Nil() => true
        case _     =>
          op(foldl_v2(zero, op, list1), reducel_v2(h2 :: t2, op)) ==
            op(foldl_v2(zero, op, list1 :+ h2), reducel_v2(t2, op))
      }
    }
  }.holds /* timeout */

  def foldl_concat_lemma_int (list1: List[BigInt], list2: List[BigInt]): Boolean = {
    if (list1 == Nil[BigInt]() || list2 == Nil[BigInt]()) trivial
    else {
      def op (a: BigInt, b: BigInt) = a + b
      val zero = BigInt(0)
      foldl_v2(zero, op, list1 ++ list2) == op(foldl_v2(zero, op, list1), reducel_v2(list2, op)) because {
        op(zero, list1.head) == foldl_v2(zero, op, List(list1.head)) &&
          check {
            list1.tail match {
              case Nil() => foldl_head_lemma_int(list1.head :: list2)
              case _     => check {
                foldl_concat_lemma_int(list1.tail, list2)
              }
            }
          }
      }
    }
  }.holds /* timeout */
}