import leon.annotation.induct
import leon.collection._
import leon.lang._
import leon.proof._

import scala.language.postfixOps


object SortedListOps {

  /**
   * Insert an element into a sorted list.
   */
  def insert (list: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(list))
    list match {
      case Nil()       => Cons(v, Nil())
      case Cons(x, xs) => if (x >= v) Cons(v, list) else Cons(x, insert(xs, v))
    }
  } ensuring (res => res.content == list.content ++ Set[BigInt](v) &&
    res.size == list.size + 1 &&
    isSorted(res)) /* verified by Leon */

  /**
   * Merge two sorted lists to obtain one sorted list.
   */
  def mergeSortedList (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    l2 match {
      case Nil()       => l1
      case Cons(x, xs) => insert(mergeSortedList(l1, xs), x)
    }
  } ensuring (res => res.content == l1.content ++ l2.content) /* verified by Leon */

  /**
   * Merge two lists to obtain one sorted list.
   */
  def merge (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    sort(l1 ++ l2)
  } ensuring (res => res.content == l1.content ++ l2.content && isSorted(res))

  /**
   * Tell whether a list is sorted or not.
   */
  def isSorted (list: List[BigInt]): Boolean = {
    list match {
      case Nil()                  => true
      case Cons(_, Nil())         => true
      case Cons(x1, Cons(x2, xs)) => x1 <= x2 && isSorted(list.tail)
    }
  } ensuring (res => !isSorted(list) || res)

  /**
   * Obtain a sorted version of the given list.
   */
  def sort (list: List[BigInt]): List[BigInt] = {
    list match {
      case Nil()       => list
      case Cons(x, xs) => insert(sort(xs), x)
    }
  } ensuring (res => res.content == list.content && isSorted(res)) /* verified by Leon */

  /**
   * Check that the result of sort is indeed sorted.
   */
  def isSorted_lemma (list: List[BigInt]): Boolean = {
    isSorted(sort(list))
  } holds /* trivial due to the post-condition of sort */

  def min (x: BigInt, y: BigInt) = if (x < y) x else y

  /**
   * Obtain the minimal element of the list.
   */
  def min (list: List[BigInt]): BigInt = {
    require(list != Nil[BigInt]())
    list match {
      case Cons(x, xs) =>
        if (xs == Nil[BigInt]()) x
        else min(x, min(xs))
    }
    /* Note: ensuring list.forall(res <= _) will timeout */
  } ensuring (res => (list contains res)) /* verified by Leon */

  /**
   * Check that min(list) is the minimal element of list.
   */
  def min_lemma (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    val m = min(list)
    list.contains(m) &&
      list.forall(m <= _) because min_lemma2(list, m)
  } holds /* verified by Leon */

  @induct
  def min_lemma2 (list: List[BigInt], m: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    m > min(list) || list.forall(m <= _)
  } holds /* verified by Leon */

  /**
   * Check that the first element of a sorted list
   * is the minimal element of the list.
   */
  @induct
  def min_head_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    sort(list).head == min(list)
  } holds /* verified by Leon */

  /**
   * Check that min(l1 ++ l2) == min(l2 ++ l1).
   */
  def min_concat_lemma (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l2 == Nil[BigInt]() ||
      l1 == Nil[BigInt]() || {
      min(l1 ++ l2) == min(l2 ++ l1) because {
        min(l1 ++ l2) == min(min(l1), min(l2)) && min_concat_lemma2(l1, l2) &&
          min(l2 ++ l1) == min(min(l2), min(l1)) && min_concat_lemma2(l2, l1) &&
          min(min(l1), min(l2)) == min(min(l2), min(l1))
      }
    }
  } holds /* verified by Leon */

  @induct
  def min_concat_lemma2 (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l2 == Nil[BigInt]() ||
      l1 == Nil[BigInt]() || {
      min(l1 ++ l2) == min(min(l1), min(l2))
    }
  } holds /* verified by Leon */

  /**
   * Check that sorting is idempotent.
   */
  @induct
  def sort_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    sort(list) == sort(sort(list))
  } holds /* verified by Leon */

  def delete (list: List[BigInt], v: BigInt): List[BigInt] = {
    if (list == Nil[BigInt]()) list
    else if (list.head == v) list.tail
    else Cons(list.head, delete(list.tail, v))
  } ensuring { res =>
    res.size == (if (list contains v) list.size - 1 else list.size)
  } /* verified by Leon */

  @induct
  def sort_detele_lemma (list: List[BigInt]): Boolean = {
    list == Nil[BigInt]() || {
      val l = sort(list)
      sort(delete(list, l.head)) == l.tail
    }
  } holds /* verified by Leon */

  def merge_lemma (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      val L1 = sort(l1 ++ l2)
      val L2 = sort(l2 ++ l1)
      L1.head == L2.head because {
        check {
          L1.head == min(l1 ++ l2) && min_head_lemma(l1 ++ l2)
        } && check {
          L2.head == min(l2 ++ l1) && min_head_lemma(l2 ++ l1)
        } && check {
          min_concat_lemma(l1, l2) && min_concat_lemma(l2, l1)
        }
      }
    }
  } holds

}
