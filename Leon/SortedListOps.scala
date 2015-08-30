import leon.annotation.{ignore, induct}
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
  @induct
  def mergeSortedList (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    l2 match {
      case Nil()       => l1
      case Cons(x, xs) => insert(mergeSortedList(l1, xs), x)
    }
  } ensuring {
    res =>  isSorted(res) && res.content == l1.content ++ l2.content
  } /* verified by Leon */

  /**
   * Merge two lists to obtain one sorted list.
   */
  def merge (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    sort(l1 ++ l2)
  } ensuring (res => res.content == l1.content ++ l2.content && isSorted(res))

  def merge_commutative_prop (l1: List[BigInt], l2: List[BigInt]) = {
    require(distinct(l1 ++ l2))
    merge(l1, l2) == merge(l2, l1) because merge_lemma(l1, l2)
  } holds

  def distinct (list: List[BigInt]): Boolean = {
    if (list == List[BigInt]()) true
    else !list.tail.contains(list.head) && distinct(list.tail)
  }

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
  } ensuring (res => res.content == list.content &&
    isSorted(res) &&
    res.size == list.size) /* verified by Leon */

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
   * Check that min(list) is indeed the minimal element of list.
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
   * Check that the sort(list).head == min(list),
   * given that list is nonempty.
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
  @ignore
  def sort_lemma (list: List[BigInt]) = {
    //require(list != Nil[BigInt]())
    sort(list) == sort(sort(list))
  } holds /* timeout */

  def delete (list: List[BigInt], v: BigInt): List[BigInt] = {
    if (list == Nil[BigInt]()) list
    else if (list.head == v) list.tail
    else Cons(list.head, delete(list.tail, v))
  } ensuring { res =>
    res.size == (if (list contains v) list.size - 1 else list.size) &&
      res.content.subsetOf(list.content)
  } /* verified by Leon */

  def sort_delete_lemma3 (list: List[BigInt], m: BigInt): Boolean = {
    sort(delete(list, m)) == delete(sort(list), m) because {
      true
      //      list match {
      //        case Nil()      => true
      //        case Cons(h, t) =>
      //          if(h == m) true
      //          else sort_delete_lemma3(t, m)
      //      }
    }
  } holds

  @induct
  def sort_delete_lemma2 (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      val m = sort(l1 ++ l2).head
      val L1t = if (l1 contains m) delete(l1, m) else l1
      val L2t = if (l1 contains m) l2 else delete(l2, m)
      sort(L1t ++ L2t) == sort(l1 ++ l2).tail because {
        check {
          sort(delete(l1 ++ l2, m)) == sort(l1 ++ l2).tail && sort_delete_lemma2(l1 ++ l2)
        } && check {
          delete(l1 ++ l2, m) == L1t ++ L2t
        }
      }
    }
  } holds /* verified by Leon */

  def sort_delete_lemma (l1: List[BigInt], l2: List[BigInt], L: List[BigInt], L2: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L2 == sort(l1 ++ l2)) {
        val m = L2.head
        if (L == sort(delete(l1 ++ l2, m))) {
          L == L2.tail because {
            sort(delete(l1 ++ l2, m)) == L2.tail &&
              sort_delete_lemma2(l1 ++ l2)
          }
        } else true
      } else true
    }
  } holds

  /* verified by Leon */
  @induct
  def sort_delete_lemma2 (list: List[BigInt]): Boolean = {
    list == Nil[BigInt]() || {
      val l = sort(list)
      sort(delete(list, l.head)) == l.tail
    }
  } holds /* verified by leon */

  @induct
  def delete_contain_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(!list.contains(m))
    delete(list, m) == list
  } holds /* verified by leon */

  @induct
  def delete_concat_lemma1 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(!l1.contains(m))
    l1 ++ delete(l2, m) == delete(l1 ++ l2, m)
  } holds /* verified by leon */

  def delete_concat_lemma2 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(!l2.contains(m))
    delete(l1, m) ++ l2 == delete(l1 ++ l2, m) because {
      l1 match {
        case Nil()      => delete_contain_lemma(l2, m)
        case Cons(h, t) => delete_concat_lemma2(t, l2, m)
      }
    }
  } holds /* verified by leon */

  /**
   * Check that sort(l1 ++ l2).head == sort(l2 ++ l1).head,
   * given that l1 ++ l2 is nonempty.
   */
  def merge_lemma1 (l1: List[BigInt], l2: List[BigInt], L1: List[BigInt], L2: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L1 == sort(l1 ++ l2) && L2 == sort(l2 ++ l1)) {
        L1.head == L2.head because {
          check {
            L1.head == min(l1 ++ l2) && min_head_lemma(l1 ++ l2)
          } && check {
            L2.head == min(l2 ++ l1) && min_head_lemma(l2 ++ l1)
          } && check {
            min_concat_lemma(l1, l2) && min_concat_lemma(l2, l1)
          }
        }
      } else true
    }
  } holds /* verified by Leon */

  def merge_lemma3 (l1: List[BigInt], l2: List[BigInt]) = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      !(l1.head == l2.head && l1.tail == l2.tail) || l1 == l2
    }
  } holds


  /**
   * Check that the merge operation is commutative.
   */
  def merge_lemma (l1: List[BigInt], l2: List[BigInt]) = {
    require(distinct(l1 ++ l2))
    merge_lemma2(l1, l2, sort(l1 ++ l2), sort(l2 ++ l1))
  } holds

  def sort_tail_lemma1 (l1: List[BigInt], l2: List[BigInt], L: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L == sort(l1 ++ l2) && !(l2.contains(L.head))) {
        L.tail == sort(delete(l1, L.head) ++ l2) because
          check {
            L.tail == delete(sort(l1 ++ l2), L.head)
          } && check {
            delete(sort(l1 ++ l2), L.head) == sort(delete(l1 ++ l2, L.head)) because
              sort_delete_lemma3(l1 ++ l2, L.head)
          } && check {
            L.tail == sort(delete(l1 ++ l2, L.head))
          } && check {
            delete(l1 ++ l2, L.head) == delete(l1, L.head) ++ l2 because
              delete_concat_lemma2(l1, l2, L.head)
          }
      } else true
    }
  } holds /* verified by leon */

  def sort_tail_lemma2 (l1: List[BigInt], l2: List[BigInt], L: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L == sort(l2 ++ l1) && !(l2.contains(L.head))) {
        L.tail == sort(l2 ++ delete(l1, L.head)) because
          check {
            L.tail == delete(sort(l2 ++ l1), L.head)
          } && check {
            delete(sort(l2 ++ l1), L.head) == sort(delete(l2 ++ l1, L.head)) because
              sort_delete_lemma3(l2 ++ l1, L.head)
          } && check {
            L.tail == sort(delete(l2 ++ l1, L.head))
          } && check {
            l2 ++ delete(l1, L.head) == delete(l2 ++ l1, L.head) because
              delete_concat_lemma1(l2, l1, L.head)
          }
      } else true
    }
  } holds /* verified by leon */

  def sort_tail_lemma3 (l1: List[BigInt], l2: List[BigInt], L: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L == sort(l1 ++ l2) && !(l1.contains(L.head))) {
        L.tail == sort(l1 ++ delete(l2, L.head)) because
          check {
            L.tail == delete(sort(l1 ++ l2), L.head)
          } && check {
            delete(sort(l1 ++ l2), L.head) == sort(delete(l1 ++ l2, L.head)) because
              sort_delete_lemma3(l1 ++ l2, L.head)
          } && check {
            L.tail == sort(delete(l1 ++ l2, L.head))
          } && check {
            l1 ++ delete(l2, L.head) == delete(l1 ++ l2, L.head) because
              delete_concat_lemma1(l1, l2, L.head)
          }
      } else true
    }
  } holds /* verified by leon */

  def sort_tail_lemma4 (l1: List[BigInt], l2: List[BigInt], L: List[BigInt]): Boolean = {
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L == sort(l2 ++ l1) && !(l1.contains(L.head))) {
        L.tail == sort(delete(l2, L.head) ++ l1) because
          check {
            L.tail == delete(sort(l2 ++ l1), L.head)
          } && check {
            delete(sort(l2 ++ l1), L.head) == sort(delete(l2 ++ l1, L.head)) because
              sort_delete_lemma3(l2 ++ l1, L.head)
          } && check {
            L.tail == sort(delete(l2 ++ l1, L.head))
          } && check {
            delete(l2, L.head) ++ l1 == delete(l2 ++ l1, L.head) because
              delete_concat_lemma2(l2, l1, L.head)
          }
      } else true
    }
  } holds /* verified by leon */

  @induct
  def distinct_lemma (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2) && l2.contains(m))
    !l1.contains(m)
  } holds

  @induct
  def distinct_delete_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(distinct(list))
    distinct(delete(list, m))
  } holds

  @induct
  def distinct_delete_lemma1 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(delete(l1, m) ++ l2) because {
      distinct(l1) && distinct_delete_lemma(l1, m)
    }
  } holds

  @induct
  def distinct_delete_lemma2 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1 ++ delete(l2, m)) because {
      distinct(l1) && distinct_delete_lemma(l2, m)
    }
  } holds

  /**
   * Check that sort(l1 ++ l2) == sort(l2 ++ l1).
   */
  def merge_lemma2 (l1: List[BigInt], l2: List[BigInt], L1: List[BigInt], L2: List[BigInt]): Boolean = {
    require(distinct(l1 ++ l2))
    l1 == Nil[BigInt]() ||
      l2 == Nil[BigInt]() || {
      if (L1 == sort(l1 ++ l2) && L2 == sort(l2 ++ l1)) {
        L1 == L2 because {
          if (l2.contains(L1.head) == false) {
            val l11 = delete(l1, L1.head)
            check {
              L1.head == L2.head because merge_lemma1(l1, l2, L1, L2)
            } && check {
              L1.tail == L2.tail because {
                check { L1.tail == sort(l11 ++ l2) because sort_tail_lemma1(l1, l2, L1) } &&
                  check { L2.tail == sort(l2 ++ l11) because sort_tail_lemma2(l1, l2, L2) } &&
                  check { distinct(l11 ++ l2) because distinct_delete_lemma1(l1, l2, L1.head) } &&
                  check { merge_lemma2(l11, l2, L1.tail, L2.tail) }
              }
            }
          } else {
            val l22 = delete(l2, L1.head)
            check {
              L1.head == L2.head because merge_lemma1(l1, l2, L1, L2)
            } && check {
              L1.tail == L2.tail because {
                check { !l1.contains(L1.head) because distinct_lemma(l1, l2, L1.head) } &&
                  check { L1.tail == sort(l1 ++ l22) because sort_tail_lemma3(l1, l2, L1) } &&
                  check { L2.tail == sort(l22 ++ l1) because sort_tail_lemma4(l1, l2, L2) } &&
                  check { distinct(l1 ++ l22) because distinct_delete_lemma2(l1, l2, L1.head) } &&
                  check { merge_lemma2(l1, l22, L1.tail, L2.tail) }
              }
            }
          }
        }
      } else true
    }
  } holds /* verified by Leon */

  @ignore
  def merge_lemma4 (l1: List[BigInt], l2: List[BigInt]) = {
    require(l1.content == l2.content && l1.size == l2.size)
    sort(l1) == sort(l2)
  } holds /* timeout */
}
