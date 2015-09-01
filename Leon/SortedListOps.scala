import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import SortedListOps._
import SortedListLemmas._
import scala.language.postfixOps

object SortedListSpec {

  /* Insert operations are commutative. */
  @induct
  def insert_commutative_prop (list: List[BigInt], e1: BigInt, e2: BigInt) = {
    require(isSorted(list) && distinct(e1 :: e2 :: list))
    insert(insert(list, e1), e2) == insert(insert(list, e2), e1)
  } holds /* verified by Leon */

  /* Merge operations are commutative. */
  def merge_commutative_prop (l1: List[BigInt], l2: List[BigInt]) = {
    require(distinct(l1 ++ l2))
    merge(l1, l2) == merge(l2, l1) because merge_commu_lemma(l1, l2)
  } holds /* verified by Leon */

  @induct
  def merge_associative_prop (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) = {
    require(distinct(l1 ++ l2 ++ l3) && l1 ++ l2 ++ l3 != Nil[BigInt]())
    val L1 = merge(merge(l1, l2), l3)
    val L2 = merge(l1, merge(l2, l3))
    L1.head == L2.head because merge_assoc_lemma(l1, l2, l3)
  } holds

  /* Sort operations are idempotent. */
  def sort_idempotent_prop (list: List[BigInt]) = {
    sort(list) == sort(sort(list)) because sort_idem_lemma(list)
  } holds /* verified by Leon */

  /* This is the ultimate result we want, but Leon cannot prove it directly. */
  @ignore
  def sort_equivalence_prop (l1: List[BigInt], l2: List[BigInt]) = {
    require(l1.content == l2.content && l1.size == l2.size)
    sort(l1) == sort(l2)
  } holds /* timeout */
}

object SortedListOps {
  /**
   * Insert an element into a sorted list.
   * @param list a sorted list
   * @param e an element
   * @return a sorted list containning e
   */
  def insert (list: List[BigInt], e: BigInt): List[BigInt] = {
    require(isSorted(list))
    list match {
      case Nil()       => Cons(e, Nil())
      case Cons(x, xs) => if (x >= e) Cons(e, list) else Cons(x, insert(xs, e))
    }
  } ensuring (res => res.content == list.content ++ Set[BigInt](e) &&
    res.size == list.size + 1 &&
    isSorted(res)) /* verified by Leon */

  /**
   * Merge two sorted lists to obtain one sorted list.
   * @param l1 a sorted list
   * @param l2 a sorted list
   * @return a sorted list
   */
  @induct
  def mergeSortedList (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    l2 match {
      case Nil()       => l1
      case Cons(x, xs) => insert(mergeSortedList(l1, xs), x)
    }
  } ensuring {
    res => isSorted(res) && res.content == l1.content ++ l2.content
  } /* verified by Leon */

  /**
   * Merge two lists to obtain one sorted list.
   * @param l1 a list
   * @param l2 a list
   * @return a sorted list
   */
  def merge (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    sort(l1 ++ l2)
  } ensuring {
    res => res.content == l1.content ++ l2.content && isSorted(res)
  }

  /**
   * Tell whether a list contains no duplicate elements.
   * @param list a list
   * @return whether list contains no duplicate elements
   */
  def distinct (list: List[BigInt]): Boolean = {
    if (list == List[BigInt]()) trivial
    else !list.tail.contains(list.head) && distinct(list.tail)
  }

  /**
   * Obtain a sorted version of the provided list (in ascending order).
   * @param list a list
   * @return a sorted list
   */
  def sort (list: List[BigInt]): List[BigInt] = {
    list match {
      case Nil()       => list
      case Cons(x, xs) => insert(sort(xs), x)
    }
  } ensuring {
    res => res.content == list.content && isSorted(res)
  } /* verified by Leon */

  /**
   * Tell whether a list is sorted in ascending order.
   * @param list a list
   * @return whether the provided list is sorted in ascending order
   */
  def isSorted (list: List[BigInt]): Boolean = {
    list match {
      case Nil()                  => trivial
      case Cons(_, Nil())         => trivial
      case Cons(x1, Cons(x2, xs)) => x1 <= x2 && isSorted(list.tail)
    }
  } ensuring {
    res => list.size == 0 || !res || list.head == min(list)
  }

  /**
   * Obtain the minimal element of the input list.
   * @param list a list
   * @return the minimal element of the provided list
   */
  def min (list: List[BigInt]): BigInt = {
    require(list != Nil[BigInt]())
    list match {
      case Cons(x, xs) =>
        if (xs == Nil[BigInt]()) x
        else min(x, min(xs))
    }
  } ensuring {
    res => (list contains res) &&
      list.forall(res <= _) because min_lemma(list, res)
  } /* verified by Leon */

  def min (x: BigInt, y: BigInt) = if (x < y) x else y
}

object SortedListLemmas {

  @induct
  def min_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    m > min(list) || list.forall(m <= _)
  } holds /* verified by Leon */

  /**
   * Check that min(list) is indeed the minimal element of list.
   */
  def min_lemma2 (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    val m = min(list)
    list.contains(m) && list.forall(m <= _) because min_lemma(list, m)
  } holds /* verified by Leon */

  /**
   * Check that the sort(list).head == min(list).
   */
  @induct
  def min_head_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    sort(list).head == min(list)
  } holds /* verified by Leon */

  @induct
  def min_sort_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    min(sort(list)) == min(list)
  } holds

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

  /**
   * Check that min(l1 ++ l2) == min(min(l1), min(l2)).
   */
  @induct
  def min_concat_lemma2 (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l2 == Nil[BigInt]() ||
      l1 == Nil[BigInt]() ||
      min(l1 ++ l2) == min(min(l1), min(l2))
  } holds /* verified by Leon */

  def delete (list: List[BigInt], e: BigInt): List[BigInt] = {
    if (list == Nil[BigInt]()) list
    else if (list.head == e) list.tail
    else Cons(list.head, delete(list.tail, e))
  } ensuring { res =>
    res.size == (if (list contains e) list.size - 1 else list.size) &&
      res.content.subsetOf(list.content)
  } /* verified by Leon */

  @induct
  def sort_delete_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(list != Nil[BigInt]() && m == sort(list).head)
    sort(delete(list, m)) == delete(sort(list), m)
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
   * Check that sort(l1 ++ l2).head == sort(l2 ++ l1).head, given that l1 ++ l2 is nonempty.
   */
  def merge_lemma1 (l1: List[BigInt], l2: List[BigInt], L1: List[BigInt], L2: List[BigInt]): Boolean = {
    if (l1 == Nil[BigInt]() || l2 == Nil[BigInt]()) trivial
    else {
      if (L1 == sort(l1 ++ l2) && L2 == sort(l2 ++ l1)) {
        L1.head == L2.head because {
          check { L1.head == min(l1 ++ l2) because min_head_lemma(l1 ++ l2) } &&
            check { L2.head == min(l2 ++ l1) because min_head_lemma(l2 ++ l1) } &&
            check { min_concat_lemma(l1, l2) because min_concat_lemma(l2, l1) }
        }
      } else true
    }
  } holds /* verified by Leon */

  /**
   * Check that the merge operation is commutative.
   */
  def merge_commu_lemma (l1: List[BigInt], l2: List[BigInt]) = {
    require(distinct(l1 ++ l2))
    sort(l1 ++ l2) == sort(l2 ++ l1) because merge_lemma2(l1, l2, sort(l1 ++ l2), sort(l2 ++ l1))
  } holds /* verified by Leon */

  @induct
  def sort_tail_lemma (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    sort(list).tail == sort(delete(list, sort(list).head))
  } holds /* verified by Leon */

  def sort_tail_lemma1 (l1: List[BigInt], l2: List[BigInt], L: List[BigInt]): Boolean = {
    require(l1 != Nil[BigInt]())
    if (l2 == Nil[BigInt]()) sort_tail_lemma(l1)
    else {
      if (L == sort(l1 ++ l2) && !(l2.contains(L.head))) {
        L.tail == sort(delete(l1, L.head) ++ l2) because
          check {
            L.tail == delete(sort(l1 ++ l2), L.head)
          } && check {
            delete(sort(l1 ++ l2), L.head) == sort(delete(l1 ++ l2, L.head)) because
              sort_delete_lemma(l1 ++ l2, L.head)
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
    require(l1 != Nil[BigInt]())
    if (l2 == Nil[BigInt]()) sort_tail_lemma(l1)
    else {
      if (L == sort(l2 ++ l1) && !(l2.contains(L.head))) {
        L.tail == sort(l2 ++ delete(l1, L.head)) because
          check {
            L.tail == delete(sort(l2 ++ l1), L.head)
          } && check {
            delete(sort(l2 ++ l1), L.head) == sort(delete(l2 ++ l1, L.head)) because
              sort_delete_lemma(l2 ++ l1, L.head)
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
    require(l2 != Nil[BigInt]())
    if (l1 == Nil[BigInt]()) sort_tail_lemma(l2)
    else {
      if (L == sort(l1 ++ l2) && !(l1.contains(L.head))) {
        L.tail == sort(l1 ++ delete(l2, L.head)) because
          check {
            L.tail == delete(sort(l1 ++ l2), L.head)
          } && check {
            delete(sort(l1 ++ l2), L.head) == sort(delete(l1 ++ l2, L.head)) because
              sort_delete_lemma(l1 ++ l2, L.head)
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
    require(l2 != Nil[BigInt]())
    if (l1 == Nil[BigInt]()) sort_tail_lemma(l2)
    else {
      if (L == sort(l2 ++ l1) && !(l1.contains(L.head))) {
        L.tail == sort(delete(l2, L.head) ++ l1) because
          check { L.tail == delete(sort(l2 ++ l1), L.head) } &&
            check {
              delete(sort(l2 ++ l1), L.head) == sort(delete(l2 ++ l1, L.head)) because
                sort_delete_lemma(l2 ++ l1, L.head)
            } &&
            check { L.tail == sort(delete(l2 ++ l1, L.head)) } &&
            check {
              delete(l2, L.head) ++ l1 == delete(l2 ++ l1, L.head) because
                delete_concat_lemma2(l2, l1, L.head)
            }
      } else true
    }
  } holds /* verified by leon */

  @induct
  def distinct_sublist_lemma (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1) && distinct(l2)
  } holds /* verified by Leon */

  @induct
  def distinct_excl_lemma (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2) && l2.contains(m))
    !l1.contains(m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma1 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(delete(l1, m) ++ l2) because distinct_delete_lemma3(l1, m)

  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma2 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1 ++ delete(l2, m)) because distinct_delete_lemma3(l2, m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma3 (list: List[BigInt], m: BigInt): Boolean = {
    !distinct(list) || distinct(delete(list, m))
  } holds /* verified by Leon */

  /**
   * Check that sort(l1 ++ l2) == sort(l2 ++ l1).
   */
  def merge_lemma2 (l1: List[BigInt], l2: List[BigInt], L1: List[BigInt], L2: List[BigInt]): Boolean = {
    require(distinct(l1 ++ l2))
    if (l1 == Nil[BigInt]() || l2 == Nil[BigInt]()) trivial
    else {
      if (L1 == sort(l1 ++ l2) && L2 == sort(l2 ++ l1)) {
        L1 == L2 because {
          check {
            L1.head == L2.head because merge_lemma1(l1, l2, L1, L2)
          } && {
            if (l2.contains(L1.head) == false) {
              val l11 = delete(l1, L1.head)
              L1.tail == L2.tail because {
                check { L1.tail == sort(l11 ++ l2) because sort_tail_lemma1(l1, l2, L1) } &&
                  check { L2.tail == sort(l2 ++ l11) because sort_tail_lemma2(l1, l2, L2) } &&
                  check { distinct(l11 ++ l2) because distinct_delete_lemma1(l1, l2, L1.head) } &&
                  check { merge_lemma2(l11, l2, L1.tail, L2.tail) }
              }
            } else {
              val l22 = delete(l2, L1.head)
              L1.tail == L2.tail because {
                check { !l1.contains(L1.head) because distinct_excl_lemma(l1, l2, L1.head) } &&
                  check { L1.tail == sort(l1 ++ l22) because sort_tail_lemma3(l1, l2, L1) } &&
                  check { L2.tail == sort(l22 ++ l1) because sort_tail_lemma4(l1, l2, L2) } &&
                  check { distinct(l1 ++ l22) because distinct_delete_lemma2(l1, l2, L1.head) } &&
                  check { merge_lemma2(l1, l22, L1.tail, L2.tail) }
              }
            }
          }
        } // end of showing L1 == L2
      } else true
    }
  } holds /* verified by Leon */

  //  @induct
  //  def merge_assoc_lemma (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) = {
  //    require(distinct(l1 ++ l2 ++ l3))
  //    if (l1 == Nil[BigInt]()) sort_idem_lemma(l2)
  //    else if (l2 == Nil[BigInt]()) sort_idem_lemma(l3) && sort_idem_lemma(l1)
  //    else if (l3 == Nil[BigInt]()) sort_idem_lemma(l2)
  //    else {
  //      val L1 = merge(merge(l1, l2), l3)
  //      val L2 = merge(l1, merge(l2, l3))
  //      L1.head == L2.head because merge_assoc_lemma2(l1, l2, l3)
  //    }
  //  } holds

  @induct
  def merge_assoc_lemma (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) = {
    require(distinct(l1 ++ l2 ++ l3) && l1 ++ l2 ++ l3 != Nil[BigInt]())
    if (l1 == Nil[BigInt]()) sort_idem_lemma(l2)
    else if (l2 == Nil[BigInt]()) sort_idem_lemma(l3) && sort_idem_lemma(l1)
    else if (l3 == Nil[BigInt]()) sort_idem_lemma(l2)
    else {
      val L1 = merge(merge(l1, l2), l3)
      val L2 = merge(l1, merge(l2, l3))
      L1 == L2 because {
        check {
          L1.head == L2.head because merge_assoc_lemma2(l1, l2, l3)
        }
      }
    } // end of proving L1 == L2
  } holds /* proof in progress */

  @induct
  def merge_assoc_lemma2 (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) = {
    require(distinct(l1 ++ l2 ++ l3) && l1 ++ l2 ++ l3 != Nil[BigInt]())
    if (l1 == Nil[BigInt]()) sort_idem_lemma(l2)
    else if (l2 == Nil[BigInt]()) sort_idem_lemma(l3) && sort_idem_lemma(l1)
    else if (l3 == Nil[BigInt]()) sort_idem_lemma(l2)
    else {
      val L1 = merge(merge(l1, l2), l3)
      val L2 = merge(l1, merge(l2, l3))
      L1.head == L2.head because {
        check { min(L1) == L1.head && min(L2) == L2.head && isSorted(L1) && isSorted(L2) } &&
          check {
            min(L1) == min(L2) because {
              check { min(sort(l1 ++ l2)) == min(l1 ++ l2) because min_sort_lemma(l1 ++ l2) } &&
                check { min(sort(l2 ++ l3)) == min(l2 ++ l3) because min_sort_lemma(l2 ++ l3) } &&
                check { min(L1) == min(sort(l1 ++ l2) ++ l3) because min_sort_lemma(sort(l1 ++ l2) ++ l3) } &&
                check { min(L2) == min(l1 ++ sort(l2 ++ l3)) because min_sort_lemma(l1 ++ sort(l2 ++ l3)) } &&
                check { min(L2) == min(min(l1), min(sort(l2 ++ l3))) because min_concat_lemma2(l1, l2 ++ l3) } &&
                check { min(L2) == min(min(l1), min(l2 ++ l3)) } &&
                check { min(L2) == min(l1 ++ l2 ++ l3) } &&
                check {
                  min(L1) == min(min(sort(l1 ++ l2)), min(l3)) because {
                    check { min(min(sort(l1 ++ l2)), min(l3)) == min(min(l1 ++ l2), min(l3)) } &&
                      check { min(L1) == min(sort(l1 ++ l2) ++ l3) } &&
                      check {
                        min(sort(l1 ++ l2) ++ l3) == min(min(sort(l1 ++ l2)), min(l3)) because
                          min_concat_lemma2(sort(l1 ++ l2), l3)
                      } &&
                      check { min(min(sort(l1 ++ l2)), min(l3)) == min(min(l1 ++ l2), min(l3)) }
                  } &&
                    check { min(L1) == min(min(l1 ++ l2), min(l3)) }
                } &&
                check { min(L1) == min(l1 ++ l2 ++ l3) because min_concat_lemma2(l1 ++ l2, l3) }
            }
          }
      }
    }
  } holds

  //  @induct
  //  def merge_assoc_lemma2 (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) = {
  //    require(distinct(l1 ++ l2 ++ l3))
  //    val L1 = merge(merge(l1, l2), l3)
  //    val L2 = merge(l1, merge(l2, l3))
  //    L1 == L2 because {
  //      check {
  //        distinct(sort(l1 ++ l2)) && distinct(l3) because distinct_sublist_lemma(sort(l1 ++ l2), l3)
  //      } &&
  //        check {
  //          sort(sort(l1 ++ l2) ++ l3) == sort(l3 ++ sort(l1 ++ l2)) because merge_commu_lemma(sort(l1 ++ l2), l3)
  //        } && check {
  //        sort(l3 ++ sort(l1 ++ l2)) == sort(l3 ++ l1 ++ l2) because sort_idem_lemma(l1 ++ l2)
  //      }
  //    }
  //  } holds

  def sort_idem_lemma (list: List[BigInt]): Boolean = {
    if (list == Nil[BigInt]()) trivial
    else {
      sort(list) == sort(sort(list)) because {
        check {
          sort(list).head == sort(sort(list)).head because {
            check { sort(list).head == min(list) because min_head_lemma(list) } &&
              check { sort(sort(list)).head == min(sort(list)) because min_head_lemma(sort(list)) } &&
              check { min(sort(list)) == min(list) because min_sort_lemma(list) }
          }
        } && check {
          val m = sort(list).head
          sort(list).tail == sort(sort(list)).tail because {
            check { sort(list).tail == sort(delete(list, m)) because sort_tail_lemma(list) } &&
              check { sort(sort(list)).tail == sort(delete(sort(list), m)) } &&
              check { delete(sort(list), m) == sort(delete(list, m)) because sort_delete_lemma(list, m) } &&
              check { sort(sort(delete(list, m))) == sort(delete(list, m)) because sort_idem_lemma(delete(list, m)) }
          }
        }
      }
    }
  } holds /* verified by Leon */
}
