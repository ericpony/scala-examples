import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._

object ScalaAggregatorSpec extends App {

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

  /**
   * Check that set union is commutative and associative.
   */
  def checkSetUnion[B] (a1: Set[B], a2: Set[B], a3: Set[B], a4: Set[B], a5: Set[B]): Boolean = {
    def op (a: Set[B], b: Set[B]) = a ++ b
    op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5)
  }.holds // verified by Leon

  /**
   * Check that integer addition is commutative and associative.
   */
  def integer_add_prop (a1: BigInt, a2: BigInt, a3: BigInt, a4: BigInt, a5: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5)
  }.holds // verified by Leon

  /**
   * Check that 32-bit integer addition is commutative and associative.
   * (Note that Leon handles overflow by wrapping, e.g., 2^32 == -2^31.)
   */
  def int32_add_prop (a1: Int, a2: Int, a3: Int, a4: Int, a5: Int): Boolean = {
    def op (a: Int, b: Int) = a + b
    op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5)
  }.holds // verified by Leon

  /**
   * Check that 64-bit floating-point addition is commutative and associative.
   */
  @ignore
  def double_add_prop (a1: Double, a2: Double, a3: Double, a4: Double, a5: Double): Boolean = {
    def op (a: Double, b: Double) = a + b
    op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5)
  }.holds // failed due to unsupported type Double

  /**
   * Check that integer vector addition is commutative and associative.
   * (Note that Leon handles overflow by wrapping, e.g., 2^32 == -2^31.)
   */
  def int_vector_add_prop (a1: List[BigInt], a2: List[BigInt], a3: List[BigInt], a4: List[BigInt], a5: List[BigInt]): Boolean = {
    require(a1.size == a2.size && a2.size == a3.size && a3.size == a4.size && a4.size == a5.size)
    if (a1.size == 0) true
    else {
      def op (a: List[BigInt], b: List[BigInt]) = a.zip(b).map(t => t._1 + t._2)
      op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5) because {
        a1 match {
          case Nil() => trivial
          case _     => integer_add_prop(a1.head, a2.head, a3.head, a4.head, a5.head) &&
            int_vector_add_prop(a1.tail, a2.tail, a3.tail, a4.tail, a5.tail)
        }
      }
    }
  }.holds // verified by Leon

  /**
   * Check that point-wise union of set vectors is commutative and associative.
   */
  def set_vector_add_prop[B] (a1: List[Set[B]], a2: List[Set[B]], a3: List[Set[B]], a4: List[Set[B]], a5: List[Set[B]]): Boolean = {
    require(a1.size == a2.size && a2.size == a3.size && a3.size == a4.size && a4.size == a5.size)
    if (a1.size == 0) true
    else {
      def op (a: List[Set[B]], b: List[Set[B]]) = a.zip(b).map(t => t._1 ++ t._2)
      op(a1, a2) == op(a2, a1) && op(a3, op(a4, a5)) == op(op(a3, a4), a5) because {
        a1 match {
          case Nil() => trivial
          case _     => checkSetUnion(a1.head, a2.head, a3.head, a4.head, a5.head) &&
            set_vector_add_prop(a1.tail, a2.tail, a3.tail, a4.tail, a5.tail)
        }
      }
    }
  }.holds // failed due to Z3 runtime exception

  def int32_vector_add_lemma (a1: List[Int], a2: List[Int]): Boolean = {
    require(a1.size == a2.size)
    if (a1.size == 0) true
    else {
      def op (a: List[Int], b: List[Int]) = a.zip(b).map(t => t._1 + t._2)
      op(a1, a2) == (a1.head + a2.head) :: op(a1.tail, a2.tail) because {
        a1.tail match {
          case Nil() => trivial
          case _     => op(a1, a2).head == a1.head + a2.head && int32_vector_add_lemma(a1.tail, a2.tail)
        }
      }
    }
  }.holds // timeout

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
  }.holds // verified by Leon

  def reducel_union_lemma[B] (list: List[Set[B]]): Boolean = {
    require(list != Nil[Set[B]]())
    def op (a: Set[B], b: Set[B]) = a ++ b
    def combinator = reducel[Set[B]] _
    determinism_lemma(list, op, combinator)
    //determinism_lemma(list, op, reducel[Set[B]] _)
    //reducel_lemma(list, op)
  }.holds // verified by Leon

  @ignore
  def reducel_append_lemma[B] (list: List[List[B]]): Boolean = {
    require(list != Nil[List[B]]())
    def op (a: List[B], b: List[B]) = a ++ b
    def combinator = reducel[List[B]] _
    determinism_lemma(list, op, combinator)
    //reducel_lemma[List[B]](list, op)
  }.holds // Leon finds a counterexample

  def foldl_add_lemma (list: List[BigInt], zero: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    def op (a: BigInt, b: BigInt) = a + b
    def combinator (list: List[BigInt], op: (BigInt, BigInt) => BigInt) = foldl[BigInt, BigInt](list, zero, op)
    determinism_lemma(list, op, combinator)
    //foldl_lemma(list, op, zero)
  }.holds // verified by Leon
}