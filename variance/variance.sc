/**
 * Container types are usually co-variant. Handler types are usually contra-variant.
 * Function types are usually contra-variant on parameter types and co-variant parameters
 * on return types.
 */

/**
 * Type Variance and Bounds Implementation of a Writer
 */

class B {
  override def toString = "Ifm B"
}

class A extends B {
  override def toString = "Ifm A"
}

// A writer for type T should be able to handle
// any subtype of T. Hence, it is defined to be
// contra-variant.
trait Writer[-T] {
  def write (t: T): String
}

// bWriter is a subtype of Writer[A],
// because Writer[A] is contra-variant.
val bWriter = new Writer[B] {
  def write (b: B): String = b.toString
}

def writeWith[T] (t: T)(w: Writer[T]) = w.write(t)

writeWith(new B)(bWriter)

// bWriter as a Writer[A]
writeWith(new A)(bWriter)

/**
 * Type Variance and Bounds Implementation of a List
 */

case class Cons[T] (head: T, tail: List[T]) extends List[T]

case object Nil extends List[Nothing]

// co-variant
trait List[+T] {
  def ::[U >: T] (u: U): List[U] = Cons[U](u, this)
}

val l1 = new A :: Nil // List[A]
val l2 = new B :: l1 // List[B]
val l3 = new A :: l2 // List[B]

def printL[T] (l: List[T]): Unit = {
  l match {
    case Nil        =>
    case Cons(h, t) => print(h); print(" "); printL(t);
  }
}
printL(l1)
printL(l2)