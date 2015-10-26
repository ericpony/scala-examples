/**
 * Ad-Hoc Polymorphism Ad-Hoc polymorphism is a way to add behavior to an
 * existing class without modifying it In Haskell, polymorphism is achieved
 * using typeclasses:
 * abs :: (Num a, Ord a) => a -> a
 * abs x = if x < 0 then -x else x
 *
 * In Scala, we can achieve Ad-Hoc polymorphism using implicits.
 * Scala library defines many Typeclasses to achieve Ad-Hoc polymorphism,
 * such as Integral, Numeric, Ordering ...
 */
def abs[T] (x: T)(implicit num: Numeric[T]): T =
  if (num.lt(x, num.zero)) num.negate(x) else x

def max[T: Ordering] (x: T, y: T): T = implicitly[Ordering[T]].max(x, y)

/**
 * We can define our own instances of existing typeclasses.
 */

case class Student (name: String, score: Float)

implicit object StudentOrdering extends Ordering[Student] {
  def compare (x: Student, y: Student) = x.score.compareTo(y.score)
}

max(Student("Bob", 95), Student("Alice", 90))