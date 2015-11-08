// Boo!
val f = (s: List[T]) => s.size

class G[T] extends (List[T] => Int) {
  def apply (s: List[T]) = s.size
}

val g = new G[Int]

println(g(List(1, 2, 3)))

println(f(List(1, 2, 3)))
