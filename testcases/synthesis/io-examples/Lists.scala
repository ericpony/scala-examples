import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Lists {

  def safetail(l: collection.List[Int]): collection.List[Int] = choose { (res : collection.List[Int]) =>
    (l, res) passes {
      case Cons(1, Cons(2, Cons(3, Cons(4, Nil())))) => collection.Cons(2, collection.Cons(3, collection.Cons(4, collection.Nil())))
      case Cons(2, Cons(3, Cons(4, Nil()))) => collection.Cons(3, collection.Cons(4, collection.Nil()))
      case Nil() => collection.Nil()
    }
  }

  def uniq(l: collection.List[Int]): collection.List[Int] = choose { (res : collection.List[Int]) =>
    (l, res) passes {
      case Cons(1, Cons(1, Cons(1, Cons(2, Nil())))) => collection.Cons(1, collection.Cons(2, collection.Nil()))
      case Cons(3, Cons(3, Cons(4, Nil()))) => collection.Cons(3, collection.Cons(4, collection.Nil()))
      case Nil() => collection.Nil()
    }
  }
}
