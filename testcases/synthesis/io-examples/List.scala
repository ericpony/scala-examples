import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Foo {

  def listOp1(l: collection.List[Int], i: Int) = {
    //Cons(i, (l-i))
    //Cons[Int](i, l).slice(0, i)
    ???[collection.List[Int]]
  } ensuring { (res: collection.List[Int]) =>
    ((l, i), res) passes {
      case (Nil(), 2) => collection.Cons(2, collection.Nil[Int]())
      case (Cons(1, Nil()), 2) => collection.Cons(2, collection.Cons(1, collection.Nil()))
      case (Cons(1, Cons(2, Cons(3, Nil()))), 3) => collection.Cons(3, collection.Cons(1, collection.Cons(2, collection.Nil())))
    }
  }

}
