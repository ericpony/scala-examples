import scala.collection.mutable.Set

class Wild {
  def contents[_] = List(1, 2, 3, 4)
}

val iter = (new Wild).contents.iterator
val set = Set.empty[???] // what type goes here?
while (iter.hasNext) {
  set += iter.next()
}

/*
To work around this kind of problem, here are two tricks you should consider:

1. When passing an existential type into a method, move type parameters
from the forSome clause to type parameters of the method. Inside the
body of the method, you can use the type parameters to refer to the
types that were in the forSome clause.

2. Instead of returning an existential type from a method, return an object
that has abstract type members for each of the types in the forSome clause.
*/

// Using these two tricks together, the previous code can be written as follows:

def getSet[T] (iter: Iterator[T]): Set[T] = {
  val ret = Set.empty[T] // T is captured here
  while (iter.hasNext) {
    ret += iter.next()
  }
  ret
}

val s = getSet((new Wild).contents.iterator)

// We can extract concrete type from an existential type using abstract type member

abstract class Type {type t}

def getType[T] (iter: Iterator[T]): Type = new Type {type t = T}

val t = getType((new Wild).contents.iterator)

