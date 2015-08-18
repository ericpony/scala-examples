import leon.lang._
import leon.collection._
import leon.annotation._
object Tree { 
  sealed abstract class Tree
  case object Empty extends Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree

  sealed abstract class Dir
  case object Left extends Dir
  case object Right extends Dir
  
  def lookup(t: Tree, path : collection.List[Dir]): Option[Tree] = {
    (t,path) match {
      case (_,Nil()) => Some[Tree](t)
      case (Empty,_) => None[Tree]()
      case (Node(left,_,_),  Cons(Left,rest)) => lookup(left,rest)
      case (Node(_,_,right), Cons(Right,rest)) => lookup(right,rest)
    }
  } 

  def cons[A](x: A, lst: collection.List[A]): collection.List[A] = collection.Cons[A](x,lst)

  def find(t: Tree, subtree: Tree): collection.List[collection.List[Dir]] = ({
    if (t==subtree) 
      collection.List(collection.Nil[Dir])
    else {
      t match {
        case Empty => collection.Nil[collection.List[Dir]]
        case Node(left,_,right) => {
          find(left,subtree).map(cons(Left,_)) ++ 
            find(right,subtree).map(cons(Right,_))
        }
      }
    }
  } : collection.List[collection.List[Dir]]).ensuring((res:collection.List[collection.List[Dir]]) => res.forall((path:collection.List[Dir]) => true))
}
