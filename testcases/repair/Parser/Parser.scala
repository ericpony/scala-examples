import leon._
import leon.lang._
import leon.collection._

object Parser {
  abstract class Token
  case object LParen extends Token
  case object RParen extends Token
  case class Id(id : Int) extends Token
  
  abstract class Tree
  case class App(args : _root_.collection.List[Tree]) extends Tree
  case class Leaf(id : Int) extends Tree

  def parse(in : _root_.collection.List[Token]) : (Option[Tree], _root_.collection.List[Token]) = { in match {
    case Cons(Id(s), tl) => 
      (Some[Tree](Leaf(s)),tl)
    case Cons(LParen, tl) => parseMany(tl) match {
      case (Some(trees:_root_.collection.Cons[Tree]), Cons(RParen,rest)) =>
        (Some[Tree](App(trees)), rest)
      case (_, rest) => (None[Tree](), rest)
    }
    case _ => (None[Tree](), in)
  }} ensuring { _ match {
    case ( Some(tree), rest@Cons(h,_)) => 
      print(tree, rest) == in
//    case ( None(), Cons(h,_)) => !h.isInstanceOf[Id]
//    case ( None(), Nil) => 
    case _ => true
  }}

  def parseMany(in : _root_.collection.List[Token]) : (Option[_root_.collection.List[Tree]], _root_.collection.List[Token]) = { parse(in) match {
    case (None(), rest) if rest == in => (Some[_root_.collection.List[Tree]](_root_.collection.Nil()), in)
    case (None(), rest) => (None[_root_.collection.List[Tree]](), rest)
    case (Some(tree), rest) => parseMany(rest) match {
      case ( None(), rest2) => (None[_root_.collection.List[Tree]](), rest2)
      case ( Some(trees), rest2) =>
        ( Some[_root_.collection.List[Tree]](tree::trees), rest2 )
    }
  }} ensuring { _ match {
    case ( Some(t), rest@Cons(h, _) ) => 
      h == RParen && printL(t, rest) == in 
    case ( None(), Cons(h, _)) => 
      h == RParen
    case _ => true
  }}


  def printL(args : _root_.collection.List[Tree], rest : _root_.collection.List[Token]) : _root_.collection.List[Token] = args match {
    case Nil() => rest
    case Cons(h,t) => print(h, printL(t, rest))
  }
  
  def print(t : Tree, rest : _root_.collection.List[Token]) : _root_.collection.List[Token] = t match {
    case Leaf(s) => Id(s) :: rest
    case App(args) => LParen :: printL(args, RParen :: rest) 
  }

}
