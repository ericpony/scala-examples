/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.collection._

object Monads3 {

  def append[T](l1: collection.List[T], l2: collection.List[T]): collection.List[T] = {
    l1 match {
      case Cons(head, tail) => collection.Cons(head, append(tail, l2))
      case Nil() => l2
    }
  } ensuring { res => (res == l1) || (l2 != collection.Nil[T]()) }

  def flatMap[T,U](list: collection.List[T], f: T => collection.List[U]): collection.List[U] = list match {
    case Cons(head, tail) => append(f(head), flatMap(tail, f))
    case Nil() => collection.Nil()
  }

  def associative_lemma[T,U,V](list: collection.List[T], f: T => collection.List[U], g: U => collection.List[V]): Boolean = {
    flatMap(flatMap(list, f), g) == flatMap(list, (x: T) => flatMap(f(x), g))
  }

  def associative_lemma_induct[T,U,V](list: collection.List[T], flist: collection.List[U], glist: collection.List[V], f: T => collection.List[U], g: U => collection.List[V]): Boolean = {
    associative_lemma(list, f, g) &&
    append(glist, flatMap(append(flist, flatMap(list, f)), g)) == append(append(glist, flatMap(flist, g)), flatMap(list, (x: T) => flatMap(f(x), g))) &&
    (glist match {
      case Cons(ghead, gtail) =>
        associative_lemma_induct(list, flist, gtail, f, g)
      case Nil() => flist match {
        case Cons(fhead, ftail) =>
          associative_lemma_induct(list, ftail, g(fhead), f, g)
        case Nil() => list match {
          case Cons(head, tail) => associative_lemma_induct(tail, f(head), collection.Nil(), f, g)
          case Nil() => true
        }
      }
    })
  }.holds

  def left_unit_law[T,U](x: T, f: T => collection.List[U]): Boolean = {
    flatMap(collection.Cons(x, collection.Nil()), f) == f(x)
  }.holds

  def right_unit_law[T](list: collection.List[T]): Boolean = {
    flatMap(list, (x: T) => collection.Cons(x, collection.Nil())) == list
  }
    
  def right_unit_induct[T,U](list: collection.List[T]): Boolean = {
    right_unit_law(list) && (list match {
      case Cons(head, tail) => right_unit_induct(tail)
      case Nil() => true
    })
  }.holds

  def flatMap_zero_law[T,U](f: T => collection.List[U]): Boolean = {
    flatMap(collection.Nil[T](), f) == collection.Nil[U]()
  }.holds

  def flatMap_to_zero_law[T](list: collection.List[T]): Boolean = {
    flatMap(list, (x: T) => collection.Nil[T]()) == collection.Nil[T]()
  }
    
  def flatMap_to_zero_induct[T,U](list: collection.List[T]): Boolean = {
    flatMap_to_zero_law(list) && (list match {
      case Cons(head, tail) => flatMap_to_zero_induct(tail)
      case Nil() => true
    })
  }.holds

  def add_zero_law[T](list: collection.List[T]): Boolean = {
    append(list, collection.Nil()) == list
  }.holds

  def zero_add_law[T](list: collection.List[T]): Boolean = {
    append(collection.Nil(), list) == list
  }.holds

}
