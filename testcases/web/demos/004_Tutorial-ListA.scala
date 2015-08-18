/* Copyright 2009-2015 EPFL, Lausanne */

import _root_.collection.ListOps
import leon._
import leon.lang._
import leon.annotation._
import leon.math._

sealed abstract class List[T] {

  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def content: Set[T] = this match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  def contains(v: T): Boolean = (this match {
    case Cons(h, t) if h == v => true
    case Cons(_, t) => t.contains(v)
    case Nil() => false
  }) ensuring { _ == (content contains v) }

  def ++(that: _root_.collection.List[T]): _root_.collection.List[T] = (this match {
    case Nil() => that
    case Cons(x, xs) => _root_.collection.Cons(x, xs ++ that)
  }) ensuring { res =>
    (res.content == this.content ++ that.content) &&
    (res.size == this.size + that.size) &&
    (that != _root_.collection.Nil[T]() || res == this)
  }

  def head: T = {
    require(this != _root_.collection.Nil[T]())
    val Cons(h, _) = this
    h
  }

  def tail: _root_.collection.List[T] = {
    require(this != _root_.collection.Nil[T]())
    val Cons(_, t) = this
    t
  }

  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    if (index == BigInt(0)) {
      head
    } else {
      tail(index-1)
    }
  }

  def ::(t:T): _root_.collection.List[T] = _root_.collection.Cons(t, this)

  def :+(t:T): _root_.collection.List[T] = {
    this match {
      case Nil() => _root_.collection.Cons(t, this)
      case Cons(x, xs) => _root_.collection.Cons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: _root_.collection.List[T] = {
    this match {
      case Nil() => this
      case Cons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): _root_.collection.List[T] = { (this, i) match {
    case (Nil(), _) => _root_.collection.Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        _root_.collection.Nil[T]()
      } else {
        _root_.collection.Cons(h, t.take(i-1))
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         BigInt(0)
      else if (i >= this.size) this.size
      else                     i
    ))
  }

  def drop(i: BigInt): _root_.collection.List[T] = { (this, i) match {
    case (Nil(), _) => _root_.collection.Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        _root_.collection.Cons[T](h, t)
      } else {
        t.drop(i-1)
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         this.size
      else if (i >= this.size) BigInt(0)
      else                     this.size - i
    ))
  }

  def slice(from: BigInt, to: BigInt): _root_.collection.List[T] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): _root_.collection.List[T] = { this match {
    case Nil() => _root_.collection.Nil[T]()
    case Cons(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        _root_.collection.Cons(to, r)
      } else {
        _root_.collection.Cons(h, r)
      }
  }} ensuring { (res: _root_.collection.List[T]) =>
    res.size == this.size &&
    res.content == (
      (this.content -- Set(from)) ++
      (if (this.content contains from) Set(to) else Set[T]())
    )
  }

  private def chunk0(s: BigInt, l: _root_.collection.List[T], acc: _root_.collection.List[T], res: _root_.collection.List[_root_.collection.List[T]], s0: BigInt): _root_.collection.List[_root_.collection.List[T]] = {
    require(s > 0 && s0 >= 0)
    l match {
      case Nil() =>
        if (acc.size > 0) {
          res :+ acc
        } else {
          res
        }
      case Cons(h, t) =>
        if (s0 == BigInt(0)) {
          chunk0(s, t, _root_.collection.Cons(h, _root_.collection.Nil()), res :+ acc, s-1)
        } else {
          chunk0(s, t, acc :+ h, res, s0-1)
        }
    }
  }

  def chunks(s: BigInt): _root_.collection.List[_root_.collection.List[T]] = {
    require(s > 0)

    chunk0(s, this, _root_.collection.Nil(), _root_.collection.Nil(), s)
  }

  def zip[B](that: _root_.collection.List[B]): _root_.collection.List[(T, B)] = { (this, that) match {
    case (Cons(h1, t1), Cons(h2, t2)) =>
      _root_.collection.Cons((h1, h2), t1.zip(t2))
    case _ =>
      _root_.collection.Nil[(T, B)]()
  }} ensuring { _.size == (
    if (this.size <= that.size) this.size else that.size
  )}

  def -(e: T): _root_.collection.List[T] = { this match {
    case Cons(h, t) =>
      if (e == h) {
        t - e
      } else {
        _root_.collection.Cons(h, t - e)
      }
    case Nil() =>
      _root_.collection.Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- Set(e)
  }

  def --(that: _root_.collection.List[T]): _root_.collection.List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        _root_.collection.Cons(h, t -- that)
      }
    case Nil() =>
      _root_.collection.Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- that.content
  }

  def &(that: _root_.collection.List[T]): _root_.collection.List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        _root_.collection.Cons(h, t & that)
      } else {
        t & that
      }
    case Nil() =>
      _root_.collection.Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == (this.content & that.content)
  }

  def padTo(s: BigInt, e: T): _root_.collection.List[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil(), s) =>
      _root_.collection.Cons(e, _root_.collection.Nil().padTo(s-1, e))
    case (Cons(h, t), s) =>
      _root_.collection.Cons(h, t.padTo(s-1, e))
  }} ensuring { res =>
    if (s <= this.size)
      res == this
    else
      res.size == s &&
      res.content == this.content ++ Set(e)
  }

  def find(e: T): Option[BigInt] = { this match {
    case Nil() => None[BigInt]()
    case Cons(h, t) =>
      if (h == e) {
        Some[BigInt](0)
      } else {
        t.find(e) match {
          case None()  => None[BigInt]()
          case Some(i) => Some(i+1)
        }
      }
    }} ensuring { res => !res.isDefined || (this.content contains e) }

  def init: _root_.collection.List[T] = {
    require(!isEmpty)
    ((this : @unchecked) match {
      case Cons(h, Nil()) =>
        _root_.collection.Nil[T]()
      case Cons(h, t) =>
        _root_.collection.Cons[T](h, t.init)
    })
  } ensuring ( (r: _root_.collection.List[T]) =>
    r.size == this.size - 1 &&
    r.content.subsetOf(this.content)
  )

  def last: T = {
    require(!isEmpty)
    (this : @unchecked) match {
      case Cons(h, Nil()) => h
      case Cons(_, t) => t.last
    }
  } ensuring { this.contains _ }

  def lastOption: Option[T] = { this match {
    case Cons(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def firstOption: Option[T] = { this match {
    case Cons(h, t) =>
      Some(h)
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def unique: _root_.collection.List[T] = this match {
    case Nil() => _root_.collection.Nil()
    case Cons(h, t) =>
      _root_.collection.Cons(h, t.unique - h)
  }

  def splitAt(e: T): _root_.collection.List[_root_.collection.List[T]] =  split(_root_.collection.Cons(e, _root_.collection.Nil()))

  def split(seps: _root_.collection.List[T]): _root_.collection.List[_root_.collection.List[T]] = this match {
    case Cons(h, t) =>
      if (seps.contains(h)) {
        _root_.collection.Cons(_root_.collection.Nil(), t.split(seps))
      } else {
        val r = t.split(seps)
        _root_.collection.Cons(_root_.collection.Cons(h, r.head), r.tail)
      }
    case Nil() =>
      _root_.collection.Cons(_root_.collection.Nil(), _root_.collection.Nil())
  }

  def evenSplit: (_root_.collection.List[T], _root_.collection.List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def updated(i: BigInt, y: T): _root_.collection.List[T] = {
    require(0 <= i && i < this.size)
    this match {
      case Cons(x, tail) if i == 0 =>
        _root_.collection.Cons[T](y, tail)
      case Cons(x, tail) =>
        _root_.collection.Cons[T](x, tail.updated(i - 1, y))
    }
  }

  private def insertAtImpl(pos: BigInt, l: _root_.collection.List[T]): _root_.collection.List[T] = {
    require(0 <= pos && pos <= size)
    if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case Cons(h, t) =>
          _root_.collection.Cons(h, t.insertAtImpl(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt(pos: BigInt, l: _root_.collection.List[T]): _root_.collection.List[T] = {
    require(-pos <= size && pos <= size)
    if(pos < 0) {
      insertAtImpl(size + pos, l)
    } else {
      insertAtImpl(pos, l)
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt(pos: BigInt, e: T): _root_.collection.List[T] = {
    require(-pos <= size && pos <= size)
    insertAt(pos, _root_.collection.Cons[T](e, _root_.collection.Nil()))
  } ensuring { res =>
    res.size == this.size + 1 &&
    res.content == this.content ++ Set(e)
  }

  private def replaceAtImpl(pos: BigInt, l: _root_.collection.List[T]): _root_.collection.List[T] = {
    require(0 <= pos && pos <= size)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons(h, t) =>
          _root_.collection.Cons(h, t.replaceAtImpl(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def replaceAt(pos: BigInt, l: _root_.collection.List[T]): _root_.collection.List[T] = {
    require(-pos <= size && pos <= size)
    if(pos < 0) {
      replaceAtImpl(size + pos, l)
    } else {
      replaceAtImpl(pos, l)
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def rotate(s: BigInt): _root_.collection.List[T] = {
    if (isEmpty) {
      _root_.collection.Nil[T]()
    } else {
      drop(s mod size) ++ take(s mod size)
    }
  } ensuring { res =>
    res.size == this.size
  }

  def isEmpty = this match { 
    case Nil() => true
    case _ => false 
  }

  // Higher-order API
  def map[R](f: T => R): _root_.collection.List[R] = { this match {
    case Nil() => _root_.collection.Nil[R]()
    case Cons(h, t) => f(h) :: t.map(f)
  }} ensuring { _.size == this.size }

  def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  def foldRight[R](z: R)(f: (T,R) => R): R = this match {
    case Nil() => z
    case Cons(h, t) => f(h, t.foldRight(z)(f))
  }
 
  def scanLeft[R](z: R)(f: (R,T) => R): _root_.collection.List[R] = { this match {
    case Nil() => z :: _root_.collection.Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def scanRight[R](z: R)(f: (T,R) => R): _root_.collection.List[R] = { this match {
    case Nil() => z :: _root_.collection.Nil[R]()
    case Cons(h, t) => 
      val rest@Cons(h1,_) = t.scanRight(z)(f)
      f(h, h1) :: rest
  }} ensuring { !_.isEmpty }

  def flatMap[R](f: T => _root_.collection.List[R]): _root_.collection.List[R] =
    ListOps.flatten(this map f)

  def filter(p: T => Boolean): _root_.collection.List[T] = { this match {
    case Nil() => _root_.collection.Nil[T]()
    case Cons(h, t) if p(h) => _root_.collection.Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def filterNot(p: T => Boolean): _root_.collection.List[T] =
    filter(!p(_)) ensuring { res =>
      res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(!p(_))
    }

  def partition(p: T => Boolean): (_root_.collection.List[T], _root_.collection.List[T]) = { this match {
    case Nil() => (_root_.collection.Nil[T](), _root_.collection.Nil[T]())
    case Cons(h, t) =>
      val (l1, l2) = t.partition(p)
      if (p(h)) (h :: l1, l2)
      else      (l1, h :: l2)
  }} ensuring { res =>
    res._1 == filter(p) &&
    res._2 == filterNot(p)
  }

  // In case we implement for-comprehensions
  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean): Boolean = this match {
    case Nil() => true
    case Cons(h, t) => p(h) && t.forall(p)
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  def find(p: T => Boolean): Option[T] = { this match {
    case Nil() => None[T]()
    case Cons(h, t) if p(h) => Some(h)
    case Cons(_, t) => t.find(p)
  }} ensuring { res => res match {
    case Some(r) => (content contains r) && p(r)
    case None() => true
  }}

  def groupBy[R](f: T => R): Map[R, _root_.collection.List[T]] = this match {
    case Nil() => Map.empty[R, _root_.collection.List[T]]
    case Cons(h, t) =>
      val key: R = f(h)
      val rest: Map[R, _root_.collection.List[T]] = t.groupBy(f)
      val prev: _root_.collection.List[T] = if (rest isDefinedAt key) rest(key) else _root_.collection.Nil[T]()
      (rest ++ Map((key, h :: prev))) : Map[R, _root_.collection.List[T]]
  }

  def takeWhile(p: T => Boolean): _root_.collection.List[T] = { this match {
    case Cons(h,t) if p(h) => _root_.collection.Cons(h, t.takeWhile(p))
    case _ => _root_.collection.Nil[T]()
  }} ensuring { res =>
    (res forall p) &&
    (res.size <= this.size) &&
    (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): _root_.collection.List[T] = { this match {
    case Cons(h,t) if p(h) => t.dropWhile(p)
    case _ => this
  }} ensuring { res =>
    (res.size <= this.size) &&
    (res.content subsetOf this.content) &&
    (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): BigInt = { this match {
    case Nil() => BigInt(0)
    case Cons(h, t) =>
      (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
  }} ensuring {
    _ == this.filter(p).size
  }

}

@ignore
object List {
  def apply[T](elems: T*): _root_.collection.List[T] = {
    var l: _root_.collection.List[T] = _root_.collection.Nil[T]()
    for (e <- elems) {
      l = _root_.collection.Cons(e, l)
    }
    l.reverse
  }
}

@library
object ListOps {
  def flatten[T](ls: _root_.collection.List[_root_.collection.List[T]]): _root_.collection.List[T] = ls match {
    case Cons(h, t) => h ++ flatten(t)
    case Nil() => _root_.collection.Nil()
  }

  def isSorted(ls: _root_.collection.List[BigInt]): Boolean = ls match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
    case Cons(_, t) => isSorted(t)
  }

  def sorted(ls: _root_.collection.List[BigInt]): _root_.collection.List[BigInt] = ls match {
    case Cons(h, t) => insSort(sorted(t), h)
    case Nil() => _root_.collection.Nil()
  }

  def insSort(ls: _root_.collection.List[BigInt], v: BigInt): _root_.collection.List[BigInt] = ls match {
    case Nil() => _root_.collection.Cons(v, _root_.collection.Nil())
    case Cons(h, t) =>
      if (v <= h) {
        _root_.collection.Cons(v, t)
      } else {
        _root_.collection.Cons(h, insSort(t, v))
      }
  }
}

case class Cons[T](h: T, t: _root_.collection.List[T]) extends _root_.collection.List[T]
case class Nil[T]() extends _root_.collection.List[T]

@library
object ListSpecs {
  def snocIndex[T](l : _root_.collection.List[T], t : T, i : BigInt) : Boolean = {
    require(0 <= i && i < l.size + 1)
    // proof:
    (l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }) &&
    // claim:
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  def reverseIndex[T](l : _root_.collection.List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
    (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def appendIndex[T](l1 : _root_.collection.List[T], l2 : _root_.collection.List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => if (i==BigInt(0)) true else appendIndex[T](xs,l2,i-1)
    }) &&
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)))
  }.holds

  def appendAssoc[T](l1 : _root_.collection.List[T], l2 : _root_.collection.List[T], l3 : _root_.collection.List[T]) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => appendAssoc(xs,l2,l3)
    }) &&
    (((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3)))
  }.holds

  def snocIsAppend[T](l : _root_.collection.List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) =>  snocIsAppend(xs,t)
    }) &&
    ((l :+ t) == l ++ _root_.collection.Cons[T](t, _root_.collection.Nil()))
  }.holds

  def snocAfterAppend[T](l1 : _root_.collection.List[T], l2 : _root_.collection.List[T], t : T) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) =>  snocAfterAppend(xs,l2,t)
    }) &&
    ((l1 ++ l2) :+ t == (l1 ++ (l2 :+ t)))
  }.holds

  def snocReverse[T](l : _root_.collection.List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocReverse(xs,t)
    }) &&
    ((l :+ t).reverse == _root_.collection.Cons(t, l.reverse))
  }.holds

  def reverseReverse[T](l : _root_.collection.List[T]) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => reverseReverse[T](xs) && snocReverse[T](xs.reverse, x)
    }) &&
    (l.reverse.reverse == l)
  }.holds

  //// my hand calculation shows this should work, but it does not seem to be found
  //def reverseAppend[T](l1 : List[T], l2 : List[T]) : Boolean = {
  //  (l1 match {
  //    case Nil() => true
  //    case Cons(x,xs) => {
  //      reverseAppend(xs,l2) &&
  //      snocAfterAppend[T](l2.reverse, xs.reverse, x) &&
  //      l1.reverse == (xs.reverse :+ x)
  //    }
  //  }) &&
  //  ((l1 ++ l2).reverse == (l2.reverse ++ l1.reverse))
  //}.holds

  //def associative[T,U](l1: List[T], l2: List[T], f: List[T] => U, op: (U,U) => U) = {
  //  f(l1 ++ l2) == op(f(l1), f(l2))
  //}
  //
  //def existsAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
  //  associative[T, Boolean](l1, l2, _.exists(p), _ || _ )
  //}.holds
  //
  //def forallAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
  //  associative[T, Boolean](l1, l2, _.exists(p), _ && _ )
  //}.holds

  //@induct
  //def folds[T,R](l : List[T], z : R, f : (R,T) => R) = {
  //  { l match {
  //    case Nil() => true
  //    case Cons(h,t) => snocReverse[T](t, h)
  //  }} &&
  //  l.foldLeft(z)(f) == l.reverse.foldRight((x:T,y:R) => f(y,x))(z)
  //}.holds
  //

  //Can't prove this
  //@induct
  //def scanVsFoldLeft[A,B](l : List[A], z: B, f: (B,A) => B): Boolean = {
  //  l.scanLeft(z)(f).last == l.foldLeft(z)(f)
  //}.holds

  @induct
  def scanVsFoldRight[A,B](l: _root_.collection.List[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  // A lemma about `append` and `updated`
  def appendUpdate[T](l1: _root_.collection.List[T], l2: _root_.collection.List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    // induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).updated(i, y) == (
        if (i < l1.size)
          l1.updated(i, y) ++ l2
        else
          l1 ++ l2.updated(i - l1.size, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T](l1: _root_.collection.List[T], l2: _root_.collection.List[T], n: BigInt): Boolean = {
    //induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }) &&
      // lemma
      ((l1 ++ l2).take(n) == (
        if (n < l1.size) l1.take(n)
        else if (n > l1.size) l1 ++ l2.take(n - l1.size)
        else l1)) &&
        ((l1 ++ l2).drop(n) == (
          if (n < l1.size) l1.drop(n) ++ l2
          else if (n > l1.size) l2.drop(n - l1.size)
          else l2))
  }.holds

  // A lemma about `append` and `insertAt`
  def appendInsert[T](l1: _root_.collection.List[T], l2: _root_.collection.List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).insertAt(i, y) == (
        if (i < l1.size) l1.insertAt(i, y) ++ l2
        else l1 ++ l2.insertAt((i - l1.size), y)))
  }.holds

}
