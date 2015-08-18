import leon.annotation._
import leon.lang._
import leon.collection._

case class Entry(id: Int, version: Int, versionSynced: Int, f1: Int, f2: Int) {
  def update(f1: Int, f2: Int): Entry = {
    Entry(id, version+1, versionSynced, f1, f2) 
  }
  def markSynced = {
    Entry(id, version, version, f1, f2) 
  } ensuring { _.isSynced }

  def isSynced = {
    version == versionSynced
  }
}

object Sync {
  def idSorted(l: collection.List[Entry]): Boolean = l match {
    case Cons(v1, Cons(v2, xs)) => v1.id < v2.id && idSorted(collection.Cons(v2, xs))
    case _ => true
  }

  // Raw content (ignoring version/versionSynced)
  def content(l: collection.List[Entry]): Set[(Int, Int, Int)] = l match {
    case Cons(h, t) => Set((h.id, h.f1, h.f2)) ++ content(t)
    case Nil() => Set()
  }

  def ids(l: collection.List[Entry]): Set[Int] = l match {
    case Cons(h, t) => Set(h.id) ++ ids(t)
    case _ => Set()
  }

  def markSynced(l1: collection.List[Entry]): collection.List[Entry] = {
    require(idSorted(l1))
    (l1 match {
      case Cons(e1, t1) => collection.Cons(e1.markSynced, markSynced(t1))
      case Nil() => collection.Nil()
    }) : collection.List[Entry]
  } ensuring { res =>
    idSorted(res) && 
    content(res) == content(l1) && 
    ids(res) == ids(l1) && 
    allSynced(res)
  }

  def allSynced(l1: collection.List[Entry]): Boolean = {
    l1 match {
      case Cons(h1, t1) => h1.isSynced && allSynced(t1)
      case Nil() => true
    }
  }

  def sync(v1: collection.List[Entry], v2: collection.List[Entry]): collection.List[Entry] = {
    require(idSorted(v1) && idSorted(v2))

    ((v1, v2) match {
      case (Cons(e1, t1), Cons(e2, t2)) =>
        if (e1.id < e2.id) {
          collection.Cons(e1.markSynced, sync(t1, v2))
        } else if (e1.id > e2.id) {
          collection.Cons(e2.markSynced, sync(v1, t2))
        } else {
          if (e1.version > e2.version) {
            collection.Cons(e1.markSynced, sync(t1, t2))
          } else {
            collection.Cons(e2.markSynced, sync(t1, t2))
          }
        }
      case (Nil(), l2) => markSynced(l2)
      case (l1, Nil()) => markSynced(l1)
    }): collection.List[Entry]

  } ensuring {
   res =>
    idSorted(res) &&
    (content(res) subsetOf (content(v1) ++ content(v2))) &&
    (ids(res) == ids(v1) ++ ids(v2)) &&
    allSynced(res)
  }


  def test() = {
    val e1 = Entry(1, 1, 0, 1, 1)
    val e2 = Entry(2, 1, 0, 2, 2)
    val e3 = Entry(3, 1, 0, 3, 3)

    val l1 = collection.Cons(e1, collection.Cons(e2, collection.Nil()))
    val l2 = collection.Cons(e2.update(5, 5), collection.Cons(e3, collection.Nil()))

    sync(l1, l2)
  }
}

