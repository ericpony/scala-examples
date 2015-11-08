class Box[E] (e: E) {
  def unbox: E = e

  def rebox[E] (e: E): Box[E] = new Box(e)

  def rebox1 (e: E): Box[E] = new Box(e) // will lead to a compile-time error
}

val box1 = new Box(1)
val box2 = new Box("ok")
val box3 = new Box(3.14)
val boxes: Seq[Box[_]] = Seq(box1, box2, box3)

boxes.head == box1                  // true
boxes.head.unbox == box1.unbox      // true
box1.rebox(box1.unbox) == box1      // false

box1.rebox(box1.unbox)              // ok
boxes.head.rebox(box1.unbox)        // ok

box1.rebox1(box1.unbox)             // ok
boxes.head.rebox1(boxes.head.unbox) // boo!

