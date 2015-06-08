object UnboxingExample extends App {

  class Box[E] (e: E) {
    def unbox: E = e

    //def rebox[E](e: E): Box[E] = new Box(e) // use this instead to avoid the error below
    def rebox (e: E): Box[E] = new Box(e) // will lead to a compile-time error
  }

  val box1 = new Box(1)
  val box2 = new Box("ok")
  val box3 = new Box(3.14)
  val boxes: Seq[Box[_]] = Seq(box1, box2, box3)

  box1.rebox(box1.unbox) // ok
  /*
  boxes.head.rebox(boxes.head.unbox) // compile-time error!
  */
}
