object ForwardReferenceExample extends App {

  /**
   * Scala hoists declarations of fields.
   * Hence, fields are visible with their default values
   * at the very beginning of the class/object it belongs to,
   * which means you refer to a variable before its lexical declaration.
   *
   * However, you usually has to use forward reference in company with
   * laziness to obtain the initialized value of the referred variable.
   */

  case class A ()

  case class B (val a: A)

  println(List(b1, b2))
  // List(null, null)

  val b1 = new B(a1) // b1.a is set to null due to call-by-value

  val b2 = new B(a2) // use lazy to archive call-by-need

  val a1 = new A

  lazy val a2 = new A

  println(b1.a) // null
  println(b2.a) // A

  /* forward reference is not allowed for non-field variables after Scala 2.10

   val b = c     // cannot compile
   val c = "foo"

   */
}
