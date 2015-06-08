object MultipleDispatchExample extends App {

  class A

  class B

  trait TypePrinter[M] {
    def printType (m: M): Unit
  }

  implicit val TypePrinterForA = new TypePrinter[A] {
    def printType (m: A) = println("A")

  }
  implicit val TypePrinterForB = new TypePrinter[B] {
    def printType (m: B) = println("B")

  }

  def TypePrinterForAB[M] (implicit p: TypePrinter[M]) = new TypePrinter[M] {
    def printType (m: M) = p.printType(m)
  }


  /* Dispatch via implicit parameter */
  def foo[M] (m: M)(implicit p: TypePrinter[M]) =
    p.printType(m)

  /* Dispatch via pattern matching */
  def hoo[M] (m: M) =
    m match {
      case a: A => println("A");
      case b: B => println("B");
    }

  val a = new A
  val b = new B
  foo(a)
  foo(b)
  hoo(a)
  hoo(b)
}
