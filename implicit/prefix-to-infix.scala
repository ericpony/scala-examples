object PrefixToInfixConversionExample extends App {

  def kleisliCompose[A, B, C](f: B => Option[C], g: A => Option[B]): A => Option[C] =
    a => for (b <- g(a); c <- f(b)) yield c


  implicit class InfixComposition[B, C](f: (B) => Option[C]) {
    def kleisliCompose[A](g: (A) => Option[B]): A => Option[C] =
      a => for (b <- g(a); c <- f(b)) yield c
  }

  def unsafeLogSqrt: Double => Double =
    scala.math.log _ compose scala.math.sqrt _

  def safeSqrt(d: Double): Option[Double] =
    if (d >= 0) Some(scala.math.sqrt(d)) else None

  def safeLog(d: Double): Option[Double] =
    if (d > 0) Some(scala.math.log(d)) else None

  // monadic composition
  def safeLogSqrt_v1(d: Double): Option[Double] =
    safeSqrt(d) flatMap safeLog

  // prefix composition
  def safeLogSqrt_v2(d: Double): Option[Double] =
    kleisliCompose(safeLog _, safeSqrt _)(d)

  // infix composition
  def safeLogSqrt_v3(d: Double): Option[Double] =
    (safeLog _ kleisliCompose safeSqrt _)(d)

  println(unsafeLogSqrt(100))
  println(safeLogSqrt_v3(100))
}


