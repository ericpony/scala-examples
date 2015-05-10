object REPL {

  def kleisliCompose[A, B, C](f: B => Option[C], g: A => Option[B]):
    A => Option[C] = {
      a: A => for (b <- g(a); c <- f(b)) yield c
    }

  implicit class InfixComposition[B, C](f: (B) => Option[C]) {
    def kleisliCompose[A](g: (A) => Option[B]):
      A => Option[C] = {
        a: A => for (b <- g(a); c <- f(b)) yield c
      }
  }

  def unsafeLogSqrt: Double => Double =
    scala.math.log _ compose scala.math.sqrt _

  def safeSqrt(d: Double): Option[Double] =
    if(d >= 0) Some(scala.math.sqrt(d)) else None

  def safeLog(d: Double): Option[Double] =
    if(d > 0) Some(scala.math.log(d)) else None

  def safeLogSqrt_v1(d: Double): Option[Double] =
    safeSqrt(d) flatMap safeLog

  def safeLogSqrt_v2(d: Double): Option[Double] =
    kleisliCompose(safeLog _, safeSqrt _)(d)

  def safeLogSqrt_v3(d: Double): Option[Double] =
    (safeLog _ kleisliCompose safeSqrt _)(d)
}
import REPL._

unsafeLogSqrt(100)
safeLogSqrt_v3(100)
