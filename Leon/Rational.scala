import leon.lang._

import scala.language.implicitConversions

case class Rational (n: BigInt, d: BigInt) {

  private def gcd (a: BigInt, b: BigInt): BigInt = {
    require(a * b != 0)
    if (b == 0) a.abs else gcd(b, a % b)
  } ensuring (_ != 0)

  def simplify: Rational = {
    require(isRational)
    val divisor = gcd(n, d)
    Rational(n / divisor, d / divisor)
  }

  def + (that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d + that.n * d, d * that.d).simplify
  } ensuring {
    _.isRational
  }

  def * (that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.n, d * that.d).simplify
  } ensuring {
    _.isRational
  }

  def - (that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d - that.n * d, d * that.d).simplify
  } ensuring {
    _.isRational
  }

  def <= (that: Rational): Boolean = {
    require(isRational && that.isRational)
    n * that.d <= that.n * d
  }

  def == (that: Rational): Boolean = {
    require(isRational && that.isRational)
    this.n == that.n && this.d == that.d
  }

  def closed_lemma (other: Rational): Rational = {
    require(isRational)
    Rational(n * other.d + other.n * d, d * other.d)
  }.ensuring {
    _.isRational
  }

  def nonnegative_lemma (other: Rational): Boolean = {
    require(other.d * other.n >= 0)
    this <= (other + this)
  }.holds

  def idempotent_lemma: Boolean = {
    require(isRational)
    this.simplify.simplify == this.simplify
  }.holds

  def isRational = d != 0

  def nonZero = n != 0

  def isSimplified (r: Rational) = r == r.simplify
}
