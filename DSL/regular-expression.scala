import scala.language.implicitConversions

/**
 * A application of implicits conversion to designing
 * domain-specific languages in Scala.
 *
 * Reference: http://matt.might.net/articles/learning-scala-in-small-bites/
 */

sealed abstract class RegExp {

  // Characters:
  private case class StrExp (str: String) extends RegExp

  // Sequences:
  private case class Sequence (left: RegExp, right: RegExp) extends RegExp

  // Alternation:
  private case class Alternation (left: RegExp, right: RegExp) extends RegExp

  // Kleene repetition:
  private case class Repetition (exp: RegExp) extends RegExp

  // Empty:
  private case object Empty extends RegExp

  def ~ (right: RegExp): RegExp = Sequence(this, right)

  def | (right: RegExp): RegExp = Alternation(this, right)

  def * = Repetition(this): RegExp

  def matches (s: String): Boolean = {
    def accept (pos: Int, regexp: RegExp, rest: Int => Boolean): Boolean =
      regexp match {
        case StrExp(str)              => s.startsWith(str, pos) && rest(pos + str.length)
        case Repetition(regex)        => rest(pos) || accept(pos, regex, accept(_, Repetition(regex), rest))
        case Sequence(left, right)    => accept(pos, left, accept(_, right, rest))
        case Alternation(left, right) => accept(pos, left, rest) || accept(pos, right, rest)
        case Empty                    => rest(pos)
      }
    accept(0, this, _ == s.length)
  }
}

object RegExp {
  // Automatically convert strings into regexes:
  implicit def stringToRegExp (str: String): RegExp = {
    val r = new RegExp() {}
    r.StrExp(str)
  }
}

object RegExpDSLExample extends App {

  import RegExp._

  // Implicits and operator overloading makes the syntax terse:
  val regexp = (("b" | "a") *) ~ "ca" *;

  println(regexp) // print the AST
  println(regexp.matches("abbacaca"))
}