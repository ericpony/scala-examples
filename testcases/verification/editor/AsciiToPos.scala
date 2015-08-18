import leon.lang._
import leon.lang.synthesis._
import leon.lang.string._
import leon.collection._

object Justify {
  def tokenize(ascii: collection.List[Char]): collection.List[String] = tokenize0(ascii, "")
  def tokenize0(ascii: collection.List[Char], wordAcc: String): collection.List[String] = ascii match {
    case Nil() => collection.Nil()
    case Cons(h, t) => if (h == ' ') {
      if (wordAcc.length == 0) {
        tokenize0(t, wordAcc)
      } else {
        collection.Cons(wordAcc, tokenize0(t, ""))
      }
    } else {
      tokenize0(t, String(collection.List(h)) + wordAcc)
    }
  }

  def asciiToPos(in: collection.List[Char], index: Int): collection.List[Int] = in match {
    case Nil() => collection.Nil()
    case Cons(head, tail) => if(head == ' ') collection.Cons(index, asciiToPos(tail, index+1)) else asciiToPos(tail, index+1)
  }

  def posToAscii(positions: collection.List[Int], originalText: collection.List[Char], currentPos: Int): collection.List[Char] = positions match {
    case Cons(start, rest) =>
      if(start > currentPos) {
        collection.Cons(' ', posToAscii(rest, originalText, currentPos+1))
      } else {
        originalText match {
          case Cons(l, ls) =>
            if(l == ' ') {
              collection.Cons(' ', posToAscii(rest, ls, currentPos+1))
            } else {
              collection.Cons(l, posToAscii(positions, ls, currentPos+1))
            }
          case Nil() => collection.Nil()
        }
      }
    case Nil() => collection.Nil()
  }

  def posToAsciiKeepTokens(ascii: collection.List[Char]) = {
    posToAscii(asciiToPos(ascii, 0), ascii, 0)
  } ensuring(res => tokenize(res) == tokenize(ascii))
}
