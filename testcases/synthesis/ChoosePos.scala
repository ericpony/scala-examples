import leon.lang._
import leon.lang.synthesis._

object ChoosePos {


def c1(x: Int): Int =
  choose {
    (y: Int) => y > x
  }

def c2(x: Int): Int =
  choose (
    (y: Int) => y > x
  )
		def c3(x: Int): Int = choose { (y: Int) => y > x }
        def c4(x: Int): Int = choose { (y: Int) => y > x }; def c5(x: Int): Int = choose { (y: Int) => y > x }

}
