object WhileLoopExample extends App {
  /**
   * Simulate while loop with closure and lazy evaluation
   */
  def While (cond: => Boolean)(body: => Unit) {
    if (cond) {
      body;
      While(cond)(body)
    }
  }

  def factorial (n: Int) = {
    var m = n
    var ret = 1
    While(m > 0) {
      ret = ret * m
      m = m - 1
    }
    ret
  }

  println(factorial(6))
}
