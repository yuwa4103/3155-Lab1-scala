package jsy.student

import jsy.lab1._

object Lab1 extends jsy.util.JsyApplication with jsy.lab1.Lab1Like {
  import jsy.lab1.Parser
  import jsy.lab1.ast._

  /*
   * CSCI 3155: Lab 1
   * <YUXIANG WANG>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function. The
   * '???' expression is a Scala expression that throws a NotImplementedError
   * exception.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * '???' as needed to get something that compiles without error.
   */

  /*
   * Example: Test-driven development of plus
   *
   * A convenient, quick-and-dirty way to experiment, especially with small code
   * fragments, is to use the interactive Scala interpreter. The simplest way
   * to use the interactive Scala interpreter in IntelliJ is through a worksheet,
   * such as Lab1Worksheet.sc. A Scala Worksheet (e.g., Lab1Worksheet.sc) is code
   * evaluated in the context of the project with results for each expression
   * shown inline.
   *
   * Step 0: Sketch an implementation in Lab1.scala using ??? for unimmplemented things.
   * Step 1: Do some experimentation in Lab1Worksheet.sc.
   * Step 2: Write a test in Lab1Spec.scala, which should initially fail because of the ???.
   * Step 3: Fill in the ??? to finish the implementation to make your test pass.
   */

  //def plus(x: Int, y: Int): Int = ???
  def plus(x: Int, y: Int): Int = x + y

  /* Exercises */

  def abs(n: Double): Double = if (n <= 0) -n else n

  def xor(a: Boolean, b: Boolean): Boolean = {
    if (a == b) false
    else
      true
  }
//a and b both true or false, then false
  def repeat(s: String, n: Int): String = {
    require(n >= 0)
    if (n > 0) {s + repeat(s,n-1)}
    else ""
  }
//repeat (a,3)-》 a+ repeat(a,3-1=2)->a+repeat(a,2-1=1），until 1-1=0, berak
  def sqrtStep(c: Double, xn: Double): Double = xn - (xn * xn - c) / (2 * xn)

  def sqrtN(c: Double, x0: Double, n: Int): Double = {
    require(c >= 0 && n >= 0)
    if (n == 0) x0
    else {sqrtN(c,sqrtStep(c,x0),(n-1))}
    // if (n>0) {sqrtN(c,sqrtStep(c,x0),(n-1))} else {x0}
    //if recursion n time until n = 0, if not ,back sqrtN
  }


  def sqrtErr(c: Double, x0: Double, epsilon: Double): Double = {
    require(epsilon > 0)
    if (abs((x0*x0)-c)>=epsilon) {sqrtErr(c,sqrtStep(c,x0),epsilon)} else {x0}
  }
//the value of abs > epsilon, that mean they are not approximate value, need go back calculate again until error<epsilon

  def sqrt(c: Double): Double = {
    require(c >= 0)
    if (c == 0) 0 else sqrtErr(c, 1.0, 0.0001)
  }

  /* Search Tree */

  // Defined in Lab1Like.scala:
  //
  // sealed abstract class SearchTree
  // case object Empty extends SearchTree
  // case class Node(l: SearchTree, d: Int, r: SearchTree) extends SearchTree

  def repOk(t: SearchTree): Boolean = {
    def check(t: SearchTree, min: Int, max: Int): Boolean = t match {
      case Empty => true
      case Node(l, d, r) => if ((d >= min) && (d < max) && check(l,min,d) && check(r,d,max)) {true}
      else {false}
//d need >= min and < max, min in the left and max on the right, check left tree and right tree
    }
    check(t, Int.MinValue, Int.MaxValue)
  }

  def insert(t: SearchTree, n: Int): SearchTree =  t match {
    case Empty => Node(Empty, n, Empty)
    case Node(l,d,r) => if (n >= d) Node(l,d,insert(r,n)) else Node(insert(l,n),d,r)
  }
//if emoty, insert n =d, else small go left, large go right
  def deleteMin(t: SearchTree): (SearchTree, Int) = {
    require(t != Empty)
    (t: @unchecked) match {
      case Node(Empty, d, r) => (r, d)
      case Node(l, d, r) =>
        val (l1, m) = deleteMin(l)
        (Node(l1, d, r), m)
    }
  }
//return a searchtree, if left empty, then d is the min, so delete d and become tree, if left not empty, use d to
  //compare its left child, if left child smaller then child become new d, and compare again, recursion until min.
  def delete(t: SearchTree, n: Int): SearchTree = t match {
    case Empty => Empty
    case Node(l, d, r) =>
      if (d == n) r match {
        case Empty => l
        case r =>
          val (r1, m): (SearchTree, Int) = deleteMin(r)
          Node(l, m, r1)
      }
      else if (d < n) Node(l, d, delete(r, n))
      else Node(delete(l, n), d, r)
  }


  /* JavaScripty */

  def eval(e: Expr): Double = e match {
    case N(n) => n
    case Unary(Neg, e) => -(eval(e))
    case Binary(Plus, b1, b2) => (eval(b1) + eval(b2))
    case Binary(Minus, b1, b2) => (eval(b1) - eval(b2))
    case Binary(Times, b1, b2) => (eval(b1) * eval(b2))
    case Binary(Div, b1, b2) => (eval(b1) / eval(b2))
  }

 // Interface to run your interpreter from a string.  This is convenient
 // for unit testing.
 override def eval(s: String): Double = eval(Parser.parse(s))



 /* Interface to run your interpreter from the command-line.  You can ignore the code below. */

 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

    println(prettyNumber(v))
  }

}
