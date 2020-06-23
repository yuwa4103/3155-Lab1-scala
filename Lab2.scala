package jsy.student

import jsy.lab2.Lab2Like

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Yuxiang Wang>
   * 
   * Partner: <Sibo Song>
   * Collaborators: <Zhaozhong Peng>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */



  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   *
   * You can catch an exception in Scala using:
   * try ... catch { case ... => ... }
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case Undefined => Double.NaN
      case S(s)=>try { s.toDouble } catch { case _: Throwable => Double.NaN }
      case B(true) => 1
      case B(false) => 0
      case _ => throw new UnsupportedOperationException
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(0) => false
      case N(n) => if (n.isNaN()) false else true
      case S("") => false
      case S(_) => true
      case Undefined => false
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if(b == true) "true" else "false"
      case N(n)	=> if (n.isWhole) n.toInt.toString else n.toString
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case S(s) => e
      case N(n) => e
      case B(b) => e
      case Var(x) => lookup(env, x)
      case Undefined => Undefined

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      //case ConstDecl(x, e1, e2) => {
        //val v1 = eval(env, e1)
        //val env2 = extend(env, x, v1)
        //val v2: Expr = eval(env2, e2)
        //v2
      //}
      case ConstDecl(x, e1, e2) => {
        eval(extend(env, x, eval(env,e1)), e2)}

      case Binary(bop, e1, e2) => bop match {
        // +      class note
        case Plus => {
          val v1 = eval(env, e1)
          val v2 = eval(env, e2)
          (v1, v2) match {
            case (S(v1), S(v2)) => S(v1 + v2)
            case (S(v1), _) => S(v1 + toStr(v2))
            case (_, S(v2)) => S(toStr(v1) + v2)
            case _ => N(toNumber(v1) + toNumber(v2))
          }
        }
        case Minus => {
          val v1 = eval(env, e1)
          val v2 = eval(env, e2)
          N(toNumber(v1) - toNumber(v2))

        }
        case Times => {
          val v1 = eval(env, e1)
          val v2 = eval(env, e2)
          N(toNumber(v1) * toNumber(v2))
        }
        case Div => {
          val v1 = eval(env, e1)
          val v2 = eval(env, e2)
          N(toNumber(v1) / toNumber(v2))
        }

        case Eq => {
          if (eval(env,e1) == eval(env, e2)) B(true) else B(false)
        }
        case Ne => {
          if (eval(env,e1) != eval(env, e2)) B(true) else B(false)
        }
        case Lt => {                  //discussed with Zhaozhong Peng
          val v1 = (eval(env, e1))
          val v2 = (eval(env, e2))
          (v1, v2) match {
            case(B(v1), B(v2)) => B(v1 < v2)
            case(S(v1),S(v2)) => B(v1 < v2)
            case _ => B(toNumber(v1) < toNumber(v2))
          }
        }
        case Le => {
          val v1 = (eval(env, e1))
          val v2 = (eval(env, e2))
          (v1, v2) match {
            case(B(v1), B(v2)) => B(v1 <= v2)
            case(S(v1),S(v2)) => B(v1 <= v2)
            case _ => B(toNumber(v1) <= toNumber(v2))
          }
        }
        case Gt => {
          val v1 = (eval(env, e1))
          val v2 = (eval(env, e2))
          (v1, v2) match {
            case(B(v1), B(v2)) => B(v1 > v2)
            case(S(v1),S(v2)) => B(v1 > v2)
            case _ => B(toNumber(v1) > toNumber(v2))
          }
        }
        // >=
        case Ge => {
          val v1 = (eval(env, e1))
          val v2 = (eval(env, e2))
          (v1, v2) match {
            case(B(v1), B(v2)) => B(v1 >= v2)
            case(S(v1),S(v2)) => B(v1 >= v2)
            case _ => B(toNumber(v1) >= toNumber(v2))
          }
        }
        case And => {
          if ( toBoolean(eval(env,e1)) ) eval(env,e2) else eval(env, e1)
        }
        case Or => {
          if( toBoolean(eval(env,e1)) ) eval(env,e1) else eval(env, e2)
        }
        case Seq => {
          eval(env, e1)
          eval(env, e2)
        }



        case _ => throw new UnsupportedOperationException
      }
      case If(e1, e2, e3) => {
        if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
      }

      case Unary(uop, e) => uop match {
        case Neg => N( -toNumber( eval(env, e) ) )
        case Not => B( !toBoolean( eval(env, e) ) )
      }
      case _ => throw new UnsupportedOperationException
    }
  }




  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
