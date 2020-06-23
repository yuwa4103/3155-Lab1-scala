package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3
   * <Yuxiang Wang>
   *
   * Partner: <Ningtian Ruan>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
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
   */

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  override type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  override def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case S(s) => if (s == "" ) false else true
      case N(n) => if (n == 0 || n.isNaN ) false else true
      case Undefined => false
      case Function(_, _, _) => true
      case _ => throw new UnsupportedOperationException // delete this line when done
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if(b) "true" else "false"
      case N(n)  => if (n.isWhole) n.toInt.toString else n.toString
      case Undefined => "undefined"
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case _ => throw new UnsupportedOperationException // delete this line when done
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {

    e match {
      /* Base Cases */
      case _ if isValue(e) => e
      case Var(x) => lookup(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case Unary(Neg, e1) => N(- toNumber(eval(env, e1)))
      case Unary(Not, e1) => B(! toBoolean(eval(env, e1)))

      case Binary(Plus, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(Minus, e1, e2) => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
      case Binary(Times, e1, e2) => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
      case Binary(Div, e1, e2) => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))

      case Binary(Eq, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (Function(_,_,_), _) => throw new DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
        case (S(s1), S(s2)) => B(s1 == s2)
        case (N(n1), N(n2)) => B(n1 == n2)
        case (B(b1), B(b2)) => B(b1 == b2)
        case (_, _) => B(false)
      }
      case Binary(Ne, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (Function(_,_,_), _) => throw new DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
        case (S(s1), S(s2)) => B(s1 != s2)
        case (N(n1), N(n2)) => B(n1 != n2)
        case (B(b1), B(b2)) => B(b1 != b2)
        case (_, _) => B(true)
      }
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eval(env, e1), eval(env, e2)))

      case Binary(And, e1, e2) =>
        val v1 = eval(env, e1)
        if (toBoolean(v1)) eval(env, e2) else v1
      case Binary(Or, e1, e2) =>
        val v1 = eval(env, e1)
        if (toBoolean(v1)) v1 else eval(env, e2)

      case Binary(Seq, e1, e2) => eval(env, e1); eval(env, e2)

      case If(e1, e2, e3) => if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eval(env, e1)), e2)
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here

      case Call(e1,e2) => (eval(env,e1),eval(env,e2)) match {
        case (Function(None,x,ebody),v2) => eval(extend(env,x,v2),ebody)
        case (v1 @ Function(Some(x1),x2,ebody),v2) => eval(extend(extend(env,x2,v2),x1,v1),ebody)
        case (_,_) => throw new DynamicTypeError(e)
      }
      case _ => throw new UnsupportedOperationException
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = {
      next(e,n) match {
        case None =>e
        case Some(e) => loop(e,(n+1))
      }
    }
      loop(e0,0)
  }


  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case Var(y) => if (x==y) v else Var(y)
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case Function(p,y,e1) => p match {
        case None =>
        {
          if (x==y) e 
          else Function(p,y,subst(e1))
        }
        case Some(f) =>
        {
          if (x==f || x==y) e
          else Function(Some(f),y,subst(e1))
        }
      }
      case Binary(bop,e1,e2) => Binary(bop,subst(e1),subst(e2))
      case Unary(uop,e1) => Unary(uop,subst(e1))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case ConstDecl(y, e1, e2) =>
      {
        if (x == y) ConstDecl(y, subst(e1), e2)
        else ConstDecl(y, subst(e1), subst(e2))
      }
      case Call(e1,e2) => Call(subst(e1),subst(e2))
      case _ => throw new UnsupportedOperationException
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, v) if isValue(v) => N(- toNumber(v))
      case Unary(Not, v) if isValue(v) => B( ! toBoolean(v))
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case(S(v1), _) => S(v1 + toStr(v2))
        case(_, S(v2)) => S(toStr(v1) + v2)
        case(_, _) => N(toNumber(v1) + toNumber(v2))
      }
      /* Do Arith */
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) - toNumber(v2))
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) * toNumber(v2))
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) / toNumber(v2))

      /* Do inequality: number, number2, string */
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))

      case Binary(bop @ (Eq | Ne), v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (Function(_, _, _), _) => throw new DynamicTypeError(e)
        case (_,Function(_, _, _)) => throw new DynamicTypeError(e)
        case (v1,v2) if isValue(v1) && isValue(v2) => {
          if (bop == Eq) B(v1 == v2)
          else B(v1 != v2)
        }
      }

      case Binary(And, v1, e2) if isValue(v1) => toBoolean(v1) match{
        case true => e2
        case _ => v1
      }

      case Binary(Or, v1, e2) if isValue(v1) => toBoolean(v1) match{
        case false => e2
        case _ => v1
      }

      case If(v1, e2, e3) if isValue(v1) => toBoolean(v1) match{
        case true => e2
        case false => e3
      }

      case ConstDecl(x, v1, e2) if isValue(v1) => {
        substitute(e2, v1, x)
      }
      /* substitute takes: e: expr, v: expr, x: string */

      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match{
        /* Not recursive */
        case Function(None, x, e) => {
          substitute(e, v2, x)
        }
        /* Recursive */
        case Function(Some(f), x2, fbody) => {
          substitute(substitute(fbody, v1, f), v2, x2)
        }
        case _ => throw new DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      //SearchBinary//
      case Binary(bop, e1, e2) => e1 match {
        //SearchBinaryArith2//
        case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => Binary(bop, e1, step(e2))
        //SearchBinary1//
        case _ => Binary(bop, step(e1), e2)
      }
      //SearchUnary//
      case Unary(uop, e1) => Unary(uop, step(e1))

      //SearchIf//
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      //SearchConst//
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      //SearchCall//
      case Call(e1, e2) => (e1,e2) match {
        case (Function(_, _, _), s2) =>  Call(e1, step(s2))
        case (s1,s2) => Call(step(s1),s2)
        //case _ => throw new TypeErrorCall(e)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }



  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
