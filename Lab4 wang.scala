package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Yuxiang Wang>
   * 
   * Partner: <Your Partner's Name>
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */


  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if(h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
  }

  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: acc
      case h1::_ => if(h == h1) acc else h :: acc
    }
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case Some(x) => x :: t
      case None => h :: mapFirst(t)(f)

    }
  }

  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){(acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i}

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc, d) => acc match {
        case (b1, None) => (b1, Some(d))
        case (b1, nextitem) => (nextitem.get < d && b1, Some(d))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => lookup(env,x)
      case Decl(mode, x, e1, e2) =>{
        val v1=typeof(env, e1)
        val env1= extend(env, x, v1)
        typeof(env1,e2)

      } //typeof(env + (x -> typeof(env, e1)), e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }

      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }

      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (TNumber, t2) => err(t2, e2)
        case (TString, t2) => err(t2, e2)
        case (t1, _) => err(t1, e1)
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)

      }

      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, t2) => err(t2, e2)
        case (_, t2) => err(t2, e2)
        case (t1, _) => err(t1,e1)
        //case (t1, _) => err(t1, e1)
      }


      case Binary(Eq|Ne, e1, e2) =>
        (typeof(env, e1), typeof(env, e2)) match {
        case (e1v, e2v) => if (e1v == e2v) TBool else err(e2v, e2)
      }

      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TBool
        case (TBool, TBool) => TBool
        case (TNumber, TNumber) => TBool
        case (TBool,tv)=>err(tv,e2)

        case (TNumber, t2) => err(t2, e2)
        case (TString, t2) => err(t2, e2)

        case (tv, _) => err(tv, e1)
      }

      case Binary(And|Or, e1, e2) =>
        (typeof(env, e1), typeof(env, e2)) match {
      case(TBool,TBool) => TBool
      case(tgot,_) => err(tgot,e1)
      case (TBool,tgot) => err(tgot,e2)
      }

      case Binary(Seq, e1, e2) => (typeof(env, e1),typeof(env, e2)) match{
        case(t1,t2) => t2
        case(tgot,_) => err(tgot,e1)
        case(_,tgot) => err(tgot,e2)

      }

      case If(e1, e2, e3) =>
        if (typeof(env,e1) != TBool) return err(typeof(env,e1),e1)
        if (typeof(env,e2)  == typeof(env,e3)) return typeof(env,e2) else return err(typeof(env,e2),e2)
      /*typeof(env, e1) match{
        case TBool => {
          val t2 = typeof(env, e2)
          val t3 = typeof(env, e3)
          if(t2 == t3) t2 else err(t3, e)
        }
      }*/

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          //          case (Some(x), Some(t)) => extend(env, x , TFunction(params, t))
          case (Some(x), Some(t)) => extend(env,x, TFunction(params,t)) //env + (x -> TFunction(params, t))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1) {
          case (acc, (xi, MTyp(_, ti))) => extend(acc, xi, ti)
        }

        // Infer the type of the function body
        val t1 = typeof(env2, e1)

        // Check with the possibly annotated return type
        tann match {
          //case(Some(t)) if(t1==t) => TFunction(params,t)
          //case(Some(_)) => err(t1,e1)
          //case(None) => TFunction(params,t1)
          case Some(t) => if(t1 == t)TFunction(params, t) else err(t1, e1)
          case None => TFunction(params, t1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((x, MTyp(m, t)), arg) => {
              val ti = typeof(env, arg)
              if( ti != t)
                err(ti, arg)
            }
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map{ case (s, e1) => (s, typeof(env, e1))})

      case GetField(e1, f) =>typeof(env,e1) match {
        case TObj(rf) => rf.get(f) match
        {
          case Some(x) => return x
          case None => return err(typeof(env,e1), e1)
        }
        case _ => return err(typeof(env,e1), e1)
      }
    }
  }


  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      // case of string
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => if (s1 < s2) true else false
        case Le => if (s1 <= s2) true else false
        case Gt => if (s1 > s2) true else false
        case Ge => if (s1 >= s2) true else false
      }

      // case of number
      case (N(n1), N(n2)) => (bop: @unchecked) match {
        case Lt => if (n1 < n2) true else false
        case Le => if (n1 <= n2) true else false
        case Gt => if (n1 > n2) true else false
        case Ge => if (n1 >= n2) true else false
      }
    }


    // case _ => ??? // delete this line when done

  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case Some(x) => loop(x, n + 1)
      case None => e
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))

      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if(y == x) esub else e
      case Decl(mode, y, e1, e2) => if(y == x) Decl(mode, y, subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))

      /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        case None => {
          val sub1 = params.foldLeft(true)((acc, y) => if (x == y._1) acc && false else acc && true)
          if (sub1)
            Function(p, params, tann, subst(e1))
          else
            Function(p, params, tann, e1)
        }
        case Some(f) => {
          val sub2 = params.foldLeft(true)((acc, y) => if (x == y._1) acc && false else acc && true)
          if (x == f || sub2 == false)
            Function(p, params, tann, e1)
          else
            Function(p, params, tann, subst(e1))
        }
      }
      case Call(e1, args) => Call(subst(e1),args.map{case (earg) => subst(earg)})
      /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.map{case (f, e) => (f, subst(e))})
      case GetField(e1, f) => GetField(subst(e1),f)
    }

    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    //    subst(rename(e)(fresh))
    subst(e)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => ???
        case Binary(bop, e1, e2) => ???
        case If(e1, e2, e3) => ???

        case Var(y) =>
          ???
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          ???

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => ???
            case Some(x) => ???
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            ???
          }
          ???
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      /***** Cases needing adapting from Lab 3. */

      case Unary(Neg, N(n1)) => N(-n1)
      case Unary(Not, B(b1)) => B(!b1)

      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      case Binary(bop @(Lt|Le|Gt|Ge), N(n1), N(n2)) => B(inequalityVal(bop, N(n1), N(n2)))
      case Binary(bop @(Lt|Le|Gt|Ge), S(s1), S(s2)) => B(inequalityVal(bop, S(s1), S(s2)))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (v1, v2) => B(v1 == v2)
      }

      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (v1, v2) => B(v1 != v2)
      }

      case Binary(And, B(e1), e2) => B(e1) match{
        case B(true) => e2
        case B(false) => B(false)
      }

      case Binary(Or, B(e1), e2) => B(e1) match{
        case B(true) => B(true)
        case B(false) => e2
      }

      case If(B(e1), e2, e3) => B(e1) match{
        case B(true) => e2
        case B(false) => e3
      }


      case Decl(m, x, e1, e2) if !isRedex(m, e1) => substitute(e2, e1 ,x)

      /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall {case (pari @ (xi, mt@MTyp(mode, _)), argi) => !isRedex(mode, argi)}) {
              val e1p = pazip.foldRight(e1) {
                case (pargs @ ((x, MTyp(mode, t)), diffname), acc) => substitute(acc, diffname, x)
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                case ((xi, MTyp(mode, ti)), ei) => if(isRedex(mode, ei)) Some((xi, MTyp(mode, ti)), step(ei)) else None
              }
              val (_, nargs) = pazipp.unzip
              Call(v1, nargs)
            }
          }
          case _ => throw StuckError(e)
        }
      //      case GetField(Obj(map), f) => map(f) // Do GetField

      case GetField(Obj(map), f) => map.get(f) match {
        case Some(e) => e
        case None => throw new StuckError(e)
      }
    
      /***** New cases for Lab 4. */

      //getfield
      /*case GetField(Obj(fields),f) => fields.get(f) match{
        case Some(e1) => e1
        case None => throw new StuckError(e)
      }*/

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      /***** Cases from Lab 3. */
      case Unary(uop, e1) => Unary(uop,step(e1))

      /***** More cases here */
      //search binary
      case Binary(bop, v1, e2) => v1 match {
        case v1 if isValue(v1) => Binary (bop, v1, step (e2))
        case _ => Binary (bop, step (v1), e2)
      }
      // search if
      case If(e1,e2,e3) => If(step(e1), e2, e3)
      //search decl
      case Decl(mode,y, e1, e2) if(isRedex(mode, e1)) => Decl(mode, y, step(e1), e2)

      /***** Cases needing adapting from Lab 3 */
      // search call 1
      case Call(v1@Function(p, params, _, e1), args) => {
        val pazip = params zip args
        val pazippAll = mapFirst(pazip) {
          case (p, b) => if (isRedex(p._2.m, b)) Some(p, step(b)) else None
        }
        val Nargs = pazippAll.map(x => x._2)
        Call(v1, Nargs)
      }

      // search call 2
      case Call(e1, args) => Call(step(e1),args)
      //decl
      //case Decl(MConst,x,e1,e2) if(isRedex(MConst,e1)) => Decl(MConst,x,step(e1),e2)

      /***** New cases for Lab 4. */
      //obj
      /*case Obj(map) => Obj(map.foldLeft(Map():Map[String,Expr]){
        (acc: Map[String,Expr], m1: (String, Expr)) => {
          m1 match {
            case (s1,e1) if (isValue(e1)) => acc + (s1->e1)
            case (s1,e1) => acc + (s1->step(e1))
          }
        }
      })*/
      case Obj(fields) => {                                       //class note
        fields.find { case (fi, ei) => !isValue(ei) } match {
          case Some((fi, ei)) => {
            val ei2 = step(ei)
            Obj(fields + (fi->ei2))
          }
          case None => throw StuckError(e) //impossible, ei is v
        }
      }

      //getfield
      //case GetField(e1,f) => GetField(step(e1),f)
      case GetField(e1, f) => {
        if (isValue(e1)) {
          //Do
          e1 match {
            case Obj(fields) => fields(f)
            case _ => throw StuckError(e)
          }
        }
        else {
          // Search
          val e12 = step(e1)
          GetField(e12, f)
        }
      }
      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}


