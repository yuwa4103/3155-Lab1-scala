package jsy.student

import jsy.lab5.Lab5Like

object Lab5 extends jsy.util.JsyApplication with Lab5Like {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <Yuxiang Wang>
   * Partner: <Tianlun Zhao>
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

  /*** Exercise with DoWith ***/

  def rename[W](env: Map[String,String], e: Expr)(fresh: String => DoWith[W,String]): DoWith[W,Expr] = {
    def ren(env: Map[String,String], e: Expr): DoWith[W,Expr] = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => doreturn(e)
      case Print(e1) => ren(env,e1) map { e1p => Print(e1p) }

      case Unary(uop, e1) => ren(env,e1).map {e1p => Unary(uop,e1p)}
      case Binary(bop, e1, e2) => ren(env,e1).flatMap{e1p => ren(env,e2).map {e2p => Binary(bop,e1p, e2p)}}
      case If(e1, e2, e3) => ren(env,e1).flatMap{e1p => ren(env,e2).flatMap {e2p => ren(env,e3).map {e3p =>If(e1p,e2p,e3p)}}}

      case Var(x) => doreturn(Var(env.getOrElse(x,x)))

      case Decl(m, x, e1, e2) => fresh(x) flatMap { xp => ren(env,e1) flatMap {e1p => ren(env+(x->xp), e2) map {e2p => Decl(m,xp,e1p,e2p)}}
      }

      case Function(p, params, retty, e1) => {
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => doreturn(None,env)
          case Some(x) => fresh(x) flatMap {xp => doreturn(xp) map {xpp => (Some(xpp), env + (x->xp))}}
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              case(paramsp, envpp) => fresh(x) map {xp => ((xp,mty) :: paramsp, envpp + (x -> xp))}
            }
          } flatMap {
            case(newparams, newenv) => ren(newenv, e1) map {e1p => Function(pp,newparams, retty, e1p)}
          }
        }
      }

      case Call(e1, args) => ren(env,e1) flatMap {e1p => mapWith(args)
           { arg => ren(env,arg)} map {argsp => Call(e1p, argsp)}}

      case Obj(fields) => {
        fields.foldRight[DoWith[W, Map[String, Expr]]](doreturn(Map[String, Expr]())) {
          (f,acc) => ren(env, f._2) flatMap{ep => acc map (a => a + (f._1 -> ep))}
        } map{fields => Obj(fields)}
      }
      case GetField(e1, f) => ren(env,e1) map {e1p => GetField(e1p,f)}
      case Assign(e1, e2) => ren(env,e1) flatMap {e1p => ren(env,e2) map {e2p => Assign(e1p,e2p)}}
      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }
  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>
      doget flatMap {a => doput(a+1) map {_ => "x" +a}}
    }
    val (_, r) = rename(empty, e)(fresh)(0)
    r
  }

  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {
    l.foldRight[DoWith[W,List[B]]]( doreturn(Nil:List[B]) ) {
  (h,acc) => {f(h) flatMap{ a => acc map { accp => a :: accp}}}
   }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W, Map[C, D]]](doreturn(Map.empty)) {
      (h, acc) => {
        acc.flatMap { hp => f(h). map { accp => hp + accp } }
      }
    }
  }

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
  case Nil => doreturn(Nil)
  case h :: t => f(h) match {
  case None => mapFirstWith(t)(f) map {n => h::n}
  case Some(x) => x map {n => n :: t}
 }
}

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    case (TObj(fields1), TObj(fields2)) => {
      val a = fields2 forall {
        case (field_1, t1) => fields1.get(field_1) match {
          case Some(t2) => if (t1 == t2) true else false
          case None => true
        }
      }

      val b = fields1 forall {
        case (field_1, t1) => fields2.get(field_1) match {
          case Some (t2) => if (t1 == t2) true else false
          case None => true
        }
      }
      a || b
    }
      /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = m match {
    case MRef if isLExpr(e) => true
    case MVar | MConst | MName => true
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
      case Var(x) => lookup(env,x) match{case (MTyp(_,t))=>t}
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
  case Unary(Not, e1) =>typeof(env, e1) match
{
  case TBool=> TBool
  case tgot => err(tgot,e1)
}
  case Binary(Plus, e1, e2) =>(typeof(env,e1),typeof(env,e2)) match
{
  case (TString,TString)=> TString
  case (TNumber,TNumber)=>TNumber
  case (TNumber,tgot)=>err(tgot,e2)
  case(TString,tgot)=>err(tgot,e2)
  case(tgot,_) => err(tgot,e1)
}
  case Binary(Minus|Times|Div, e1, e2) =>
  (typeof(env,e1),typeof(env,e2)) match {
  case(TNumber,TNumber) => TNumber
  case(tgot,_) => err(tgot,e1)
  case(TNumber,tgot) => err(tgot,e2)
}
  case Binary(Eq|Ne, e1, e2) =>
  (typeof(env,e1),typeof(env,e2)) match {
  case (e1got, e2got) => if (e1got == e2got) TBool else err(e1got, e1)

}
  case Binary(Lt|Le|Gt|Ge, e1, e2) =>
  (typeof(env,e1),typeof(env,e2)) match {
  case (TString, TString) => TBool
  case (TNumber, TNumber) => TBool
  case (TBool, TBool) => TBool
  case (TBool, tgot) => err (tgot, e2)
  case (TNumber, tgot) => err (tgot, e2)
  case (TString, tgot) => err (tgot, e2)
  case (tgot, _) => err (tgot, e1)
}
  case Binary(And|Or, e1, e2) =>
  (typeof(env,e1),typeof(env,e2)) match {
  case(TBool,TBool) => TBool
  case(tgot,_) => err(tgot,e1)
  case (TBool,tgot) => err(tgot,e2)
}

  case Binary(Seq, e1, e2) => typeof(env,e1); typeof(env,e2)

  case If(e1, e2, e3) =>
  if(typeof(env,e1) != TBool) return err(typeof(env,e1),e1)
  if(typeof(env,e2) == typeof(env,e3)) return typeof(env,e2) else return err(typeof(env,e2),e2)

  case Obj(fields) =>
  TObj(fields.mapValues(ei => typeof(env, ei)))
  case GetField(e1, f) =>
  typeof(env, e1) match {
  case TObj(tfields) => tfields.get(f) match {
  case Some(t) => t
  case None => err(TUndefined, e)
}
}

        /***** Cases from Lab 4 that need a small amount of adapting. */
  case Decl(m, x, e1, e2) if isBindex(m, e1) =>{
  // Bind to env1 an environment that extends env with an appropriate binding if
  // the function is potentially recursive.
  val t1 = typeof(env, e1)
  val t2 = typeof(extend(env, x, MTyp(m, t1)), e2)
  t2
}
  case Function(p, params, tann, e1) => {
  val env1 = (p, tann) match {
  case (Some(f), Some(tret)) =>
  val tprime = TFunction(params, tret)
  extend(env, f, MTyp(MConst, tprime))
  case (None, _) => env
  case _ => err(TUndefined, e1)
}
  // Bind to env2 an environment that extends env1 with bindings for params.
  val env2 = params.foldRight(env1) {
  case ((xi, mtypi), envi) => extend(envi, xi, mtypi)
}
  // Match on whether the return type is specified.
  val t1 = typeof(env2,e1)
  tann match {
  case None => TFunction(params,t1)
  case Some(tret) => if(t1 == tret) TFunction(params,tret) else err(t1,e1)
}

}
  case Call(e1, args) => typeof(env, e1) match {

  case TFunction(params, tret) if (params.length == args.length) =>
  (params, args).zipped.foreach {
  case (((_,MTyp(m,typ)), ei)) => {
  val ti = typeof(env,ei)
  if (typ != ti || !isBindex(m,ei)) err(ti,ei)
}
}
  tret
  case tgot => err(tgot, e1)

}

        /***** New cases for Lab 5. ***/
  case Assign(Var(x), e1) =>
  env.get(x) match {
  case Some(MTyp(mode,tx)) => {
  val t1 = typeof(env,e1)
  if (tx!= t1) err(TUndefined, e1)
  mode match {
  case MVar | MRef => t1
  case _ => err(TUndefined, e)
}
}
  case None => err(TUndefined, e)

}

  case Assign(GetField(e1, f), e2) => (typeof(env,e1), typeof(env,e2)) match {
  case (TObj(_), t2) => t2
  case (tgot, _) => err(tgot,e1)
}
  case Assign(_, _) => err(TUndefined, e)


  case Null => TNull

  case Unary(Cast(t), e1) => typeof(env, e1) match {
  case tgot if castOk(tgot,t) => t
  case tgot => err(tgot, e1)
}

  /* Should not match: non-source expressions or should have been removed */
  case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
}
}


  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case(S(s1),S(s2))=>
        bop match {
          case Lt => if (s1<s2) true else false
          case Le => if (s1<=s2) true else false
          case Gt => if (s1>s2) true else false
          case Ge => if (s1>=s2) true else false
        }
      case (N(n1),N(n2)) => bop match {
        case Lt => if (n1<n2) true else false
        case Le => if (n1<=n2) true else false
        case Gt => if (n1>n2) true else false
        case Ge => if (n1>=n2) true else false
      }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))

      /** *** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1, esub, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, esub, x), substitute(e2, esub, x))
      case If(e1, e2, e3) => If(substitute(e1, esub, x), substitute(e2, esub, x), substitute(e3, esub, x))
      case Var(y) => if (y == x) esub else e

      /** *** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))

      /** *** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) =>
        if (p == Some(x) || (paramse exists {
          case (y, _) => x == y
        })) e else Function(p, paramse, retty, subst(e1))

      /** *** Cases directly from Lab 4 */
      case Call(e1, args) => Call(subst(e1), args.map {
        case (arg) => subst(arg)
      })
      case Obj(fields) => Obj(fields.map {
        case (f, e) => (f, subst(e))
      })
      case GetField(e1, f) => GetField(subst(e1), f)

      /** *** New case for Lab 5 */
      case Assign(e1, e2) => Assign(substitute(e1, esub, x), substitute(e2, esub, x))

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }

    def myrename(e: Expr): Expr = {
      val fvs = freeVars(esub)

      def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x

      rename[Unit](e)(Nil) {
        x => doreturn(fresh(x))

      }
    }
      subst(myrename(e))
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
  case MConst | MVar => ! isValue (e)
  case MRef => ! isLValue (e)
  case MName => false
}

  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
  mode match {
  case MConst if isValue(e) => doreturn(e)
  case MName => doreturn(e)
  case MVar if isValue(e) => memalloc(e) map {a=>Unary(Deref, a)}
  case MRef if isLValue(e) => doreturn(e)
}
}

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, v1) if isValue(v1) => v1 match {
        case N(n) => doreturn(N(-n))
      }
      case Unary(Not, B(b)) => doreturn(B(!b))

      case Binary(Seq, v1, e2) if isValue(v1) => doreturn(e2)

      case Binary(bop @ (Plus|Minus|Times|Div), N(n1), N(n2)) => bop match {
        case Plus => doreturn(N(n1+n2))
        case Minus => doreturn(N(n1-n2))
        case Times => doreturn(N(n1*n2))
        case Div => doreturn(N(n1/n2))
      }
      case Binary(Plus, S(s1), S(s2)) => doreturn(S(s1+s2))

      case Binary(bop @ (Lt|Le|Gt|Ge), v1,v2) if (isValue(v1) && isValue(v2))  => doreturn(B(inequalityVal(bop,v1,v2)))

      case Binary(bop @ (Eq|Ne), v1, v2) if (isValue(v1) && isValue(v2)) => bop match {
        case Eq => doreturn(B(v1 == v2))
        case Ne => doreturn(B(v1 != v2))
      }
      case Binary(And, B(true), e2) => doreturn(e2)

      case Binary(And, B(false), e2) => doreturn(B(false))

      case Binary(Or, B(true), e2) => doreturn(B(true))

      case Binary(Or, B(false), e2) => doreturn(e2)

      case If(B(true), e2, e3) => doreturn(e2)

      case If(B(false), e2, e3) => doreturn(e3)

      case Unary(Cast(t), Null) => t match {
        case TObj(_) => doreturn(Null)
        case _ => throw DynamicTypeError(e)
      }
      case Unary(Cast(t), a@A(_)) => doget map { m =>
        val exists = ((m(a), t): @unchecked) match {
          case (Obj(fields), TObj(tfields)) => tfields.forall { case (f, typ) => fields.contains(f) }
        }
        if (!exists) throw DynamicTypeError(e)
        a
      }
      case Unary(Cast(t), v) if isValue(v) => doreturn(v)
  /***** Cases needing adapting from Lab 4. */

  case GetField(a @ A(_), f) =>
  doget map { m => m.get(a) match {
  case Some(Obj(fields)) => fields.get(f) match {
  case Some(field) => field
  case _ => throw StuckError(e)
}
  case _ => throw StuckError(e)
}
}

  case GetField(a @ A(_), f) =>
  doget map { m => m.get(a) match {
  case Some(Obj(fields)) => fields.get(f) match {
  case Some(field) => field
  case _ => throw StuckError(e)
}
  case _ => throw StuckError(e)
}
}



  case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn(substitute(e2, v1, x))
  case Decl(MVar, x, v1, e2) if isValue(v1) =>
  memalloc(v1) map {a => substitute(e2, Unary(Deref,a), x)}


  case Obj(fields) if (fields forall { case (_, vi) => isValue(vi) }) =>
  memalloc(e)


  /***** New cases for Lab 5. */
  case Unary(Deref, a@A(_)) => doget map {m => m(a)}
  case Assign(Unary(Deref, a@A(_)), v) if isValue(v) => domodify[Mem] {m => m + (a,v)} map {_ => v}
  case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
  domodify[Mem] { m => m.get(a) match {
  case Some(Obj(fields)) if(fields.contains(f)) => m + (a -> Obj(fields + (f -> v)))
  case _ => throw new StuckError(e)
}} flatMap { _ => doreturn(v)}
  case Call(v@Function(p, params, _, e1), args) => {
  val pazip = params zip args
  val redex = pazip.exists { case ((name, MTyp(mode, _)), ei) => isRedex(mode, ei) }
  if (!redex) {
  val dwep = pazip.foldRight(doreturn(e1): DoWith[Mem, Expr]) {
  case (((xi, MTyp(mi, _)), ei), dwacc) => dwacc flatMap { acc =>
  getBinding(mi, ei) map { eip => substitute(acc, eip, xi) }
}
}
  p match {
  case None => dwep
  case Some(x) => dwep map { ep => substitute(ep, v, x) }
}
}
  else {
  val dwpazipp = mapFirstWith(pazip) {
  case (m@(_, MTyp(mode, _)), ei) => if (isRedex(mode, ei)) Some(step(ei) map { eip => (m, eip) }) else None
}
  dwpazipp map { pazipp => Call(v, pazipp.unzip._2) }
}
}

  /* Base Cases: Error Rules */
  /***** Replace the following case with a case to throw NullDeferenceError.  */
  //case _ => throw NullDeferenceError(e)
  case GetField(Null, _) => throw NullDereferenceError(e)
  case Assign(GetField(Null, _), _) => throw NullDereferenceError(e)
  /* Inductive Cases: Search Rules */
  /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
  case Print(e1) => step(e1) map { e1p => Print(e1p) }

  case Unary(uop, e1) => step(e1) map { e1p => Unary(uop, e1p)}

  case Binary(bop, v1, e2) if isValue(v1) => step(e2) map { e2p => Binary(bop, v1, e2p)}

  case Binary(bop, e1, e2) => step(e1) map {e1p => Binary(bop, e1p, e2)}

  case If(e1, e2, e3) => step(e1) map { e1p => If(e1p, e2, e3)}

  /***** Cases needing adapting from Lab 4 */
  case GetField(e1, f) => step(e1) map { e1p => GetField(e1p, f)}

  case Obj(fields: Map[String,Expr]) =>
  fields find { case (_,x) => !isValue(x)} match {
  case Some((x1,x)) =>
  step(x) map {xp => Obj(fields + (x1 -> xp))}
  case None => throw StuckError(e)
}

  case Decl(mode, x, e1, e2) if isRedex(mode,e1) => step(e1) map {e1p => Decl(mode,x,e1p,e2)}

  case Call(e1, args) => step(e1) map { e1p => Call(e1p, args)}
        /***** New cases for Lab 5.  */
  case Assign(e1, e2) if !isLValue(e1) => step(e1) map {e1p => Assign(e1p,e2)}
  case Assign(e1, e2) => step(e2) map {e2p => Assign(e1,e2p)}
  /* Everything else is a stuck error. */
  case _ => throw StuckError(e)
}
}

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def lower(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
