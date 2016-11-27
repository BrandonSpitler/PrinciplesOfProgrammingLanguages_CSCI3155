package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
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
    case Nil | _ :: Nil => l;//list is Nil and prepends all h1 to nil list ex h1::h1::h1::nil
    case h1 :: (t1 @ (h2 :: _)) =>  if(h1 != h2) h1 :: compressRec(t1) else compressRec(t1);
    //h1 is head of list, t1 is tail, h2 is head of tail
    //if h1 != h2, prepend(::) h1 to compressRec(t1), else compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) =>
      if(acc == Nil) h :: acc;//prepend(::) h to acc
      else if (acc != Nil && h != acc.head) h :: acc;//if list is not nil and h != first element in acc
        //prepend h to acc;
      else acc;//else acc;
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l;//if function never returns anything list reaches Nil
    // and prepends all h1 to nil list ex h1::h1::h1::nil
    case h :: t => f(h) match { //function of f(h) match
      case None => h :: mapFirst(t)(f) ; //function(head) returns none then prepend head to mapFirst(tail)(function)
      case Some(e) => e :: t; //function(head) returns something then prepend something to rest of list(tail)
        //ex h1::h1::e::t
    }
  }

  /* Trees */
  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc;//t is empty return acc = 0
      case Node(l, d, r) => loop(f(loop(acc,l),d),r);//if node then loop with function of loop and d, and r
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc,x) => acc match{//acc is bool, x is number
        case (b1,None) => (b1,Some(x)) //if Some(x) is None then
        // no calculation was performed no need to check
        case  (b1, Some(e)) => if(e < x) (b1 && true,Some(e)) else (false,Some(e));
          //else if x returned Some(e) then need to check e because e is next
          //val in tree, so if e < x then true else false
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
      case Print(e1) => typeof(env, e1); TUndefined //1
      case N(_) => TNumber//2
      case B(_) => TBool//3
      case Undefined => TUndefined//4
      case S(_) => TString//5
      //Rule TypeVar
      case Var(x) => lookup(env,x);//5
      //Rule TypeConst
      case Decl(mode, x, e1, e2) => //6
        val typee1 = typeof(env,e1)
        val newEnv = env + (x -> typee1)
        typeof(newEnv,e2);
      // Rule TypeNeg
      case Unary(Neg, e1) => typeof(env, e1) match { //7
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      //Rule TypeNot
      case Unary(Not, e1) => typeof(env,e1) match {
          case TBool  => TBool
          case tgot => err(tgot,e1);
        }
      //Rule TypePlusString,TypeArith+
      case Binary(Plus, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
          case (TString,TString) => TString
          case (TNumber,TNumber) => TNumber
          case (tgot,_)  => err(tgot,e1);
          case (_,tgot)  => err(tgot,e2);
        }
       //Rule TypeArith-*/
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env,e1),typeof(env,e2)) match {
          case (TNumber,TNumber) => TNumber
          case (tgot,_)  => err(tgot,e1);
          case(_,tgot) => err(tgot,e2)  ;
        }
      //Rule TypeEquality
      case Binary(Eq|Ne, e1, e2) if typeof(env, e1) != TFunction && typeof(env, e2) != TFunction =>  (typeof(env, e1), typeof(env, e2)) match {  //not sure if correct
          case (t1,t2) if t1 == t2 => TBool;
          case (tgot,_) => err(tgot,e1);
          case(_,tgot) => err(tgot,e2) ;
        }
      //Rule TypeInequality
      case Binary(Lt|Le|Gt|Ge, e1, e2) => //12
        (typeof(env,e1),typeof(env,e2)) match{
          case (TString,TString) => TBool
          case (TNumber ,TNumber) => TBool
          case (tgot,_) => err(tgot,e1);
          case(_,tgot) => err(tgot,e2) ;
        }
      //Rule TypeAndOr
      case Binary(And|Or, e1, e2) => (typeof(env,e1),typeof(env,e2)) match{ //13
        case (TBool,TBool) => TBool;
        case (tgot,_) => err(tgot,e1);
        case(_,tgot) => err(tgot,e2) ;
      }
      //Rule TypeSeq
      case Binary(Seq, e1, e2) => (typeof(env,e1),typeof(env,e2)) match{
          case (t1,t2) => t2;
        }
      //Rule TypeIf
      case If(e1, e2, e3) => (typeof(env,e1),typeof(env,e2),typeof(env,e3)) match { //15
        case(TBool,x1,x2) if x1==x2  => x1
        case (tgot, _, _) => err(tgot, e1)   //check if line is right
        case (_, tgot, _) => err(tgot, e2)   //check if line is right
        case (_, _, tgot) => err(tgot, e3)  //check if line is right
      }

      //Rule Function
      case Function(p, params, tann, e1) =>  //16
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          //p:option string and tann:option type
          /** *** Add cases here *****/
          case (None, None) => env; //if return none then return default env
          case (None,Some(t)) => env;
          case (Some(s), Some(t)) => //if both return a value
            val one = TFunction(params, t); //type one = function with params and type t
            env + (s -> one); //adds string e -> to the type of one
          case _ => err(TUndefined, e1) // else err
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 =  params.foldLeft(env1){(acc,h) => extend(acc,h._1, h._2.t) }   //check
        // Infer the type of the function body
        val t1 = typeof(env2,e1)
        tann match{ //type of tann , type of e1
          case Some(tcheck) => if (tcheck == t1) TFunction(params,t1)  else err(t1,e1);//type of tann and other then TFunction else err
          case None => TFunction(params,t1);//err
        }

      case Call(e1, args) => typeof(env, e1) match { //17
        case TFunction(params, tret) if params.length == args.length =>
          (params zip args).foreach { //params:(string->typeOf),args:(a) -> ((string,typeOf),arg)
          // case ((_, ty), argument) => if (ty.t != typeof(env,argument)) err(typeof(env,argument),argument) else  ty.t;
            paramsvsargs => if(paramsvsargs._1._2.t == typeof(env, paramsvsargs._2)) paramsvsargs._1._2.t else throw StaticTypeError( typeof(env, paramsvsargs._2), e1, e )
          }//string to t, check if t is type of argument, if not then throw err, else we are good because every type is compatible with type of argument
          tret
        case tgot => err(tgot, e1)
      }

      case Obj(fields) => TObj(fields mapValues( exp => typeof(env,exp)));//18 //maps obj:(string,exp) to (string,type(expression)) = TObj;
      //GetField
      case GetField(e1, f) =>
        val typeE1 = typeof(env,e1);//looks up type of expression1
        typeE1 match{ //match to typeE1
          //if string f is a key in TObj fields then look up type, else return err
          case (TObj(fields)) => if(fields.contains(f)) fields(f) else throw StaticTypeError(typeof(env, e1), e1, e);
          case _ => throw StaticTypeError(typeof(env, e1), e1, e);//else err
        }
    }
  }

//ABOVE GOOD

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
      case (S(s1), S(s2)) => bop match {
        case Lt => if(s1 < s2) true else false
        case Le => if(s1 <= s2) true else false
        case Gt => if(s1 > s2) true else false
        case Ge => if(s1 >= s2) true else false
      }
      case (N(n1),N(n2)) => bop match {
        case Lt => if(n1 < n2) true else false
        case Le => if(n1 <= n2) true else false
        case Gt => if(n1 > n2) true else false
        case Ge => if(n1 >= n2) true else false
      }

    }
  }
//iterate
  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(e) => loop(e,n + 1)
    }
    loop(e0, 0)
  }
//substitute
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    require(isValue(esub))
   def subst(e: Expr): Expr =
  //  val fvs = freeVars(e)
    //def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
      /* Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2)) //replace all x in e1 with y, replace all x in e2 with y
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (y == x) esub else e
      case Decl(mode, y, e1, e2) =>  if (y == x) Decl(mode, y, subst(e1), e2) else Decl(mode, y, subst(e1),  subst(e2)) // rename(e1)(x=> fresh(x))
      /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        if(params.exists((parameter: (String, MTyp)) => parameter._1 == x))
          Function(p, params, tann, e1)
        else
          Function(p, params, tann, subst(e1))

      case Call(e1, args) => Call(subst(e1), args.map{case (arg) => subst(arg)})  //check if right

      case Obj(fields) => Obj(fields.mapValues(expr=> subst(expr)))  //check if right

      case GetField(e1, f) => GetField(subst(e1), f)// e1 is expression and f is the string, no need to check if f==x since in PDF it says object expressions are not variable binding constructs
    }
    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(e) //subst(???)
    }


  /* Rename bound variables in e */
  /* Rename bound variables in e */
  def rename(e: Expr)(renameVar: String => String): Expr = {
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
          val yp = renameVar(y)
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
    ren(Map.empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case Const => !isValue(e);
    case Name => false;
  }


  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, N(n1)) => N(-n1)
      case Unary(Not, B(b1)) => B(!b1)
      case Binary(Seq, v1, e1) if isValue(v1) => e1
      case Binary(bop @ (Plus | Minus | Times | Div), N(n1), N(n2)) => bop match{
        case Plus => N(n1+n2)
        case Minus => N(n1-n2)
        case Times => N(n1*n2)
        case Div => N(n1/n2)
      }
      case Binary(Plus, S(s1), S(s2)) => S(s1+s2)
      case Binary(bop @ (Lt | Le | Gt | Ge), N(n1), N(n2)) => B(inequalityVal(bop,N(n1),N(n2)))
      case Binary(bop @ (Lt | Le | Gt | Ge), S(s1), S(s2)) => B(inequalityVal(bop,S(s1),S(s2)))
      case Binary(Eq, v1,v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1,v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case Binary(And, B(true), e2)  => e2
      case Binary(And, B(false), e2)  => B(false)
      case Binary(Or, B(true), e2)  => B(true)
      case Binary(Or, B(false), e2)  => e2
      case If(B(true),e2,e3) => e2
      case If(B(false),e2,e3) => e3
      case Decl(mode, x, e1, e2) if !isRedex(mode, e1) => mode match {
        case Const => substitute(e2, e1, x)
        case Name => substitute(e2, e1, x)
      }
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args //so now a list of tuples (param1, arg1)...(paramn,argn)
            if ( pazip.forall{ case ((_,MTyp(mi, _)), ei) => !isRedex(mi, ei)}) { //i think the ??? has to do with redex
            val e1p = pazip.foldRight(e1) {
              (h, acc) => substitute(acc, h._2,h._1._1)  // syntax is ((string, MType), expression) aka ((parameter name, parameter type), argument) so replace all calls of parameter name with the argument expression
            }
              p match {
                case None => e1p //since has no name just return
                case Some(x1) => substitute(e1p, v1,x1)   //now since this function has name go replace all instances of the name with the actual function
              }
            }
            //searchcall2
            else {
              val pazipp = mapFirst(pazip) {

                case (p, a) => if(isRedex(p._2.m, a)) Some(p, step(a)) else None
                //if argument is value do nothing
                //if not a value you need to step on that argument
              }
              val new_args = pazipp.map(x => x._2)
              Call(v1, new_args) //call with new arguments
            }
          }
          case _ => throw StuckError(e)
        }
      /*Search Cases */
      case Print(e1) => Print(step(e1))
      case Unary(uop,e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) => v1 match {
        case v if isValue(v1) => Binary (bop, v1, step (e2))
        case _ => Binary (bop, step (v1), e2)
      }
      case If(e1,e2,e3) => If(step(e1), e2, e3)
      case Decl(Const, x, e1, e2) if(isRedex(Const, e1)) => Decl(Const, x, step(e1), e2)
      case Call(e1, args) => Call(step(e1), args)
      //SearchGetField
      case GetField(e1, f) => e1 match {
        //DoGetField (Definition of object value: it's a value if en is a value for every (f,en) pair, en is a value)
        //Everything is a value so get corresponding value
        case Obj(fields) => if (fields.foldLeft(true) {case (acc, (str, expr)) => acc && isValue(expr) } == true) {
          fields(f) //get the corresponding value
        } //else if not expr is a value then step on the expressions that are not values to reduce them
        else {
        val newfields = fields mapValues { (en) => if(isValue(en)) en else step(en) }
          GetField(Obj(newfields), f) //return the same GetField Node with the "stepped on" object
        }
        case _ => throw StuckError(e1)
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