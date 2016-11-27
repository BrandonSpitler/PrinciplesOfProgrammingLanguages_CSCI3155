package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3
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
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(n) => if(n==true) 1 else 0
      case S("") => 0;
      case S(n) => try n.toDouble catch{case _:Throwable => Double.NaN} //todo
      case Undefined => Double.NaN
      case Function(_, _, _) => Double.NaN
      case _ => throw new UnsupportedOperationException
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if(n==0 || n==Double.NaN){ false } else true
      case null => false
      case S("") => false
      case S(_) => true
      case Undefined =>false
      case Function(_, _, _) => true
      case _ => throw new UnsupportedOperationException

    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {

      case S(s) => s
      case Undefined => "undefined"
      case B(b) => if (b==true) "true" else "false"
      case N(n) =>
        if(n.isWhole()) {
          n.toInt.toString
        }else{
          n.toString
        }
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case _ => throw new UnsupportedOperationException
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
      case (S(_),S(_)) => bop match {
        case Lt => if (toStr(v1).charAt(0) < toStr(v2).charAt(0)) true else false
        case Le => if (toStr(v1).charAt(0) <= toStr(v2).charAt(0)) true else false
        case Gt => if (toStr(v1).charAt(0) > toStr(v2).charAt(0)) true else false
        case Ge => if (toStr(v1).charAt(0) >= toStr(v2).charAt(0)) true else false
      }
      case (_,_) => bop match {
        case Lt => if (toNumber(v1) < toNumber(v2)) true else false
        case Le => if (toNumber(v1) <= toNumber(v2)) true else false
        case Gt => if (toNumber(v1) > toNumber(v2)) true else false
        case Ge => if (toNumber(v1) >= toNumber(v2)) true else false
      } // delete this line when done
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    val t = B(true)
    val f = B(false)
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e


      case _ if(isValue(e)) => e
      case Var(x) => try lookup(env,x)
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case Unary(Neg,e1) => N(-toNumber(eval(env,e1)))
      case Unary(Not,e1) => B(!toBoolean(eval(env,e1)))

      case Binary(Seq,e1,e2) => {
        val ee1 :Expr=eval(env,e1)
        val ee2 :Expr=eval(env,e2)
        ee2
      }

      case Binary(Plus,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {
          case (v1,S(e2)) => S(toStr(v1)+e2)
          case (S(e1),v2) => S(e1+toStr(v2))
          case (v1,v2) => N(toNumber(v1)+toNumber(v2))
        }
      case Binary(Minus,e1 ,e2) =>
        (eval(env,e1),eval(env,e2))  match{
          case (v1,v2) => N(toNumber(v1)-toNumber(v2))
        }
      case Binary(Times,e1,e2) =>
        (eval(env,e1),eval(env,e2)) match {
          case (v1,v2) => N(toNumber(v1)*toNumber(v2))
        }

      case Binary(Div,e1,e2) => //todo apply string test cases as well as devide by zero
        (eval(env, e1),eval(env,e2)) match {
          case (v1,v2) => N(toNumber(v1)/toNumber(v2))
        }
      case Binary(bop @(Le|Ge|Lt|Gt),e1,e2) => B(inequalityVal(bop,eval(env,e1),eval(env,e2)))


      case Binary(And,e1,e2) => {
        eval(env,e1) match {
          case N(0) => N(0)//todo look at this it seems like it should be the next one
          case S("") => S("")
          case B(false) => f
          case v1 =>
            if(toBoolean(v1)) {
              eval(env, e2) match {
                //tod change this so that it calls eval
                //case B(v2) =>
                case v2 => v2
              }
            }else{
              v1
            }
          //case _ => ???
        }
      }

      case Binary(Or,e1,e2) => {

        (eval(env, e1), eval(env, e2)) match {
          case (S(""), v1) => v1
          case (B(false), v1) => v1
          case (N(0),v1) => v1
          case (v1,v2) => v1
        }
      }






      case If(e1,e2,e3) => if(toBoolean(eval(env,e1))) eval(env,e2) else{ eval(env,e3)}

      case Binary(Eq,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {
          case (Function(_,_,_),v2) => throw new DynamicTypeError(e)
          case (v1,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (S(s1),S(s2)) => if(s1==s2) t else f;
          case (N(n1),N(n2)) => if(n1==n2) t else f
          case (B(b1),B(b2)) => if(b1==b2) t else f;
          case (v1,v2) => f//two things that arent equal
        }


      case Binary(Ne,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {
          case (Function(_,_,_),v2) => throw new DynamicTypeError(e)
          case (v1,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (S(s1),S(s2)) => if(s1==s2) f else t;
          case (N(n1),N(n2)) => if(n1==n2) f else t
          case (B(b1),B(b2)) => if(b1==b2) f else t;
          case (v1,v2) => t;
        }




      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case ConstDecl(x,e1,e2) => eval(extend(env,x,eval(env,e1)),e2)

      case Call(e1, e2) => (eval(env,e1),eval(env,e2)) match {
        case (Function(None,x,ep),ee2) => eval(    extend(env,x,ee2),    ep)
        case (Function(Some(x1),x2,ep),ee2) =>eval(    extend(   extend(env,x2,ee2)   ,x1, Function(Some(x1),x2,ep)),    ep);

        case _ => throw new DynamicTypeError(e) //unknown if correct did give any points
        case (_,_) => throw new DynamicTypeError(e) //unknown if correct did give any points
      }

      case _ => throw new DynamicTypeError(e)
      case _ => ??? // delete this line when done
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case Some(ep) => loop(ep,n + 1)
      case None => e
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))
      case Var(y) => if (x == y) v else Var(y)
      case Function(None, y, e1) => if (x == y) e else Function(None, y, substitute(e1, v, x))
      case Function(Some(y1), y2, e1) => if (x == y1 || x == y2) e else Function(Some(y1), y2, substitute(e1, v, x))
      case ConstDecl(y, e1, e2) => {

        ConstDecl(y,substitute(e1,v,x),if(y==x) { e2
        }else{
          substitute(e2,v,x)
        })
      }
      case _ => throw new UnsupportedOperationException
    }
  }

  def step(e: Expr): Expr = {
    e match {


      /* Base Cases: Do Rules */
      /*Do rules require values*/
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg,v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not,v1) if isValue(v1) => B(!toBoolean(v1))
      case Binary(Seq,e1,e2) if isValue(e1) => e2
      case Binary(Plus,v1,v2) if isValue(v1) && isValue(v2) => (v1,v2) match {
        case (S(s1),e2) => S(s1 + toStr(e2))
        case (e1,S(s2)) => S(toStr(e1) + s2)
        case (_,_) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(bop @ (Minus|Times|Div),v1,v2) if (isValue(v1) && isValue(v2)) => bop match {
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div => N(toNumber(v1) / toNumber(v2))
      }
      case Binary(bop @ (Lt|Le|Gt|Ge),v1,v2) if (isValue(v1) && isValue(v2)) => B(inequalityVal(bop,v1,v2))
      case Binary(bop @ (Eq|Ne),v1,v2) if isValue(v1) &&isValue(v2) =>
      (v1,v2)match {
        case (Function(fb,x,fbody),exp2) =>throw new DynamicTypeError(e)
        case (exp1,Function(fb,x,fbody)) =>throw new DynamicTypeError(e)

        case (vv1,vv2) => {
          bop match{
            case Eq => if (toNumber(vv1) == toNumber(vv2)) B(true) else B(false)
            case Ne => if (toNumber(vv1) != toNumber(vv2)) B(true) else B(false)
          }
        }
      }
      //Need Binary(Seq,v1,e2)

      case Binary(And,v1,e2) if isValue(v1) => {
        if (!toBoolean(v1)) v1
        else  e2

      }
      case Binary(Or,v1,e2) if isValue(v1) => {
        if (toBoolean(v1)) v1
        else e2
      }
      case If(v1,e2,e3) if isValue(v1) => {
        if (toBoolean(v1)) e2
        else e3
      }
      case ConstDecl(x,v1,e2) if isValue(v1) => substitute(e2,v1,x)

      case Call(v1,v2) if (isValue(v1) && isValue(v2)) => //unknown if correct did not give any extra points
        v1 match{
          case f1 @ Function(Some(f),x,fbody) => substitute(     substitute(fbody,f1,f)   ,v2,x)
          case Function(None, x,fbody) => substitute(fbody,v2,x)
          case _ => throw new DynamicTypeError(e)
        }



      // ****** Your cases here



      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      case Unary(uop,e1) => Unary(uop,step(e1))
      case Binary(bop,e1,e2) => if (isValue(e1)) Binary(bop,e1,step(e2)) else Binary(bop,step(e1),e2)
      case Binary(bop @ (Plus|Minus|Times|Div|Lt|Le|Gt|Ge),e1,e2) => if (isValue(e1)) Binary(bop,e1,step(e2)) else Binary(bop,step(e1),e2)
      case Binary(bop @ (Eq|Ne),e1,e2) => if (isValue(e1)) Binary(bop,e1,step(e2)) else Binary(bop,step(e1),e2)
      case If(e1,e2,e3) => If(step(e1),e2,e3)
      case ConstDecl(x,e1,e2) => ConstDecl(x,step(e1),e2)
      case Call(e1, e2)  => e1 match {
        case Function(_, _, _) =>  Call(e1, step(e2))
        case s1 => Call(step(s1),e2);
        case _ => throw new DynamicTypeError(e)
      }
        // ****** Your cases here


      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
