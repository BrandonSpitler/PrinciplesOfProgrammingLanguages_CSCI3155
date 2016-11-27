package jsy.student

import jsy.lab2.Lab2Like

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
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
      case B(n) => if(n==true) 1 else 0
      case S("") => 0;
      case S(n) => try n.toDouble catch{case _:Throwable => Double.NaN} //todo
      case Undefined => Double.NaN
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
      /*
              n match {
                case Double.NaN => "NaN"
                case 0 => "0"
                case Double.PositiveInfinity => "Infinity"
                case Double.NegativeInfinity => "-Infinity"
                case v => v.toString
              }*/
      case _ => throw new UnsupportedOperationException
    }
  }

  def eval(env: Env, e: Expr): Expr = { //todo add evals before you evalutate anything add the connor statments and match statements to your code
  val t = B(true)
    val f = B(false)
    //val Pattern = "(^.*[a-zA-Z]+.*$)".r

    e match {
      /* Base Cases */
      case Var(x) => lookup(env,x)
      case _ if(isValue(e)) => e


      case Undefined => Undefined


      case Binary(And,e1,e2) => {


        eval(env,e1) match {
          case N(0) => N(0)//todo look at this it seems like it should be the next one
          case S("") => S("")
          case B(false) => f

          case v1 =>
            eval(env,e2) match { //tod change this so that it calls eval
              //case B(v2) =>
              case v2 => v2
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
      /*
      eval(env,e1) match {
        case N(v) => N(v)
        case v1 =>
          eval(env, e2) match {
            case N(v) => N(v)
            case v2 => if(toBoolean(v1)==false) v2 else t

            case _ => ???
          }

        case _ => ???
      }
    }*/

      case Binary(Plus,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {

          case (S(e1),S(e2))=> S(e1+e2);
          case (v1,S(e2)) => S(toStr(v1)+e2)
          case (S(e1),v2) => S(e1+toStr(v2))
          case (v1,v2) => N(toNumber(v1)+toNumber(v2))
        }


      //


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



      case If(e1,e2,e3) => if(toBoolean(eval(env,e1))==true) eval(env,e2) else{ eval(env,e3)}



      case Binary(Eq,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {
          case (S(s1),S(s2)) => if(s1==s2) t else f;
          case (N(n1),N(n2)) => if(n1==n2) t else f
          case (B(b1),B(b2)) => if(b1==b2) t else f;
          case (v1,v2) => f//two things that arent equal
        }



      //if(toNumber(eval(env,e1))==toNumber(eval(env,e2))) t else f



      case Binary(Ne,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match {
          case (S(s1),S(s2)) => if(s1==s2) f else t;
          case (N(n1),N(n2)) => if(n1==n2) f else t
          case (B(b1),B(b2)) => if(b1==b2) f else t;

          case (v1,v2) => t; //two things that arent equal

          //to things that arent equal
        }


      //if(toNumber(eval(env,e1))==toNumber(eval(env,e2))) f else t



      case Binary(Lt,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match{
          case (S(s1),S(s2)) => if(s1<s2) t else f
          /*
        case (S(""),v1) => if(toNumber(v1)>0) t else f
        case (v1,S("")) => if(toNumber(v1)<0) t else f
        case (S(s1),v1) => f;
        case (v2,S(s2)) => f;*/
          case (v1,v2) => if(toNumber(v1)<toNumber(v2)) t else f
        }



      //if(toNumber(eval(env,e1))<toNumber(eval(env,e2))) t else f



      case Binary(Le,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match{
          case (S(s1),S(s2)) => if(s1<=s2) t else f
          /*
        case (S(""),v1) => if(toNumber(v1)>=0) t else f
        case (v1,S("")) => if(toNumber(v1)<=0) t else f
        case (S(s1),v1) => f;
        case (v2,S(s2)) => f;*/
          /*case (S(s1),v2) => if(s1<=toStr(v2)) t else f
          case (v2,S(s1)) => if(s1>=toStr(v2)) t else f*/
          case (v1,v2) => if(toNumber(v1)<=toNumber(v2)) t else f
        }


      //if(toNumber(eval(env,e1))<=toNumber(eval(env,e2))) t else f



      case Binary(Ge,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match{
          case (S(s1),S(s2)) => if(s1>=s2) t else f
          /*
        case (S(s1),v2) => if(s1>=toStr(v2)) t else f
        case (v2,S(s1)) => if(s1<=toStr(v2)) t else f*/
          case (v1,v2) => if(toNumber(v1)>=toNumber(v2)) t else f
        }




      //if(toNumber(eval(env,e1))>=toNumber(eval(env,e2))) t else f



      case Binary(Gt,e1,e2) =>
        (eval(env,e1), eval(env,e2)) match{
          case (S(s1),S(s2)) => if(s1>s2) t else f
          case (S(""),v1) => if(toNumber(v1)>0) t else f
          case (v1,S("")) => if(toNumber(v1)<0) t else f
          /*case (S(s1),v1) => f;
          case (v2,S(s2)) => f;*/
          /*case (S(s1),v2) => if(s1>toStr(v2)) t else f
          case (v2,S(s1)) => if(s1<toStr(v2)) t else f*/
          case (v1,v2) => if(toNumber(v1)>toNumber(v2)) t else f
        }


      //if(toNumber(eval(env,e1))>toNumber(eval(env,e2))) t else f



      case Binary(Seq,e1,e2) => {
        val ee1 :Expr=eval(env,e1)
        val ee2 :Expr=eval(env,e2)
        return ee2
      }

      case Unary(Neg,e1) => N(-toNumber(eval(env,e1)))
      case Unary(Not,e1) => B(!toBoolean(eval(env,e1)))

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case ConstDecl(x,e1,e2) => eval(extend(env,x,eval(env,e1)),e2)
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