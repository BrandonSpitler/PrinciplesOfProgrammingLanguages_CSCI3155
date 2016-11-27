package jsy.student

import java.lang.IllegalArgumentException

import jsy.lab1._

object Lab1 extends jsy.util.JsyApplication with jsy.lab1.Lab1Like {
  import jsy.lab1.Parser
  import jsy.lab1.ast._

  /*
   * CSCI 3155: Lab 1
   * <Your Name>
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

  def abs(n: Double): Double = if(n < 0) n*(-1) else n//{ if(n <0) n-n*2 else n }

  def xor(a: Boolean, b: Boolean): Boolean = {a^b} /*{
    if (a==false && b == true) true
    else if(a==true && b==false) true
    else if(a==false && b==false) false
    else false
  }*///{a ^ b}

  def repeat(s: String, n: Int): String = {
    require(n>=0)
    if (n==0) ""
    else if(n>1) s + repeat(s, n-1)
    else s
  }/*{
    if(n > -1) {
      if(n!=0) {
        var x: String = s;
        var a: Int = 1;
        while (a < n) {
          x = x.concat(s);
          a = a + 1;

        }
        x;
      }else{
        ""
      }
    }else throw new IllegalArgumentException
  }*/

  def sqrtStep(c: Double, xn: Double): Double = {
    xn-(xn*xn-c)/(2*xn);
  }

  def sqrtN(c: Double, x0: Double, n: Int): Double = {
    require(n>=0)
    if(n==0){
      x0
    }else {
      var i: Int = 0;
      var xn: Double = x0;
      while (i < n) {
        xn = sqrtStep(c, xn);
        i += 1;
      }
      xn;
    }
  }
//https://www.math.upenn.edu/~kazdan/202F09/sqrt.pdf
  def sqrtErr(c: Double, x0: Double, epsilon: Double): Double = {
     require(epsilon>0)
      if(abs(x0*x0-c) < epsilon){ //if the value squared minus the value is less the epsilon the difference is less the ther error
        x0;
      }else {
        sqrtErr(c, sqrtStep(c, x0), epsilon)
      }
  }

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
      case Node(l, d, r) => {
        if(check(l,min,d)==false){
          return false;
        }else if(check(r,d,max)==false) {

          return false;
        }else if(d>max || d<min){
          return false;


        }else{
          true;
        }
      }
    }
    check(t, Int.MinValue, Int.MaxValue)
  }

//  def insert(t: SearchTree, n: Int): SearchTree = ???

  def insert (t: SearchTree, i :Int): SearchTree =

    t match{
      case Empty => new Node(Empty,i,Empty)
      case Node(l,d,r) =>
        //val t: SearchTree= Node(l,10,Node(Empty,10,Empty))

        if(d <= i){ new Node(l,d,insert(r,i))}
        else { new Node(insert(l,i),d,r)}
    }

  def deleteMin(t: SearchTree): (SearchTree, Int) = {
    require(t != Empty)
    (t: @unchecked) match {
      case Node(Empty, d, r) => (r, d)
      case Node(l, d, r) =>
        val (l1, m) = deleteMin(l)
        (Node(l1,d,r),m)
    }
  }


  def delete(t: SearchTree, n: Int): SearchTree =

    t match{
      case Empty => t

      case Node(Empty,d,Empty) =>
        if(n==d){
          Empty
        }
        else{
          t
        }
      case Node(l,d,r) =>
        if(n<d){
          Node(delete(l,n),d,r)
        }else if(n>d){
          Node(l,d,delete(r,n))
        }else{
          val (l1,m) = deleteMin(r);//find the lowest node on the right side and delete it save it in val l1 and m
          //Node(l,m,r)//give node the proberties of the val node int with the current nodes right and left tails doesnt work bc it doest give the node the new updted right tail
          Node(l,m,l1)//gives the node the new update right tail
        }
    }

  /* JavaScripty */
//

  def eval(e: Expr): Double =
    e match {
    case N(n) => n

    case Binary(Plus,e1,e2) => eval(e1) + eval(e2);
    case Binary(Minus,e1,e2) => eval(e1) - eval(e2);
    case Binary(Times,e1,e2) => eval(e1) * eval(e2);
    case Binary(Div,e1,e2) => eval(e1) / eval(e2);
    case Unary(Neg,e1) => -1*eval(e1) // I belive this is the one of the cases we are missing
    case _ => ???
  }

 // Interface to run your interpreter from a string.  This is convenient
 // for unit testing.
 def eval(s: String): Double = eval(Parser.parse(s))



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
