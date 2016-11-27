/*
 * CSCI 3155: Lab 2 Worksheet
 *
 * This worksheet demonstrates how you could experiment
 * interactively with your implementations in Lab2.scala.
 */

// Imports the parse function from jsy.lab1.Parser
import jsy.lab2.Parser.parse

// Imports the ast nodes
import jsy.lab2.ast._

// Imports all of the functions form jsy.student.Lab2 (your implementations in Lab2.scala)
import jsy.student.Lab2._

// Call the JavaScripty parser (from the provided library) on a string
val negFourAST = parse("-4")

// Evaluate that JavaScripty expression.
//eval(negFourAST)

// For convenience, we also have an eval function that takes a string,
// which calls the parser and then delegates to your eval function.


toNumber(S("99"))


eval(Binary(Plus,S("hello"),N(3)))
eval(Binary(Minus,S("9llo"),N(3)))
eval(Binary(And,S("3"),N(3)))


eval(Binary(Times,S("aa"),N(11)))


eval(Unary(Neg,N(Double.NaN)))
eval(Unary(Neg,Undefined))


eval(Binary(Div,N(9),S("")))

eval(Binary(Plus,N(99),N(-98)))


toNumber(S(""))

