/* *********************************************************************
 * This file is part of the MELIA theorem prover
 *
 * Copyright (c) NICTA/Peter Baumgartner <Peter.Baumgartner@nicta.com.au>
 *
 * MELIA is free software: you can redistribute it
 * and/or modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of
 * the License, or (at your option) any later version.
 *
 * MELIA is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MELIA.  If not, see  <http://www.gnu.org/licenses/>. 
 * ********************************************************************* */

/*
 * A parser for tme-files
 * The syntax is basically Prolog Syntax, but facts and heads of rules can be disjunctions
 * of atoms.
 * Example clauses:
 * p(X,a).                              (fact)
 * p(X,a) ; p(f(a),Y).                  (disjunctive fact)
 * p(X,a) :- q(X), r(a).                (rule)
 * p(X,a) ; p(f(a),Y) :- q(X), r(a).    (disjunctive rule)
 * false :- q(X), r(a).                 (head "false" is OK, for  purely negative clauses)
 *
 * atoms can also be equations, like f(x)=x
 *
 * * Comments start with a '%'
 * Caveat: all comments must be outside clauses.
  * */ 


object TMEParser {

  import scala.util.parsing.combinator._
  import java.io.FileReader
  import Clauses._
  import Type._ 
  import Signature._

  import scala.util.matching.Regex
  import java.io.FileReader
  import Term._
  import Eqn._
  import Literal._
  import Predefined._
  import Misc._


  class TMEParser extends JavaTokenParsers {

    // No need to check terms - the only unsorted case is if a predicate appears in 
    // a term position, or vice versa, and these cases are checked because the symbol
    // would be inserted with different types, $i and $o

    def CheckedEquation(s: Term, t: Term) = {
      // def illSorted() {
      // 	throw new SyntaxError("TME Parser: ill-sorted equation: " + s + " = " + t)
      // }

      val typ = (s, t) match {
	case (_:Var, _:Var) => IType
	case (_:Var, FunTerm(fun,_)) => 
	  if (Sigma(fun).resType == IType) 
	    IType
	  else
	    throw new SyntaxError("TME Parser: ill-sorted equation: " + s + " = " + t)
	case (FunTerm(fun,_), _:Var) => 
	  if (Sigma(fun).resType == IType) 
	    IType
	  else
	    throw new SyntaxError("TME Parser: ill-sorted equation: " + s + " = " + t)
	case (FunTerm(fun1,_), FunTerm(fun2,_)) => 
	  // could be pType
	  if (Sigma(fun1).resType == Sigma(fun1).resType)
	    Sigma(fun1).resType
	  else
	    throw new SyntaxError("TME Parser: ill-sorted equation: " + s + " = " + t)
      }
      Eqn(s, t, typ)
    }

    // This is used in the parser only, so that we can write 
    // 'false' in the head.
    val FF = Const("$false") 
    private object FalseEqn extends Eqn(FF,TT,OType)

    def clauses: Parser[List[Clause]] = rep(clause | comment) ^^ { 
      x => x.filter(_.isInstanceOf[Clause]).asInstanceOf[List[Clause]] }
 
    def clause: Parser[Clause] = ( rule | fact ) <~ "."

    def fact: Parser[Clause] = rep1sep(atom, ";") ^^ { atoms => 
      Clause(OClause(atoms.filter(_ != FalseEqn).map(Lit(true,_))), "input")
   }

    def rule: Parser[Clause] = head ~ ":-" ~ body ^^ { 
      case head ~ ":-" ~ body => 
	if (body contains FalseEqn)
	  TrueClause
	else {
	  val posLits = head.filter(_ != FalseEqn).map(Lit(true,_))
	  val negLits = body.filter(_ != TrueEqn).map(Lit(false,_))
	  Clause(OClause(posLits ::: negLits), "input")
	}
    }

    def head: Parser[List[Eqn]] = rep1sep(atom, ";") 

    def body: Parser[List[Eqn]] = rep1sep(atom, ",")

    // only used outside for test purposes
    def literal: Parser[Lit] = "~" ~> atom ^^ { case atom => Lit(false, atom) } |
          atom ^^ { case atom => Lit(true, atom) }

    def atom = ("(" ~> fof_atom <~ ")") | fof_atom

    def fof_atom =
      ( "true" ^^ { _ => TrueEqn } ) |
      ( "false" ^^ { _ => FalseEqn } ) |
      // Variable - can only be an equation than
      ( fof_var ~ "=" ~ fof_term ^^ { 
	  case x ~ _ ~ t => CheckedEquation(x, t)
        } ) |
      // proper functional term as lhs or atom
    (( ( identif ~ "(" ~ fof_termlist ~ ")" ^^ { 
 	       case identif ~ "(" ~ fof_termlist ~ ")" => (identif, fof_termlist) } ) |
      // constant or proposiitonal variable
       ( identif ~ guard(not("(")) ^^ { 
	       case identif ~ _ => (identif, List()) } ) ) ~
     // Up to here the above could be an atom or the lhs of an equation.
     ( ( "=" ~ fof_term ^^ { 
           case _ ~ t =>
	     (identif:String, args:List[Term]) => { 
	       Sigma += (identif -> Rank((args map { _ => IType }) -> IType))
	       CheckedEquation(FunTerm(identif, args), t)
	     } 
         } ) |
       ( guard(not("=")) ^^ { 
           case _ =>
	     (identif:String, args:List[Term]) => { 
	       Sigma += (identif -> Rank((args map { _ => IType }) -> OType))
	       CheckedEquation(FunTerm(identif, args),TT)
	     } 
         } ) ) ^^ 
     // Put together the results of the parsing obtained so far
     { case (identif,args) ~ fTemplate => fTemplate(identif,args) } )

    // Terms
    def fof_term: Parser[Term] =  fof_nonvar_term | fof_var 

    def fof_nonvar_term: Parser[Term] = fof_funterm | fof_const

    def fof_var: Parser[Var] = regex(new Regex("[A-Z][a-zA-Z0-9_]*")) ^^ { 
      name => Var(name) }

    def fof_funterm: Parser[FunTerm] = identif ~ "(" ~ fof_termlist ~ ")" ^^ {
      case identif ~ "(" ~ fof_termlist ~ ")" => { 
	Sigma += (identif -> Rank((fof_termlist map { _ => IType }) -> IType))
	// todo: check well-sortedness of arguments
	FunTerm(identif, fof_termlist) 
      }
    }

    def fof_termlist = rep1sep(fof_term, ",")

    def fof_const: Parser[FunTerm] = 
      guard(identif ~ not("(")) ~
      identif ^^ { case _ ~ identif => 
	Sigma += (identif -> Rank(List() -> IType))
        Const(identif) 
    }

    // def equals = regex(new Regex("==")) // don't confuse = with =>
    def equals = "=" ~ guard(not(">")) ^^ { _ => "=" }
    // def equals = regex(new Regex("+")) // don't confuse = with =>

    def identif: Parser[String] = 
      ( regex(new Regex("""'.*'""")) ^^ { _.drop(1).dropRight(1) } ) |
      regex(new Regex("[a-z][a-zA-Z0-9_]*"))

    def comment: Parser[Eqn] = """%.*""".r ^^ { _ => TrueEqn }
    
  }

  def parseTMEFile(fileName: String) = {
    // Assumes that Sigma has been set
    val reader = new FileReader(fileName)
    val TMEparser = new TMEParser
    val clauses = TMEparser.parseAll[List[Clause]](TMEparser.clauses, reader).get
    clauses
  }


}

