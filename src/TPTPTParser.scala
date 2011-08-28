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

object TPTPTParser {

  import scala.util.matching.Regex
  import scala.util.parsing.combinator._
  import java.io.FileReader

  import Term._
  import Predefined._
  import Type._ 
  import Signature._
  import Formula._
  import Misc._

  /**
   * A parser for TPTP, both FOF and TFF
   */

  class TPTPTParser extends JavaTokenParsers {

    // Mapping of variables to types - needed, as quantified formuals are entered,
    // and the varTypes map keeps track of all governing (quantified) variables
    var varTypes = List[TypedVar]()
    // Because I did not find a way to pass around signatures as arguments 
    // in parsing, varTypes is built up and restored explictly in a stack
    var varTypesStack = List[List[TypedVar]]() 

    var haveConjecture = false

    /**
     * The grammar rules
     */
    def TPTP_input: Parser[List[List[Formula]]] = rep(annotated_formula | comment | include)

    def annotated_formula = 
      // TPTP_input requires a list, because include abobe returns a list
      ( fof_annotated_logic_formula ^^ { List(_) } ) |
      ( tff_annotated_type_formula ^^ { _ => List() } ) |
      ( tff_annotated_logic_formula ^^ { List(_) } ) 
    // cnf_annotated


    def fof_annotated_logic_formula = "fof" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ 
                        atomic_word ~ "," ~ fof_logic_formula ~ ")" <~ "." ^^ {
      case "fof" ~ "(" ~ name ~ "," ~ role ~ "," ~ f ~ ")" => 
	role match {
	  case "conjecture" => {
	    haveConjecture = true
	    Neg(f)
	  }
	  // "type" just returns TrueAtom - deal with that above
	  // case "type" => xxx
	  case _ => f // Assume f sits on the premise side
	}
    } 

    /**
     * TFF types
     */

    // In fact, non-null annotatations are currently not accepted
    // Slightly rewritten version of the BNF rule in the TPTP report, to discrimate
    // between type and non-type very early, thus helping the parser.
    def tff_annotated_type_formula = "tff" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ "type" ~ "," ~
                        tff_typed_atom ~ ")" <~ "." ^^ { 
      // It's there just for its side effect
      _ => ()
    }

    def tff_annotated_logic_formula = "tff" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ 
                        formula_role_other_than_type ~ "," ~ tff_logic_formula ~ ")" <~ "." ^^ {
      case "tff" ~ "(" ~ name ~ "," ~ role ~ "," ~ f ~ ")" => 
	role match {
	  case "conjecture" => {
	    haveConjecture = true
	    Neg(f)
	  }
	  case _ => f // Assume f sits on the premise side
	}
    } 

    def formula_role_other_than_type = commit(
      // "type" | 
      "axiom" | "hypothesis" | "definition" | "assumption" | "lemma" | "theorem" | 
      "conjecture" | "negated_conjecture" | "unknown" | atomic_word )




    // tff_typed_atom can appear only at toplevel
    def tff_typed_atom:Parser[Unit] =
                              ( ( tff_untyped_atom ~ ":" ~ tff_top_level_type ) ^^ { 
				    // could declare a new type or a symbol of an existing type
                                    case typeName ~ ":" ~ Rank((Nil, TType)) => { 
				      // println("declare type " + Type(typeName))
				      Sigma += Type(typeName)
				      // println("declared")
				      // return a dummy
				      // TrueAtom
				    }
                                    case symbolName ~ ":" ~ rank => {
				      // println("declare rank " + (symbolName -> rank))
				      if (rank.argsTypes contains OType)
					throw new SyntaxError("Error: type declaration for " + 
						symbolName + ": " + rank + ": argument type cannot be $oType")
				      // todo: generalize: can we do something sensible
				      // if all argtypes are foreground types?
				      // eg "car" would fall under this scheme.
				      if (rank.argsTypes.isEmpty && 
					  // Prop variables are better handled
					  // by the foreground
					  rank.resType != OType &&
					  (Sigma.BGTypes contains rank.resType) &&
					  Flags.paramsOpSet.value == "BG")
					// only in this case we have a BG operator
					Sigma = Sigma addBG (symbolName -> rank)
				      else
					Sigma += (symbolName -> rank)
				      // return a dummy
				      // println("declared")
				      // TrueAtom
				    }
				  } ) |
                              ( "(" ~> tff_typed_atom <~ ")" )
    def tff_untyped_atom =    atomic_word

    // This results in a Rank in our terminology
    def tff_top_level_type:Parser[Rank] =
			        tff_mapping_type |
				( tff_atomic_type  ^^ { (typ:Type) => Rank0(TypeExistsChecked(typ)) } )

    def tff_mapping_type:Parser[Rank] =
                              ( ( tff_unitary_type ~ ">" ~ tff_atomic_type ) ^^ {
				    case argsTypes ~ ">" ~ resType => 
				      Rank((argsTypes map { TypeExistsChecked(_) }), 
					   TypeExistsChecked(resType))
				  } ) |
                              ( "(" ~> tff_mapping_type <~ ")" )
    def tff_unitary_type =    ( tff_atomic_type ^^ { List(_) } ) | 
                              ( "(" ~> tff_xprod_type <~ ")" )
    def tff_xprod_type:Parser[List[Type]] =
                              ( tff_atomic_type ~ "*" ~  rep1sep(tff_atomic_type, "*") ^^ {
				  case t1 ~ "*" ~ tail => t1::tail
				  } ) |
                              ( "(" ~> tff_xprod_type <~ ")" )

    /**
     * TFF formulas
     */

    def tff_logic_formula =   tff_binary_formula | tff_unitary_formula
    def tff_binary_formula =  tff_binary_nonassoc | tff_binary_assoc
    def tff_binary_nonassoc = tff_unitary_formula ~ 
			      binary_nonassoc_connective ~ 
			      tff_unitary_formula ^^ {
				case f1 ~ op ~ f2 => op(f1,f2)
			      }
    def tff_binary_assoc =  tff_or_formula | tff_and_formula
    def tff_or_formula =
      tff_unitary_formula ~ "|" ~ rep1sep(tff_unitary_formula, "|") ^^ {
				  case f1 ~ "|" ~ tail => {
				      f1::tail reduceLeft { Or(_, _) }
				  }
			      }
    def tff_and_formula =     
      tff_unitary_formula ~ "&" ~ rep1sep(tff_unitary_formula, "&") ^^ {
				  case f1 ~ "&" ~ tail => {
				      f1::tail reduceLeft { And(_, _) }
				  }
			      }
    def tff_unitary_formula:Parser[Formula] = 
                              tff_quantified_formula | 
			      tff_unary_formula |
                              atom |
			       "(" ~> tff_logic_formula <~ ")"
    def tff_unary_formula = "~" ~> tff_unitary_formula ^^ { Neg(_) }
    def tff_quantified_formula:Parser[Formula] = 
                    (((forallSign ^^ { _ => { Forall(_,_) } } ) |
		      ("?" ^^ { _ => { Exists(_,_) }})) ~ 
		     "[" ~ tff_varlist ~ "]" ^^ { 
		                case q ~ "[" ~ vl ~ "]" => { 
				  // remember current varTypes for later restoration
				  varTypesStack ::= varTypes
				  varTypes ++= vl
				  // Return the partially instantiated Quantifier-Formula
				  (f:Formula) => q(vl,f)
				} 
		     }) ~ ":" ~ tff_unitary_formula ^^ {
		      // Put together the two parts, quantification and formula
		       case quantTemplate ~ ":" ~ f => {
			 // restore varTypes as it was before
			 varTypes = varTypesStack.head
			 varTypesStack = varTypesStack.tail
			 quantTemplate(f)
		       } 
		     }


    // Variable list
    def tff_varlist: Parser[List[TypedVar]] =  rep1sep(tff_var, ",")

    def tff_var: Parser[TypedVar] = 
      ( variable ~ ":" ~ tff_atomic_type ^^ { 
	case x ~ ":" ~ typ => (x,TypeExistsChecked(typ)) 
      } ) |
      ( variable <~ guard(not(":")) ^^ { 
	// default type of variables (in quantifications) is IType
	x => (x,IType) 
      } )

    def tff_atomic_type = 
      // user-defined type
      defined_type |
      ( atomic_word ^^ { Type(_) } ) 
    // predefined type

    def defined_type: Parser[Type] = 
      (("$oType" | "$o") ^^ { _ => OType }) |
      (("$iType" | ("$i" <~ guard(not("nt")))) ^^ { _ => IType }) |
      ("$tType" ^^ { _ => TType }) |
      ("$int" ^^ { _ => IntType })
     // $real | $rat | $int 

    /*
     * FOF formulas
     */


    def fof_logic_formula =   fof_binary_formula | fof_unitary_formula
    def fof_binary_formula =  fof_binary_nonassoc | fof_binary_assoc
    def fof_binary_nonassoc = fof_unitary_formula ~ 
			      binary_nonassoc_connective ~ 
			      fof_unitary_formula ^^ {
				case f1 ~ op ~ f2 => op(f1,f2)
			      }
    def fof_binary_assoc =  fof_or_formula | fof_and_formula
    def fof_or_formula =
      fof_unitary_formula ~ "|" ~ rep1sep(fof_unitary_formula, "|") ^^ {
				  case f1 ~ "|" ~ tail => {
				      f1::tail reduceLeft { Or(_, _) }
				  }
			      }
    def fof_and_formula =     
      fof_unitary_formula ~ "&" ~ rep1sep(fof_unitary_formula, "&") ^^ {
				  case f1 ~ "&" ~ tail => {
				      f1::tail reduceLeft { And(_, _) }
				  }
			      }
    def fof_unitary_formula:Parser[Formula] = 
                              fof_quantified_formula | 
			      fof_unary_formula |
                              atom |
			       "(" ~> fof_logic_formula <~ ")"
    def fof_unary_formula = "~" ~> fof_unitary_formula ^^ { Neg(_) }
    def fof_quantified_formula:Parser[Formula] = 
                    (((forallSign ^^ { _ => { Forall(_,_) } } ) |
		      ("?" ^^ { _ => { Exists(_,_) }})) ~ 
		     "[" ~ fof_varlist ~ "]" ^^ { 
		                case q ~ "[" ~ vl ~ "]" => { 
				  // remember current varTypes for later restoration
				  varTypesStack ::= varTypes
				  varTypes ++= vl
				  // Return the partially instantiated Quantifier-Formula
				  (f:Formula) => q(vl,f)
				} 
		     }) ~ ":" ~ fof_unitary_formula ^^ {
		      // Put together the two parts, quantification and formula
		       case quantTemplate ~ ":" ~ f => {
			 // restore varTypes as it was before
			 varTypes = varTypesStack.head
			 varTypesStack = varTypesStack.tail
			 quantTemplate(f)
		       } 
		     }


    // Variable list
    def fof_varlist: Parser[List[TypedVar]] = 
      rep1sep(variable, ",") ^^ { _ map { (_,IType) } } // looks cryptic?

 /**
  * Definitions common to TFF and FOF
  */

    def binary_nonassoc_connective = 
			      ( "=>" ^^ { _ => Implies(_,_) } ) |
			      ( "<=" <~ guard(not(">")) ^^ { _ => Implied(_,_) } ) |
			      ( "<=>" ^^ { _ => Iff(_,_) } ) |
			      ( "<~>" ^^ { _ => IffNot(_,_) } ) 

    // Atom
    // Difficulty is determining the type. If fun(args...) has been read 
    // it is possible that fun(args...) is an atom or the lhs of an equation.
    // Determining the type hence nees to be deferred until "=" (or "!=") is 
    // seen (or not). Once that is clear, the signature is extended 
    // appropriately. It can only be done this late because otherwise the signature
    // might be extended unappropriately, and backtracking (in the parser)
    // cannot undo that.

    def atom =
      ( "$true" ^^ { _ => TrueAtom }) |
      ( "$false" ^^ { _ => FalseAtom }) |
      // eqn with lhs a variable
      ( variable ~ equalsSign ~ term ^^ { 
	  case x ~ _ ~ t => CheckedEquation(x, t)
        } ) |
      ( variable ~ "!=" ~ term ^^ { 
	  case x ~ _ ~ t => Neg(CheckedEquation(x, t))
        } ) |
      ( bg_constant ~ equalsSign ~ term ^^ { 
	  case c ~ _ ~ t => CheckedEquation(c, t)
        } ) |
      ( bg_constant ~ "!=" ~ term ^^ { 
	  case c ~ _ ~ t => Neg(CheckedEquation(c, t))
        } ) |
    // functor with or without arguments
    (( ( functor ~ "(" ~ termlist ~ ")" ^^ { 
 	       case functor ~ "(" ~ termlist ~ ")" => (functor, termlist) } ) |
       ( functor ~ guard(not("(")) ^^ { 
	       case functor ~ _ => (functor, List()) } ) ) ~
     // Up to here the above could be an atom or the lhs of an equation.
     // The following three cases all return a template for a (dis)equation or an atom
     ( ( equalsSign ~ term ^^ { 
           case _ ~ t =>
	     (functor:String, args:List[Term]) => { 
	       if (!(Sigma.ranks contains functor))
		 Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       CheckedEquation(CheckedFunTerm(functor, args), t)
	     } 
         } ) |
       ( "!=" ~ term ^^ { 
           case _ ~ t =>
	     (functor:String, args:List[Term]) => { 
	       if (!(Sigma.ranks contains functor))
		 Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       Neg(CheckedEquation(CheckedFunTerm(functor, args), t))
	     } 
         } ) |
       ( guard(not(equalsSign | "!=")) ^^ { 
           case _ =>
	     (functor:String, args:List[Term]) => { 
	       if (!(Sigma.ranks contains functor))
		 Sigma += (functor -> Rank((args map { _ => IType }) -> OType))
	       CheckedAtom(functor, args)
	     } 
         } ) ) ^^ 
     // Put together the results of the parsing obtained so far
     { case (functor,args) ~ fTemplate => fTemplate(functor,args) } )

    // Terms
    // Parsing (of atoms) is such that whenever a term is to be parsed
    // it is clear it must be a term (no backtracking), hence as soon
    // as a term is found the signature can be extended.
    def term: Parser[Term] =  nonvar_term | variable 
    def nonvar_term: Parser[Term] = funterm | constant | bg_constant
    def variable: Parser[Var] = regex(new Regex("[A-Z][a-zA-Z0-9_]*")) ^^ { 
      name => Var(name) }
    def funterm: Parser[FunTerm] = functor ~ "(" ~ termlist ~ ")" ^^ {
      case functor ~ "(" ~ termlist ~ ")" => { 
	if (!(Sigma.ranks contains functor))
	  Sigma += (functor -> Rank((termlist map { _ => IType }) -> IType))
	// todo: check well-sortedness of arguments
	CheckedFunTerm(functor, termlist) 
      }
    }

    def termlist = rep1sep(term, ",")

    // Foreground constant or parameter
    def constant: Parser[FunTerm] = 
      // a constant cannot be followed by a parenthesis, would see a FunTerm instead
      // Use atomic_word instead of functor?
      guard(functor ~ not("(")) ~>
      functor ^^ { functor => 
	if (!(Sigma.ranks contains functor)) 
	  Sigma += (functor -> Rank0(IType))
	CheckedFunTerm(functor, List())
    }

    // Background literal constant
    def bg_constant = 
      regex(new Regex(Sigma.isBGElemRegEx)) ^^ { 
	s => {
	  // There is no default type for a BG constant - it must always be of the background type
	  // todo: get rid of declaring BGLitConsts in the first place
	  Sigma = Sigma addBG (s -> Rank0(Sigma.BGType))
	  BGLitConst(s.toInt)
	}
      }
    
    // lexical: don't confuse = with => (the lexer is greedy)
    def equalsSign = "=" <~ guard(not(">"))
    
    def forallSign = "!" <~ guard(not("="))

    def functor = keyword | atomic_word

    def atomic_word: Parser[String] = 
      ( regex("""'.*'""".r) ^^ { _.drop(1).dropRight(1) } ) |
      regex("[a-z][a-zA-Z0-9_]*".r)

    def keyword = regex("[$][a-z]+".r)

/* Could be specific (but why?)
    def keyword = 
      "$uminus"     |
      "$sum"        |
      "$difference" |
      "$product"    |
      ("$less" <~ guard(not("eq")))   |
      "$lesseq"     |
      ("$greater" <~ guard(not("eq")))  |
      "$greatereq"  |
      "$evaleq"     
*/

    // Parsing of comments is not optimal as they may not appear
    // inside formulas - essentially they are an atom
    def comment: Parser[List[Formula]] =
    """%.*""".r ^^ (x => List(Comment(x)))

    def include: Parser[List[Formula]] = 
      "include" ~> "(" ~> atomic_word <~ ")" <~ "." ^^ {
	case fileName  => {
	  val TPTPHome = System.getenv("TPTP")
	  parseTPTPTFile((if (TPTPHome == null) "" else TPTPHome + "/") +
			 fileName)._1 // ignore haveConjecture
	} 
      }

    /**
     * CheckedXX: creates an XX, type-checked against sig and varTypes
     */
    def CheckedEquation(s: Term, t: Term) = {
      val typ = Sigma.typeOf(s, varTypes)
      if (typ != OType && typ == Sigma.typeOf(t, varTypes)) 
	Equation(s, t)
      else
	throw new SyntaxError("Error: ill-sorted (dis)equation: between " + s + " and " + t)
    }

    def CheckedAtom(pred: String, args: List[Term]) = 
      // Assume that pred has been entered into sig already
      if (Sigma(pred).argsTypes == Sigma.typesOf(args, varTypes))
	Atom(pred, args)
      else
	throw new SyntaxError("Error: ill-sorted atom: " + Atom(pred, args))

    def CheckedFunTerm(fun: String, args: List[Term]) = 
      // Assume that fun has been entered into sig already
      if (args.isEmpty) {
	// A constant. See if we have a foreground constant or parameter
	if (Sigma.BGRanks contains fun)
	  // We have a parameter
	  Param(fun)
	else
	  // Foreground Constant
          Const(fun) 
      } else if (Sigma(fun).argsTypes == Sigma.typesOf(args, varTypes)) 
	// Type Checking OK 
	FunTerm(fun, args)
      else
	throw new SyntaxError("Error: ill-sorted term: " + FunTerm(fun, args))

    def TypeExistsChecked(typ: Type) = 
      if (Sigma.types contains typ)
	  typ
      else
	throw new SyntaxError("Error: type has not been declared: " + typ)
  }

  def parseTPTPTFile(fileName: String) = {
    val reader = new FileReader(fileName)
    val TPTPTparser = new TPTPTParser
    val tffs = TPTPTparser.parseAll[List[List[Formula]]](TPTPTparser.TPTP_input, reader).get.flatten.filter(!_.isComment)
    (tffs, TPTPTparser.haveConjecture)
  }

}

