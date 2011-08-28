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

object Signature {

  import Predefined._
  import Misc._
  import Term._
  import Formula._
  import Type._

  /**
  * For a given set of Types, a Signature is a mapping from symbols to ranks over 
  * these types. Our Signatures are constructed from an (optional) fixed Background type and
  * ranks of the Background operatos, which can be extended (Skolem constants!)
  */
  

  // For simplicity we assume one global signature which is stored here as well.
  var Sigma = signatureEmpty

  // We allow function symbols to be equipped with FormatFn's, which
  // are functions that convert a term with that function symbol to a String
  type FormatFn = List[Term] => String
  // The most commonly used FormatFns, see Predefined.scala for usages.
  def infix(op: String) = (ts: List[Term]) => 
    // "(" + ts(0) + " " + op + " " + ts(1) + ")"
    // Allow symbols be used varyadic 
    if (ts.isEmpty) "" else if (ts.tail.isEmpty) ts.head.toString else ts.toMyString("(",op , ")")
  def prefix(op: String) = (ts: List[Term]) => op + ts(0)
  def functional(fun: String) = (ts: List[Term]) => fun + ts.toMyString("","(", ", ", ")")

  class Signature(val BGTypeOpt: Option[(Type, String)],
		  val FGTypes: Set[Type], 
		  val BGRanks: Map[String,Rank],
		  val FGRanks: Map[String,Rank],
		  val FormatFns: Map[String,FormatFn]) {


    def BGOps = BGRanks.keySet
    def FGOps = FGRanks.keySet

    def hasBGType = BGTypeOpt != None

    // Assume that BGTypeOpt != None
    def BGType = BGTypeOpt.get._1

    // def isBGType(typ: Type) = hasBGType && BGType == typ

    def isBGElemRegEx = if (hasBGType) BGTypeOpt.get._2 else "__never_see_this__"
    def BGTypes = if (hasBGType) Set(BGType) else Set[Type]()

    // val isBGElemRegExR = ("^" + isBGElemRegEx + "$").r
    // def isBGElem(s: String) = isBGElemRegExR.findFirstIn(s) != None

    def ranks = BGRanks ++ FGRanks
    def types = BGTypes ++ FGTypes


    // Add a *foreground* type
    def + (t: Type):Signature = {
      require(!(BGTypes contains t), { println("Error: Cannot extend BG types"); show() } )
      new Signature(BGTypeOpt, FGTypes + t, BGRanks, FGRanks, FormatFns)
    }

    def + (sr: (String, Rank)):Signature = { 
      val (symbol,r) = (sr._1, sr._2)
      require((!(ranks contains symbol)) || ranks(symbol) == r, 
	      { println("Error: double declaration of symbol " + symbol +
		        " with ranks " + r + " and " + ranks(symbol)); show() })
      new Signature(BGTypeOpt, FGTypes, BGRanks, FGRanks + (symbol -> r), FormatFns)
    }

    // Used to declare parameters - less common, hence the verbose name
    def addBG(srs: (String, Rank)*) = { 
      require(srs forall { sr => { val (symbol,r) = (sr._1, sr._2)
			           (!(ranks contains symbol)) || ranks(symbol) == r } },
	      { println("Error: double declaration in " + srs); show() })
      new Signature(BGTypeOpt, FGTypes, BGRanks ++ srs, FGRanks, FormatFns)
    }


    def addFormatFns(newFormatFns: (String, FormatFn)*) = {
      new Signature(BGTypeOpt, FGTypes, BGRanks, FGRanks, FormatFns ++ newFormatFns)
    }

    def getFormatFn(symbol: String) = 
      FormatFns.get(symbol) match { 
	case None => functional(symbol) // Default 
	case Some(fun) => fun
      }

    def apply(symbol: String) = {
      require(ranks contains symbol, { println("Error: no rank defined for symbol " + symbol); show() } )
      ranks(symbol)
    }

    // Get the (result) type of a given FunTerm.
    def typeOf(t: FunTerm) =  ranks(t.fun).resType
    
    // Get the (result) type of a given term t.
    // Additionally a varTypes map has to be provided in case t is a variable.
    def typeOf(t: Term, varTypes: List[TypedVar]) =
      t match { 
	case v:Var => {
	  require(varTypes.varsOf contains v,
		  { println("Error: variable " + v + " has not been declared"); show()})
	  varTypes(v)
	}
	case FunTerm(fun, _) => {
	  require(ranks contains fun, 
		  { println("Error: symbol " + fun + " has not been declared"); show()})
	  ranks(fun).resType
	}
      }

    // Lifting to lists of terms
    def typesOf(ts: List[Term], varTypes: List[TypedVar]) = ts map { typeOf(_,varTypes) }
    
    def show() {
      println("Signature with")
      println(" background types: " + BGTypes.toList.toMyString("{", ", ", "}"))
      println(" background ranks: ")
      BGRanks foreach { x => println("    " + x._1 + ": " + x._2) }
      println(" foreground types: " + FGTypes.toList.toMyString("{", ", ", "}"))
      println(" foreground ranks: ")
      FGRanks foreach { x => println("    " + x._1 + ": " + x._2) }
    }
    
  }

  object Signature {
    // Usually this is how a signature is initiaally created, then use the methods provided
    // to extend it.
    def apply(BGTypeOpt: Option[(Type, String)]) = 
      new Signature(BGTypeOpt, Set(), Map(), Map(), Map())
  }

}
