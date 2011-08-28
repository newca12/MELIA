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

object Predefined {

  import Term._
  import Eqn._
  import Literal._
  import Clauses._
  import Type._ 
  import Formula._
  import Subst._
  import Signature._
  import scala.util.matching.Regex

  /**
   * All the predefined things
   */

  // Types
  object IType extends Type("$i") // Individuals (of the Herbrand Universe)
  // cannot call the object iType because if so Scala pattern matching assumes iType is a *variable*
  object OType extends Type("$o") // Truth values
  object TType extends Type("$tType") // The type of types (kinds)
  object IntType extends Type("$int")
  object RatType extends Type("$rat")
  object RealType extends Type("$real")

  // Terms
  val TT = Const("$true")   // The constant true used as rhs of predicative equations,
  // with $$$, $$$true will be the smallest term around, hence equations get ordered the right way
  val AAConst = Const("$A") // Assert
  val AAVar = Var("$A")     // Assert

  val VVConst = Const("$V") // Pseudo-Variable
  val VVVar = Var("$V")     // Pseudo-Variable


  // Equations
  object TrueEqn extends Eqn(TT, TT, OType)
  // The type of PseudoVarEqn and AssertEqn does not matter,
  // unification and matching ignores it. This must be so that
  // they can be used to pair with equations of any type
  object PseudoVarEqn extends Eqn(VVConst, VVConst, OType)
  object AssertEqn extends Eqn(AAConst, AAConst, OType)

  // Literals
  object TrueLit extends Lit(true, TrueEqn)
  // The pseudo-literal -v. 
  object NegVLit extends Lit(false, PseudoVarEqn)
  // The assert literal. 
  object AssertLit extends Lit(true, AssertEqn)

  // Clauses
  object TrueClause extends Clause(clauseCtr.next(),
				   OClause(TrueLit), 
				   Restriction(), Constraint(), Set(), "true clause") 


  // (input) Formulas
  object TrueAtom extends Atom("$true", List()) {
    override def applySubst(sigma: Subst) = this
    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = this
    override def toString = "⊤"
  }
  object FalseAtom extends Atom("$false", List()) {
    override def applySubst(sigma: Subst) = this
    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = this
    override def toString = "⊥"
  }
  

  // Signature, over empty background signature
  var signatureEmpty = Signature(None)
  signatureEmpty += IType
  signatureEmpty += OType
  signatureEmpty += TType
  signatureEmpty += "$true" -> Rank0(OType)
  signatureEmpty += "$false" -> Rank0(OType)

  // Notice: no space between - and digits
  def isIntegerConstRegEx = """[+-]?[0-9]+""" 

  var signatureInt = Signature(Some(IntType, isIntegerConstRegEx))
  signatureInt += IType
  signatureInt += OType
  signatureInt += TType
  // signatureInt += "=" -> Rank2((IType, IType) -> OType)
  signatureInt += "$true" -> Rank0(OType)
  signatureInt += "$false" -> Rank0(OType)
  signatureInt =
    signatureInt.addBG(
      "$true"       -> Rank0(OType), // Belongs to both FG and BG operators!
      "$uminus"     -> Rank1(IntType -> IntType),
      "$sum"        -> Rank2((IntType, IntType) -> IntType),
      "$difference" -> Rank2((IntType, IntType) -> IntType),
      "$product"    -> Rank2((IntType, IntType) -> IntType),
      "$less"       -> Rank2((IntType, IntType) -> OType),
      "$lesseq"     -> Rank2((IntType, IntType) -> OType),
      "$greater"    -> Rank2((IntType, IntType) -> OType),
      "$greatereq"  -> Rank2((IntType, IntType) -> OType),
      "$evaleq"     -> Rank2((IntType, IntType) -> OType),
      "$divides"     -> Rank2((IntType, IntType) -> OType)
    )
  signatureInt =
    signatureInt.addFormatFns(
      "$uminus"     -> prefix("-"),
      "$sum"        -> infix(" + "),
      "$difference" -> infix(" - "),
      "$product"    -> infix("⋅"),
      "$less"       -> infix(" < "),
      "$lesseq"     -> infix(" ≤ "),
      "$greater"    -> infix(" > "),
      "$greatereq"  -> infix(" ≥ "),
      "$evaleq"     -> infix(" ≐ "),
      "$divides"    -> infix("|")
    )

}
