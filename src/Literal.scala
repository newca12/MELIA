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

object Literal {

  import Term._
  import Misc._
  import Subst._
  import Eqn._
  import Clauses._
  import Expression._
  import Predefined._
  import Formula._

  /**
   * The class of literals as appearing in clauses.
   * Also Context literals (CLit). Todo: Separate out Context Literals into State,
   * which would be a more logical place.
   */

  class Lit(val isPositive: Boolean, val eqn: Eqn) extends Expression[Lit] {

    // Mixin Expression
    lazy val vars = eqn.vars
    lazy val rvars = eqn.rvars
    lazy val params = Set[Param]() // parameters can occur in constraints only
    lazy val freeBGConsts = Set[FreeBGConst]() // parameters can occur in constraints only

    def applySubst(sigma: Subst) = Lit(isPositive, sigma(eqn))
    def mgus(that: Lit) = 
      if (isPositive == that.isPositive) 
	eqn mgus that.eqn
      else 
	List()
    def matchers(that: Lit, gammas:List[Subst]) = 
      if (isPositive == that.isPositive) 
	eqn.matchers(that.eqn, gammas)
      else 
	List()

    // This definitions works also to test CLits for being Assert literal
    def isAssertLit = 
      isPositive && eqn.isAssertEqn 

    def isNegVLit = 
      (!isPositive) && eqn.isPseudoVarEqn 

    val depth = eqn.depth

    override def toString = 
      if (isAssertLit)
	eqn.toString
      else if (isPositive) 
	eqn.toString
      else if (isNegVLit)
	"¬" + eqn.toString
      else if (eqn.typ == OType)
	"¬" + eqn.toString
      else "¬(" + eqn.toString + ")"

    // convenience methods: create a context literal from this
    def ^ (kind: Kind) = CLit(this, kind)
    def ^ (kind: Kind, status: CtxtStatus) = CLit(this, kind, status)
    def ^ (kind: Kind, status: CtxtStatus, idx:Int) =  CLit(this, kind, status, idx)

    // Complement
    def compl = Lit(!isPositive, eqn)

    val skoCtr = new Counter

    // Create a renaming substition from vars to a set of fresh variables
    def mkSkolemSubst(vars: Set[Var]) = {
      new Subst((for (Var(x,i) <- vars) yield 
	           (Var(x,i), Const("$sk_" + skoCtr.next()))).toMap)
    }

    def sko() = applySubst(mkSkolemSubst(vars))

    // Notice that skolem constants will not be inserted into Sigma.
    // It is not needed, as Skolem constants never occur in clauses, the are used only
    // in CUI computation, and Skolem context literals (SS)
    // are explicitly never used for paramodulation.
    // In conclusion we need not worry about typing Skolem constants.


    def == (that:Lit) = isPositive == that.isPositive && eqn == that.eqn

    lazy val isTrivialNeg = (!isPositive) && eqn.isTrivial
    lazy val isTrivialPos =  isPositive && eqn.isTrivial


    def toFormula = if (isPositive) eqn.toFormula else Neg(eqn.toFormula)

    def purify = { 
      val (eqnPure, eqnDefs) = eqn.purify 
      (Lit(isPositive, eqnPure), eqnDefs)
    }

    def isBGLiteral = eqn.isBGEquation || eqn.isBGAtom

    // straightforward lifting of para from equations to literals
    def para(E: Eqn) = 
      for ((eqn1,sigma,e1) <- eqn.para(E)) yield 
	(Lit(isPositive, eqn1),sigma,e1)

    // straightforward lifting of sup from equations to literals
    def sup(E: Eqn) = 
      for ((eqn1,sigma,e1) <- eqn.sup(E)) yield 
	(Lit(isPositive, eqn1),sigma,e1)

    // Lifting of demodulate from equations to literals.
    // Demodulate is applied into clause literals from unit clauses (only).
    // To exploit the redundancy criterion, must make sure that the demodulating 
    // equation is smaller than that clause. We ensure this by passing a
    // term to Eqn.demodulate to indicate that toplevel-demodulations into larger 
    // sides can be from equations only whose instantiated rhs is smaller than 
    // that term. (It is always OK for negative literals, tacitly assuming that
    // negative literals are larger than positive ones.)
    def demodulate(Ss: Seq[(Eqn,Set[Int])]):(Lit,Option[Set[Int]]) = {
      val (eqnSimplified, eqnIdxRelevant) = eqn.demodulate(Ss, isPositive)
      // val (eqnSimplified, eqnIdxRelevant) = eqn.demodulate(Ss, true)
      (Lit(isPositive, eqnSimplified), eqnIdxRelevant)
    }

    // this produces that in lambda
    def produces(that: Lit, Lambda: Seq[CLit]) = {

      // Whether clit blocks this from producing that
      def blocks(clit: CLit):Boolean = {
	val clitCompl = clit.compl
	clit.kind match {
	  case PP => 
  	    // Check if clit sits between this and that 
  	    this > clitCompl && clitCompl >~ that
	    // println("blocks: " + res + ": " + this + " > " + clitCompl + ">=" + that)
	  case UU | SS => {
  	    // clit is universal or Skolmized, so we
  	    // can use any instance to check if that
  	    // instance sits between this and that.
  	    // We do this by unifying this and clit
  	    // and checking the instance of clit then.
  	    // There are 0, 1 or 2 different substitutions in sigmas.
  	    // Check if one of these blocks:
	    for (sigma <- this.fresh mgus clitCompl;
		 clitComplInst = sigma(clitCompl)) 
		   if (this > clitComplInst && clitComplInst >~ that)
		     return true
	    false
	  }
	}
      }
      this >~ that && ! ( Lambda exists { blocks(_) } )
      // println(res + ": " + this + " produces ")
      // println("      " + that + " in " + Lambda)
      // res
    }
			    
    // Straight from the definition
    def iin(clits: Seq[CLit]) =
      clits exists { K => 
	K.kind match {
	  case PP => K ~ this
	  case _ => K >~ this
	}
      }

    // Instance of a universal literal
    def uin(clits: Seq[CLit]) =
      clits exists { K => 
	K.kind == UU && K >~ this
      }
  }

  def Lit(isPositive: Boolean, eqn: Eqn) = new Lit(isPositive: Boolean, eqn: Eqn)

  /**
   * Contexts Literals
   */

  abstract class Kind
  case object UU extends Kind
  case object PP extends Kind
  case object SS extends Kind

  abstract class CtxtStatus
  case object DD extends CtxtStatus // decision Literal
  case object II extends CtxtStatus // implied Literal


  class CLit(lit: Lit, val kind: Kind, val status: CtxtStatus, 
		val idx: Int) extends Lit(lit.isPositive, lit.eqn) {

    def == (that: CLit) = 
      isPositive == that.isPositive && eqn == that.eqn &&
      kind == that.kind && status == that.status && idx == that.idx

    def isContradictory(that: CLit):Boolean = 
      // assumes that not both this and that are special
      if (isNegVLit || that.isNegVLit ||
	  isAssertLit || that.isAssertLit)
	false
      else (kind, that.kind) match {
	case (PP, PP) => this ~ that.compl
	case (PP, _) =>  that.compl >~ this
        case (_, PP) =>  this >~ that.compl
	case (_, _)  =>  !(this.fresh mgus that.compl).isEmpty // Kind SS is possible
      }
    

    def isContradictory(clits: Seq[CLit]):Boolean = 
      clits exists { _.isContradictory(this) }

    override def toString = 
      super.toString + 
    (kind match { 
      case UU => "" 
      case PP => "^"+PP
      case SS => "^"+SS }) +
    (status match { 
      case II => "" 
      case DD => "^"+DD})
    
 }

  // Companion object
  object CLit {
    // def apply(L: Lit, kind: Kind, status: CtxtStatus, idx: Int, idxRelevant: Set[Int]) = 
    //   new CLit(L, kind, status, idx, idxRelevant)
    def apply(L: Lit, kind: Kind, status: CtxtStatus, idx: Int) = 
      new CLit(L, kind, status, idx)
    def apply(L: Lit, kind: Kind, status: CtxtStatus) = 
      new CLit(L, kind, status, -1)
    def apply(L: Lit, kind: Kind) = 
      new CLit(L, kind, II, -1)
  }

}
