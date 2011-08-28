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

object Eqn {

  import Expression._ 
  import Signature._
  import Predefined._
  import Clauses._ 
  import Term._ 
  import Subst._ 
  import Type._ 
  import State._ 
  import Formula._ 

  /**
   * Equations
   */ 

  class Eqn(s: Term, t: Term, val typ: Type) extends Expression[Eqn] {

    // Represent equations in an ordered way, if possible
    // isOrdered is true iff one side is greater than the other
    // in this case lhs holds the greater side.
    // All non-equational atoms are always ordered
    var lhs = s 
    var rhs = t
    var isOrdered = false
    if (s gtr_lpo t) 
      isOrdered = true
    else if (t gtr_lpo s) {
      isOrdered = true; 
      lhs = t; rhs = s
    }
    else if (t.toString > s.toString) {
      // this gives us a "canonical" ordering of equations,
      // so that checking equality modulo symmetry can be done by using
      // the oriented versions in this ordering only
      lhs = t; rhs = s
    }

    // because the print name of TT starts with "$", TT is smaller than
    // every non-variable term.

    def samePredSym(that: Eqn) = {
      // Assume that this and that are predicate atoms
      lhs.asInstanceOf[FunTerm].fun == that.lhs.asInstanceOf[FunTerm].fun
    }

    lazy val isTrivial = lhs == rhs

    val depth = math.max(lhs.depth, rhs.depth)

    def isAssertEqn = lhs == AAConst
    def isPseudoVarEqn = rhs == VVConst

    // Whether this is a foreground equation or not (by definition).
    // Intuitively, *background* equations are those that can be checked for 
    // satisfiability by the background theory.
    // Assume this is pure.
    lazy val isBGEquation = 
      // Only background-sorted equations can be BG equation, and
      (Sigma.BGTypes contains typ) &&
      // lhs is a variable or top-level symbol is background, and
      (lhs.isVar || (Sigma.BGOps contains lhs.asInstanceOf[FunTerm].fun)) &&
      // same for rhs
      (rhs.isVar || (Sigma.BGOps contains rhs.asInstanceOf[FunTerm].fun))

    lazy val isBGAtom = 
      typ == OType && (Sigma.BGOps contains lhs.asInstanceOf[FunTerm].fun)


    def toFormula = 
      if (typ == OType) {
	// Boolean always have lhs non-variable.
	val FunTerm(fun, args) = lhs.asInstanceOf[FunTerm]
	Atom(fun, args)
      } else
	Equation(lhs, rhs)

    // Used to convert an equation into a term.
    // Officially, it does not have a type, because $equal does not have one.
    // This is OK as we never need to check the type of a term itself, but we do need
    // to check the type of an equation
    def toTerm = FunTerm("$equal",List(lhs,rhs))

    // Mixin UnifiableExpression[Eqn]
    def mgus(that: Eqn) = {
      val result =
	if (this.isPseudoVarEqn)
	  List(Subst(VVVar.fresh.asInstanceOf[Var] -> that.toTerm))	
	else if (that.isPseudoVarEqn)
	  List(Subst(VVVar.fresh.asInstanceOf[Var] -> this.toTerm))	
	else if (this.isAssertEqn) 
	  List(Subst(AAVar -> that.toTerm))	
	else if (that.isAssertEqn)
	  List(Subst(AAVar -> this.toTerm))	
	else {
	  // Have all special cases now. Only unification of equations of the same
	  // type is possible
	  if (typ == that.typ) {
	    if (isOrdered && that.isOrdered) // This includes the non-equational case
	      pair(lhs,rhs) mgus pair(that.lhs,that.rhs) // which is either the empty list or a singleton
	    else // at least one equation is unordered - need to consider both cases
	      (pair(lhs,rhs) mgus pair(that.lhs,that.rhs)) :::
	    (pair(rhs,lhs) mgus pair(that.lhs,that.rhs))
	    // todo: we could possibly check that both are most general
	    // otherwise return only the more general one
	    // println("mgus(" + this + ", " + that + ") = " + result) 
	  } else 
	    List() // different types
	}
      result
    }
    
    def matchers(that: Eqn, gammas: List[Subst]) = 
      if (this.isPseudoVarEqn) {
	val delta = Subst(VVVar.fresh.asInstanceOf[Var] -> that.toTerm)
	gammas map { _ ++ delta }
      }
      else if (this.isAssertEqn) {
	val delta = Subst(AAVar -> that.toTerm)
	gammas map { _ ++ delta }
      }
      else if (that.isPseudoVarEqn || that.isAssertEqn)
	List()
      else { 
	if (typ == that.typ) {
	  if (isOrdered && that.isOrdered)
	    pair(lhs,rhs).matchers(pair(that.lhs,that.rhs),gammas)
	  else 
	    (pair(lhs,rhs).matchers(pair(that.lhs,that.rhs),gammas)) :::
  	    (pair(rhs,lhs).matchers(pair(that.lhs,that.rhs),gammas))
	} else
	  List() // different types
      }

    // Because equations are symmetric, equality is modulo symmetry.
    // But see above for why we don't need this:
    // if (isOrdered && that.isOrdered)
    // 	(lhs == that.lhs && rhs == that.rhs)
    // else
    // 	(lhs == that.lhs && rhs == that.rhs) ||
    // 	(lhs == that.rhs && rhs == that.lhs)
    def ==(that: Eqn) = (typ == that.typ && lhs == that.lhs && rhs == that.rhs)


    def purify: (Eqn, List[Eqn]) = {
      (lhs, rhs) match {
	case (Var(_,_), Var(_,_)) => (this, List())
	case (Var(_,_), FunTerm(fun,_)) => {
	  val (rhsPure, rhsDefs) = rhs.purify
	  (Eqn(lhs, rhsPure, typ), rhsDefs)
	}
	case (FunTerm(fun,_), Var(_,_)) => {
	  val (lhsPure, lhsDefs) = lhs.purify
	  (Eqn(lhsPure, rhs, typ), lhsDefs)
	}
	case (FunTerm(lhsFun,_), FunTerm(rhsFun,_)) => {
	  val (lhsPure, lhsDefs) = lhs.purify
	  val (rhsPure, rhsDefs) = rhs.purify
	  if (((Sigma.BGOps contains lhsFun) && (Sigma.BGOps contains rhsFun)) ||
	      ((Sigma.FGOps contains lhsFun) && (Sigma.FGOps contains rhsFun)))
	    // no need to further purify
	    (Eqn(lhsPure, rhsPure, typ), lhsDefs ::: rhsDefs)
	  else {
	    val x = Var("X",variantCtr.next())
	    (Eqn(lhsPure, x, typ), Eqn(rhsPure, x, typ) :: (lhsDefs ::: rhsDefs))
	  }
	}
      }
    }


    override def toString = {
      if (this.isPseudoVarEqn) 
	lhs.toString
      else if (this.isAssertEqn) 
	lhs.toString
      else if (typ == OType) 
	lhs.toString 
      else {
	val eqsym = if (isOrdered) "→" else "≈"
	if (typ == IType) 
	  lhs.toString + eqsym + rhs.toString
	else 
	  lhs.toString + " " + eqsym + "(" + typ + ") " + rhs.toString
      }
    }
    
    // Superposition from E into this, result structure is the same as with
    // paramodulation into terms
    // supFlag determines if we do superposition, in this case 
    // paramodulation into smaller sides is forbidden
    def sup(E: Eqn) = {
      // we do the paramodulations into this.lhs and this.rhs separately,
      // the latter only if needed and collect the results
      // Typechecking is to be done in Term.para

      val lhsResult = 
	for ((lhs1, sigma, e1) <- lhs.para(E);
	     // superposition: don't paramodulate into smaller sides, check it.
	     // the first test is redundant with the second but cheaper
	     if (isOrdered || !(sigma(rhs) geq_lpo sigma(lhs)))) yield 
	       // we build up the result structure with the (non-instatiated)
	       // equation
	       (Eqn(lhs1, rhs, typ), sigma, e1)
		    
      val rhsResult = 
	if (isOrdered)
	  // rhs is the smaller side and hence shall not be paramodulated into
	  List()
	else
	  for ((rhs1, sigma, e1) <- rhs.para(E);
	       // superposition: don't paramodulate into smaller sides, check it.
	       // the first test is redundant with the second but cheaper
	       if (!(sigma(lhs) geq_lpo sigma(rhs)))) yield 
		 // we build up the result structure with the (non-instatiated)
	         // equation
		 (Eqn(lhs, rhs1, typ), sigma, e1)
		 
      lhsResult ::: rhsResult
    }

    def para(E: Eqn) = {
      // we do the paramodulations into this.lhs and this.rhs separately,
      // and collect the results
      ( for ((lhs1, sigma, e1) <- lhs.para(E)) yield 
	// we build up the result structure with the (non-instatiated)
	// equation
	(Eqn(lhs1, rhs, typ), sigma, e1) ) :::
      ( for ((rhs1, sigma, e1) <- rhs.para(E)) yield
	(Eqn(lhs, rhs1, typ), sigma, e1) )
    }


    lazy val vars = lhs.vars union rhs.vars
    lazy val rvars = lhs.rvars union rhs.rvars
    lazy val params = Set[Param]()
    lazy val freeBGConsts = Set[FreeBGConst]()

    def applySubst(sigma: Subst) = new Eqn(sigma(lhs), sigma(rhs), typ)

    def demodulate(Ss: Seq[(Eqn,Set[Int])], topLevelCheck: Boolean):(Eqn,Option[Set[Int]]) = {
      // topLevelCheck indicates if demodulating into the toplevel-position
      // of the larger side needs checking if the demodulating equation is 
      // smaller than this, which is realized by passing the other side
      // as a bound to demodulate.
      val (lhsSimplified, lhsIdxRelevant) = 
	lhs.demodulate(Ss, if (topLevelCheck) Some(rhs) else None)
      val (rhsSimplified, rhsIdxRelevant) = 
	rhs.demodulate(Ss, if (topLevelCheck && !isOrdered) Some(lhs) else None)
      val IdxRelevant = 
	(lhsIdxRelevant, rhsIdxRelevant) match {
	  case (None, None) => None
	  case (Some(lhsIdxs), None) => Some(lhsIdxs)
	  case (None, Some(rhsIdxs)) => Some(rhsIdxs)
	  case (Some(lhsIdxs), Some(rhsIdxs)) => Some(lhsIdxs union rhsIdxs)
      }
      if (IdxRelevant == None)
	// No effect, don't bother constructing something new
	(this, None)
      else
	(Eqn(lhsSimplified, rhsSimplified, typ), IdxRelevant)
    }
  }

  // handy
  object Eqn {
    def apply(s: Term, t: Term, typ: Type) = new Eqn(s, t, typ)
    def unapply(e: Eqn) = Some((e.lhs, e.rhs, e.typ))
  } 
}

