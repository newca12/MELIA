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

object BGContext {

  import Term._
  import Misc._
  import Formula._
  import Predefined._
  import Type._
  import Subst._
  import Signature._
  import Clauses._
  import Inference._
  import Integers._
  import Cooper._


  /*
   * A Background Context is a list of closed formulas over the background
   * signature extended by rigid variables, which are constants.
   */


  class BGContextExtensionFail extends Exception 

  // The background context, kept globally
  var Gamma = new BGContext

  class BGContext {
    
    // *Non-trivial* Equations between SymBGConsts and FunTerms,
    // they are used to eliminate the rigid variables from the fs.
    // It is better to maintain them here than in Integer.scala, as here
    // we do an incremental version, and use them as rewrite rules for the formulas in fs
    var eqns = List[(SymBGConst, FunTerm)]()

    // The formulas in the background context, except the eqns above
    var fs = List[Formula]() 

    // The rigid variables that have been *declared*, 
    // at least the ones occuring in fs and equations
    var rvars = Set[RVar]() 
    // At least the Params occuring in fs and equations
    var params = Set[Param]() 
    // At least the skolem constants occuring in fs and equations
    var freeBGConsts = Set[FreeBGConst]() 

    // The open Restrict Inferences
    var openInfRestrict = List[InfRestrict]()

    def state = (eqns, fs, rvars, params, freeBGConsts, openInfRestrict)
    def restore(state: (List[(SymBGConst, FunTerm)], 
			List[Formula], 
			Set[RVar], 
			Set[Param], 
			Set[FreeBGConst], 
			List[InfRestrict])) {
      eqns = state._1
      fs = state._2
      rvars = state._3
      params = state._4
      freeBGConsts = state._5
      openInfRestrict = state._6
    }

    def length = fs.length

    // Handy to extract the SymBGConsts from the eqns
    def eqnsAsFormulas = eqns map { xt => Equation(xt._1, xt._2) }

    def removeOpenInfRestrict(inf: InfRestrict) {
      openInfRestrict = openInfRestrict filterNot { _ == inf }
    }

    // Add the given formula f to the background context. 
    // Some cheap cases of inconsistency are detected, thus may throw Inconsistent
    def addUnchecked(f: Formula) {
      var open = Integers.normalize(f.applyCSubst(eqns))
      // Invariant: all formulas in open have all eqns applied and are normalized
      // Same for fs
      while (!open.isEmpty) {
	var fn = open.head
	open = open.tail
	// fn is normalized and all eqns have been applied
	// We see if we get a new equation, and if so, apply it too all formulas
	// so far and remember it
	val e:Option[(SymBGConst,FunTerm)] = 
	  fn match {
	    case ZeroEQPoly(Polynomial(k, Monomial(k1, c1) :: Monomial(k2, c2) :: Nil)) =>
	      (k1, k2) match {
		case ( 1, _ ) => Some(c1 -> (Monomial(k2+k, c2) * -1).toTerm)
		case (_ ,  1) => Some(c2 -> (Monomial(k1+k, c1) * -1).toTerm)
		case (-1, _ ) => Some(c1 -> (Monomial(k2+k, c2)     ).toTerm)
		case (_ , -1) => Some(c2 -> (Monomial(k1+k, c1)     ).toTerm)
		case (_ , _ ) => None
	      }
	    case ZeroEQPoly(Polynomial(k, Monomial(k1, c1) :: Nil)) =>
	      k1 match {
		case ( 1) => Some(c1 -> BGLitConst(-k))
		case (-1) => Some(c1 -> BGLitConst(k))
		case ( _) => None
	      }
	    case _ => None
	  }
	e match {
	  case None => 
	    // no success with fn as an equation. Just plainly add it
	    if (!(fs contains fn))
	      fs ::= fn
	  case Some((rv,c)) => {
	    // Preserve the invariants above
	    // First for fs
	    var newFs = List[Formula]()
	    for (f <- fs;
		 hf = f.applyCSubst(rv -> c).reduceInnermost(elimTrivial);
		 if hf != TrueAtom;
		 if !(newFs contains hf)) {
		   if (hf == FalseAtom)
		     throw new Inconsistent
		   else newFs ::= hf
		 }
	    fs = newFs
	    // Second for open
	    var newOpen = List[Formula]()
	    for (f <- open;
		 hf = f.applyCSubst(rv -> c).reduceInnermost(elimTrivial);
		 if hf != TrueAtom;
		 if !(newOpen contains hf)) {
		   if (hf == FalseAtom)
		     throw new Inconsistent
		   else newOpen :::= Integers.normalize(hf)
		 }
	    open = newOpen
	    // The rhs of the eqns have to be normalized by the new rule
	    eqns = eqns map { xt => ((xt._1 -> xt._2.applyCSubst(rv -> c))) }
	    // Finally remeber the new eqn
	    eqns ::= ((rv -> c))
	  }
	}
	
	// Common to all cases
	rvars ++= fn.rvars
	params ++= fn.params
	freeBGConsts ++= fn.freeBGConsts
      }
    }

    // Some use cases of the above, which all include consistency checks
    def ++= (hfs: List[Formula]) {
      val saved = state
      try {
	hfs foreach { addUnchecked(_) }
	Integers.checkConsistency(fs)
      } catch {
	case _:Inconsistent => {
	  restore(saved)
	  throw new BGContextExtensionFail
	}
      }
    }

    // Usecases
    def += (f: Formula) {
      this ++= List(f)
    }
    def ++= (c: Constraint) {
      this ++= c.fs
    }

    // Expensive!
    def isConsistentWith(c: Constraint):Boolean = {
      if (c.isEmpty)
	return true
      require(c.vars.isEmpty, { println("isConsistentWith: expected closed constrained, got " + c) })
      // println("isConsistentWith: " + c)
      // Gamma.show()
      val saved = state
      try {
	c.fs foreach { addUnchecked(_) }
	Integers.checkConsistency(fs)
      } catch {
	case _:Inconsistent => {
	  restore(saved)
	  return false
	}
      }
      restore(saved)
      return true
    }


/*
    /// A "cheap" pretest before ++= above is called, or to delete clauses with inconsistent constraints
    def isConsistentWithPre(c: Constraint):Boolean = {
      require(c.vars.isEmpty, { println("isConsistentWith: expected closed constrained, got " + c) })
      val saved = state
      try {
	c.fs foreach { addUnchecked(_) }
      } catch {
	case _:Inconsistent => {
	  restore(saved)
	  return false
	}
      }
      restore(saved)
      return true
    }
  */  

    // Declare a rigid variable
    def declare(rv: RVar) {
      // We treat rigid variables as operators (i.e. constants)
      Sigma = Sigma addBG (rv.name -> Rank0(Sigma.BGType))
      // Pairwise inequality constraints
      // This assumes that rv has not been declared before,
      // otherwise we get an inconsistent context
      rvars foreach { hrv => 
	if (hrv != rv) this += Neg(Equation(hrv, rv))
      }
      rvars += rv // make it available for Inst
    }

    /**
     * All domain instantiation substitutions for a given constraint
     */
    def DIsubsts(c: Constraint) = {
      val rvarsList = rvars.toList
      var res = List(Subst()) 
      for (x <- c.vars) {
	// All bindings of x with a rigid variables
	val xSubsts = rvarsList map { (x -> _) }
	res = combine(res, xSubsts)
      }
      res // filter { gamma => isConsistentWithPre(gamma(c)) }
    }


    // All DI substitutions that involve rv in the codomain
    def DIsubsts(c: Constraint, rv: RVar) = {

      def pow(m: Int, n:Int) = {
	var res = 1
	for (i <- 1 to n) res *= m
	res
      }

      // The rigid variables in this minus the given rv.
      // rv is treated specially below
      val rvarsList = (rvars - rv).toList 
      var res = List[Subst]()

      // Use a non-zero bitword that tells us where to include rv at a position or not
      // Because we start by one, every bitword contains at least one yes.
      for (i <- 1 to (pow(2, c.vars.size)-1)) {
	var next = List(Subst()) 
	var iPos = i // The rightmost bit of iPos will tell us
	for (x <- c.vars) {
	  val xSubsts = 
	    if (iPos % 2 == 0) 
	      // take the whole existing rvars
	      rvarsList map { (x -> _) }
	    else 
	      // hit - take the listed one
	      List(x -> rv)
	  next = combine(next, xSubsts)
	  iPos = iPos / 2
	}
	res :::= next
      }
      res
    }

    def combine(ss:List[Subst], vts:List[(Var, Term)]) = 
      for (s <- ss; vt <- vts) yield (s + vt)


    override def toString = fs.toList.toMyString("⊤", "(", " ∧ ", ")")

    def show() {
      println("Gamma:")
      println("  Rigid variables: " + rvars)
      println("  Parameters: " + params)
      println("  Free constants: " + freeBGConsts)
      println("  Open Restrict inferences: " + openInfRestrict)
      println("  Formulas (equations with lhs eliminated): ")
      for ((rv, c) <- eqns) {
	println("  " + rv + " ≈ " + c )
      }
      println("  Formulas (other), over rigid variables " + rvars + ":")
      for (f <- fs) 
	println("  " + f)
    }
  }
}

