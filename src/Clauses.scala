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

object Clauses {

  /**
   * Constrained clauses, comprised of Ordinary Clauses, Restrictions and Constraints
   */

  import Term._
  import Eqn._
  import Predefined._
  import Subst._
  import Expression._
  import Literal._
  import Misc._
  import Flags._
  import Formula._
  import BGContext._

  // Thrown when a clause is detected as redundant
  case class Redundant() extends Exception {}

  // Whenever a closing clause (instance) is found we can fail immediately,
  // hence the Closing exception.
  // The clause D is needed only for documentation purposes.
  case class Closing(val idxRelevant: Set[Int], val D: Clause) extends Exception {
    override def toString = "Closing(" + idxRelevant + "," + D + ")"
  }

  /**
   * The contrained clauses, consisting of an ordinary clause and a
   * context restriction.
   * Further, idxRelevant is the set of idx'es of the context
   * literals that are relevant to derive this
   */

  class Clause(val nr: Int,
	       val C: OClause, 
	       val R: Restriction, 
	       val c: Constraint,
	       val idxRelevant: Set[Int], 
	       val doc: String) extends Expression[Clause] {
    

    // Mixin Expression
    lazy val vars = (C.vars union R.vars) union c.vars
    lazy val rvars = (C.rvars union R.rvars) union c.rvars
    lazy val params = c.params // parameters can occur in c only
    lazy val freeBGConsts = c.freeBGConsts // parameters can occur in c only
    
    // Have to check separately that sigma is simple for c
    def applySubst(sigma: Subst) = 
      Clause(clauseCtr.next(),sigma(C), sigma(R), sigma(c), idxRelevant, doc)
    // mgus don't need to be defined - dummy
    def mgus(that: Clause) = List[Subst]()
    def matchers(that: Clause, gammas: List[Subst]) =
      C.matchers(that.C, gammas) match {
	case Nil => Nil
	case gammasC => { 
	  R.matchers(that.R, gammasC) match {
	    case Nil => Nil
	    case gammasR => c.matchers(that.c, gammasR)
	  }
	}
      }
	
    def isUnitClause = R.isEmpty && c.isEmpty && C.length == 1 

    val weight = List(C.depth,R.depth,R.length).max // Restrictions can grow without bound in length, hence included

    // The selection function for negative literals:
    // If negative literals are selected, only these are used for superposition and CUIs.
    // Otherwise, all literals are used.
    // If all literals are used, CUIs are used for split an close, otherwise
    // CUIs are (new) clauses with a non-empty (non-negative) ordinary clause part
    // Notice that if C is empty allUsable is implied
    lazy val iUsable = selectionFunction.value match {
	case "auto" => 
	  if (!C.iNegLits.isEmpty) {
	    // There is a negative literal. We use them all if a positive equational literal
	    // exists, so there is a chance to derive a unit equational clause.
	    if (C.iPosLits exists { C(_).eqn.typ != OType })
	      // Yes, there is a positive equation
	      // (0 until C.length).toList
	      C.iNegLits
	    else
	      // no - use all literals
	      (0 until C.length).toList
	  } else 
	    C.iPosLits
	case "all" => if (!C.iNegLits.isEmpty) C.iNegLits else C.iPosLits
	case "one" => if (!C.iNegLits.isEmpty) List(C.iNegLits.head) else C.iPosLits
	case "off" => (0 until C.length).toList
    }

    // whether all literals in C are selected or not
    lazy val allUsable = C.iPosLits.size + C.iNegLits.size == iUsable.size
	 
    // the indices of the isolated literals, i.e. those that are variable disjoint
    // with the rest
    lazy val iIsolatedCLits = 
      // those literals in C that are already isolated in C and do not share
      // variables with R and with c
      C.iIsolatedLits filterNot { C(_).vars intersects (R.vars union c.vars) }

    /**
     * The inf* procedures below return all clauses that can be obtained by one-step
     * application of the inference rule to this, as specified.
     */
    
    /**
     * The generic superposition/paramodulation inference rule
     * which implements both Sup-Pos and Sup-Neg.
     * iL is the index of the literal paramodulated
     * into, and K is the (positive) context literal to paramodulate from.
     */
    def infSup(iL:Int, K:CLit) = {
      // Assume that K is parametric or universal (but not Skolem).
      // First do superposition or paramodulation into L, depending whether 
      // L is negative or positive and variable disjoint with the rest
      val lRes = 
	if (!C(iL).isPositive || // a negative literal, or ...
	    (iIsolatedCLits contains iL))
	  // ... the to-literal is variable-disjoint with the others.
	  // these are the two cases we do superposition
	  C(iL).sup(K.eqn)
	else
	  // else do paramodulation
	  C(iL).para(K.eqn)
      // build the result using the triples in lRes
      for ((l1,sigma,e1) <- lRes;
	   // sigma must be simple, i.e. not act on the variables in c
	   // If it does, it would introduce a foreground
	   if (sigma.isSimple(c))) yield {
	// first we build the paramodulated clause part
	val newClits = C.lits.replaceNth(iL, l1)
	// second the restriction
	val newRlits = 
	  if (K.kind == UU) 
	    // implicit simplifiction by not adding e1 to D.R.eqns
	    R.eqns
	  else
	    // parametric case - must include the used equation e1
	    e1 :: R.eqns
	// finally build the new clause
        Clause(clauseCtr.next(),
	       OClause(sigma(newClits)), 
	       Restriction(sigma(newRlits)), 
	       sigma(c),
	       idxRelevant + K.idx, "Sup(" + K + ", " + nr + ")").normalize
        }
    }

    /*
     * Simplfication of a clause by unit-resolution steps that
     * make the clause one literal shorter
     */

    def unitSimpRes(CSs: Seq[Clause]) = {
      val units = CSs filter { _.isUnitClause }
      var thisSimplified = this
      // var touched = false
      while (
	(0 until thisSimplified.C.length) exists { 
	  i => units exists { 
	    D => { 
	      val unit = D.C(0)
	      val hit = 
		if (thisSimplified.iIsolatedCLits contains i) 
		  !(unit mgus thisSimplified.C(i).compl.fresh).isEmpty
		else
		  // thisSimplified contains non-isolated literals, hence
		  // its length must be greated than one. Therefore we can use
		  // >~ (instead of >) and unitSimpRes will still be well-founded.
		  unit >~ thisSimplified.C(i).compl
	      if (hit) {
		thisSimplified = 
		  Clause(clauseCtr.next(),
			 OClause(thisSimplified.C.lits.removeNth(i)),
			 R, 
			 c,
			 thisSimplified.idxRelevant union D.idxRelevant, 
			 "Unit-Simp-Res(" + unit + ", " + nr + ")")
		// touched = true
	      } 
	      hit // whether to continue the while loop
	    }
	  }
	}
      ) 
      {} // the body of the while loop
      // (thisSimplified,touched)
      thisSimplified
    }

    // Whether this is subsumed by the given CS
    def isSubsumed(CS: Clause) = 
      CS.isUnitClause && (C.lits exists { CS.C(0) >~ _ })
      
    // Simplify the clause part C by the given CSs.
    def simplifyC(CSs: Seq[Clause]):Clause = {

      val CSsDemodulators = 
	for (d <- CSs;
	     if d.isUnitClause && d.C(0).isPositive;
	     e = d.C(0).eqn;
	     // predicates are treated by subsumption 
	     // and simplifying unit resolution
	     if e.typ != OType && e.isOrdered) yield 
	       (e, d.idxRelevant)
      // todo: better do this test separately, as simplifyC does not
      // modify R and hence the test will be done many times with the same R
       if (R.isReducible(CSsDemodulators map { _._1 }))
 	 throw new Redundant()

      val (cSimplified1, cStatus1) = C.demodulate(CSsDemodulators) 
      val thisSimplified1 = cStatus1 match {
       	case None => 
	  this
	case Some(cIdxRelevant) => {
	  val res = Clause(clauseCtr.next(),
		 cSimplified1, 
		 R, c, idxRelevant union cIdxRelevant, "Demod(" + nr + ")").normalize
	  res
	}
      }
      
      // Unit simplification resolution
      // val (thisSimplified, touched) = thisSimplified1.unitSimpRes(CSs)
      val thisSimplified2 = 
	if (Flags.simplifyingUnitResolution.valueBoolean)
	  thisSimplified1.unitSimpRes(CSs)
	else
	  thisSimplified1

      // Subsumption check
      if (CSs exists { thisSimplified2.isSubsumed(_) })
       	throw new Redundant()

      // strictly speaking not necessary but useful to detect empty clause early
      if (thisSimplified2.C.isEmpty && 
	  thisSimplified2.R.isEmpty && thisSimplified2.c.isEmpty) 
	throw new Closing(thisSimplified2.idxRelevant, thisSimplified2)

      thisSimplified2
    }

    def simplifyC(CS: Clause):Clause = simplifyC(List(CS))

    // Ditto, wrt the Restriction part
    def simplifyR(clits: Seq[CLit]):Clause = {
      val (rSimplified, rStatus) = R.simplify(clits)
      rStatus match {
	case None =>
	  // don't bother making a new clause
	  // (this, false)
	  this
	case Some(rIdxRelevant) => {
	  // put together the new Clause
	  val resIdxRelevant = idxRelevant union rIdxRelevant
	  // strictly speaking not necessary but useful to detect empty clause early
	  val newNr = clauseCtr.next()
	  if (C.isEmpty && rSimplified.isEmpty && c.isEmpty) 
	    throw new Closing(resIdxRelevant, Clause(newNr, C, rSimplified, c, resIdxRelevant, 
						     "Simp(" + nr + ")"))
	  else
	    Clause(newNr, C, rSimplified, c, resIdxRelevant, "Simp(" + nr + ")")
	}
      }
    }

    // Convenience function
    def simplifyR(clit: CLit):Clause = simplifyR(List(clit))

    // Move all BGLiterals into the constraint part.
    // The need arises after Superposition or Demodulation because then
    // a (dis)equation between variables or rigid variables only can come up
    def normalize = {
      var touched = false
      var newCLits = List[Lit]()
      var newcFs = c.fs
      for (i <- 0 until C.length) 
	if (C(i).isBGLiteral) {
	  newcFs ::= C(i).compl.toFormula
	  touched = true
	}
      else
	newCLits ::= C(i)
      if (touched)
	Clause(clauseCtr.next(), OClause(newCLits.reverse), R, Constraint(newcFs), idxRelevant, doc)
      else
	// don't bother making a new clause
	this
    }


    override def toString = 
      nr + ":" + doc + ":" + C.toString + 
      ((R.eqns, c.fs) match {
	case (Nil, Nil) => ""
	case (Nil, _) => " ← ∅ ⋅ " + c.toString
	case (_, Nil) => " ← " + R.toString
	case (_, _) => " ← " + R.toString + " ⋅ " + c.toString
      }) + ":" + iUsable.toMyString("[", ",", "]")
  }

  // companion object
 object Clause {
    def apply(nr: Int, C: OClause, R: Restriction, c: Constraint, idxRelevant: Set[Int], doc: String) = 
      new Clause(nr, C, R, c, idxRelevant, doc)

   def apply(C: OClause, doc: String) = 
     new Clause(clauseCtr.next(), C, Restriction(), Constraint(), Set(), doc)

   def apply(C: OClause, c: Constraint, doc: String) = 
     new Clause(clauseCtr.next(), C, Restriction(), c, Set(), doc)

 }

  // A counter to generate unique numbers for Clauses
  val clauseCtr = new Counter
    

  /**
   * Ordinary clause
   */
  case class OClause(lits: List[Lit]) extends Expression[OClause] {

    val C = lits.toArray // use for faster access of individual literals

    val depth = if (lits.isEmpty) 0 else (lits map { _.depth }).max

    // some ArrayLike operations
    def apply(i: Int) = C(i)
    def length = C.length

    // Mixin Expression:
    lazy val vars = lits.vars
    lazy val rvars = lits.rvars
    lazy val params = Set[Param]() // parameters can occur in constraints only 
    lazy val freeBGConsts = Set[FreeBGConst]()

    def applySubst(sigma: Subst) = OClause(sigma(lits))
    // mgus don't need to be defined - dummy
    def mgus(that: OClause) = List[Subst]()
    def matchers(that: OClause, gammas: List[Subst]) = 
      if (length != that.length) 
	List()
      else 
	Expression.matchers(lits, that.lits, gammas)

    // New stuff

    // The indices of the isolated literals in C.
    // Straightforward from the definition.

    var iIsolatedLits = List[Int]()
    for (iL <- 0 until C.length) 
      if ((0 until C.length) forall { 
	      jL => iL == jL || !(C(iL).vars intersects C(jL).vars)}) 
	iIsolatedLits ::= iL

    var iPosLits = List[Int]()
    var iNegLits = List[Int]()
    // todo: check what of the below we really need
    for (i <- 0 until C.length) {
      if (C(i).isPositive) 
	iPosLits ::= i
      else {
	iNegLits ::= i
      }
    }

    def isPositive = iNegLits.isEmpty
    def isNegative = iPosLits.isEmpty
    def hasPositive = !iPosLits.isEmpty
    def hasNegative = !iNegLits.isEmpty

    def isEmpty = lits.isEmpty

    def isTautology:Boolean = 
      if (lits exists { _.isTrivialPos })
	return true
      else {
	for (ks <- lits.tails; if !ks.isEmpty; k = ks.head; l <- ks.tail) {
	  if (k == l.compl) return true 
	}
	return false
      }

    /**
     * Simplify this by exhaustive demodulation of its clause literals by the CSs,
     * removal of trivial equations and tautology check.
     */
    def demodulate(CSs: Seq[(Eqn,Set[Int])]):(OClause,Option[Set[Int]]) = {

      // Simplify lits and collect the result
      // The simplified literals
      var litsSimplified = List[Lit]()
      // The relevant context literals for the simplifications
      var litsIdxRelevant = Set[Int]()
      var litsSimplifiedF = false
      for (i <- (0 until C.length).reverse) {
	val (litSimplified, litIdxRelevant) = C(i).demodulate(CSs)
	litIdxRelevant match {
	  case None => () // nothing to update
	  case Some(idxs) => {
	    litsIdxRelevant ++= idxs
	    litsSimplifiedF = true
	  }
	}
	// trivial negative equations can be ignored when building up the
	// new clause
	if (litSimplified.isTrivialNeg)
	  litsSimplifiedF = true
	else 
	  litsSimplified ::= litSimplified
      }

      if (!litsSimplifiedF)
	// don't bother making a new OClause
	(this, None)
      else { 
	val thisSimplified = OClause(litsSimplified)
	if (thisSimplified.isTautology) 
	  throw new Redundant()
	else
	  (thisSimplified, Some(litsIdxRelevant))
      }
    }

    override def toString = lits.toMyString("□",""," ∨ ","")
  }
  
  // companion object
  object OClause {
    def apply(lits: Lit*) = new OClause(lits.toList)
  }


  /**
   * Context restriction
   */
  case class Restriction(eqns: List[Eqn]) extends Expression[Restriction] {

    // Mixin Expression
    lazy val vars = eqns.vars
    lazy val rvars = eqns.rvars
    lazy val params = Set[Param]() // parameters can occur in constraints only
    lazy val freeBGConsts = Set[FreeBGConst]() // parameters can occur in constraints only

    def applySubst(sigma: Subst) = Restriction(sigma(eqns))
    // mgus don't need to be defined
    def mgus(that: Restriction) = List[Subst]()
    def matchers(that: Restriction, gammas: List[Subst]) = 
      if (length != that.length) 
	List()
      else
	Expression.matchers(eqns, that.eqns, gammas)

    // the list of negative literals built from eqns 
    lazy val compl = eqns map { Lit(false,_) }

    val depth = if (eqns.isEmpty) 0 else (eqns map { _.depth }).max

    def isEmpty = eqns.isEmpty

    lazy val length = eqns.length

    override def toString = eqns.toMyString("∅","{",", ","}")

    /**
     * A Restriction is redundant if it contains an equation s=t with
     * a larger side that is reducible by an ordered unit clause.
     * 
     */
    def isReducible(CSs: Seq[Eqn]) = {
      // Assume that the equations in CSs are ordered.

      def isMatchableFromCSsEqns(t: Term):Boolean = 
      // Is there a term in CSsEqnsLhs that can be matched to t?
      // Could be improved - coarse approximation currently.
	t match { 
	  case Var(_,_) => false 
	  case FunTerm(_,args) => 
	    (CSs exists { _.lhs >~ t }) || 
	    (args exists { isMatchableFromCSsEqns(_) })
	}

      CSs exists { E => 
	// We check if a proper subterm of the lhs of 
	// E can be demodulated by an ordered equation in CSs
	(E.lhs match  { 
	  case FunTerm(_,args) => 
	    args exists { isMatchableFromCSsEqns(_) }
	  case _ => false
	})
      }
    }

    /**
     * Simplify a Restriction by context literals.
     * Returns the pair of the simplified restriction and the sets of idx's of the
     * relevant context literals, or None if simplification does not apply.
     * May throw a Redundant-exception 
     */
    def simplify(clits: Seq[CLit]):(Restriction,Option[Set[Int]]) = {
      // trivial equations can never be instantiated
      // into an *ordered* equation.
      if (eqns exists { _.isTrivial }) throw new Redundant()

      // Context-Subsume:
      if (compl exists { _ iin clits }) throw new Redundant()


      // Experimental:
      // the cecks below are possibly not worth the effort.
      // The important case when a universal context literal is used for
      // superposition is covered anyway (cf. infSup in Clauses)
      // return (this,None)

      // Context-Simp:
      var newRlits = List[Eqn]()
      var idxRelevant = Set[Int]()
      for (e <- eqns) {
	// See if e is subsumed by a universal literal.
	// Notice we cannot use a parametric literal for that.
	// Removing a literal is a soundness issue. No problem here, though.
	val Kcand = clits find { K => K.kind == UU && 
			              K.isPositive && K.eqn >~ e }
	Kcand match {
	  // e is not subsumed - keep it
	  case None => newRlits ::= e
	  // e is subsumed - update index
	  case Some(k) => idxRelevant += k.idx
	}
      }
      if (idxRelevant.isEmpty)
	// don't bother constructing a new Restriction
	(this,None)
      else 
	// construct the result
	(Restriction(newRlits), Some(idxRelevant))
    }
  }

  object Restriction {
    def apply(eqns: Eqn*) = new Restriction(eqns.toList)
  }


  /**
   * Constraint
   * Elements in fs are implicitly conjoined
   */

    case class Constraint(fs: List[Formula]) extends Expression[Constraint] {
    
    lazy val length = fs.length
   
    // Mixin Expression
    lazy val vars = fs.vars
    lazy val rvars = fs.rvars
    lazy val params = fs.params
    lazy val freeBGConsts = fs.freeBGConsts

    def applySubst(sigma: Subst) = Constraint(sigma(fs))
    // mgus don't need to be defined
    def mgus(that: Constraint) = List[Subst]()
    def matchers(that: Constraint, gammas: List[Subst]) = 
      if (length != that.length) 
	List()
      else
	Expression.matchers(fs, that.fs, gammas)

    def isEmpty = fs.isEmpty

    override def toString = if (length == 1) fs.head.toString else fs.toMyString("⊤","("," ∧ ",")")
  }

  object Constraint {
    def apply(fs: Formula*) = new Constraint(fs.toList)
  }


}
