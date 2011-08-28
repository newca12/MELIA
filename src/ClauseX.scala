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

object ClauseX {

  import Term._
  import Subst._
  import Eqn._
  import Expression._
  import Predefined._
  import Literal._
  import Misc._
  import Clauses._
  import Type._
  import Inference._
  import BGContext._
  import Flags._
  import Signature._
  import collection.mutable.{Set => MSet}


  /**
   * ClauseX: Clauses with some additional information attached:
   * - openClausal: the list of open clausal inferences still to be applied to this.
   * - PUs: for each usable literal in C the list of partial unifiers with
   *   context literals in State.Lambda.
   * - CUIs: a CUISet representing the context unifier instances (CUIs) of D.
   *   Applies only if all literals of C are usable.
   *
   * Todo: the description of the Invariants below is ot up to date.
   * It misses all invariants that have to do with background reasoning.
   * 
   * Invariants:
   * (1) openClausal contains all clausal inferences that involve literals from
   *     State.Lambda.
   * (2) PUs is in sync with State.Lambda (must use ExtendCUIs to preserve it, though)
   * (3) For each CUI, the information which literal is contradictory with
   *     State.Lambda is in sync with State.Lambda.
   * (4) (a) CUIs does not contain a CUI that is non-productive wrt State.Lambda,
   *     (Currently by a cheaper pre-test),
   *     and (b) CUIs does not contain two variants of the same CUI.

   * These invariants are to established by calling initInvariants() after
   * a ClauseX has been created time, and are to be preserved
   * by calling updateInvariants(K) after a context literal K as
   * been added to State.Lambda.
   *
   * The parameters:
   * - D: the clause component
   * - nr: a unique number identifying this
   * - the set of Clausal Inferences that are potentially applicable to this.
   *   A superset of those needed for fairness
   * - PUs: the partial unifiers, i.e. the individual unifiers of the literals
   *   in C with all context literals in State.Lambda.
   *   The algorithm is the one of the "Implementing the Model Evolution Calculus".
   * - CUIs: a list of CUIs, where CUI(Dsigma, forAssertOnly) represents the
   *   substitution instance sigma(D), where D = C u -R, when all literals in C are usable.
   *   C could be empty.
   */


  class RedundantCUI extends Exception

  class ClauseX(val D: Clause, 
		val openClausal: MSet[ClausalInference],
		val PUs: Array[List[Subst]],
		var CUIs: List[CUI]) extends Clause(D.nr, D.C, D.R, D.c, D.idxRelevant, D.doc) {

    def this(D: Clause) {
      this(D, MSet(), new Array(D.C.length), null)
    }

    // Initialize the list of open clausal inferences.
    // It is to be called explicitly, not during object creation itself,
    // because sometimes we do not want that. Specifically, when restoring 
    // a cloned version of a ClauseX we get this list from the clone, not.
    // Similarly for other init... methods in other classes.
    def initOpenClausal() {

      assume(openClausal.isEmpty, { println("initOpenClausal: openClausal is not empty") })
      // Usable negative proper equations are to be paired with X=X.
      // We must retrieve X=X of the appropriate type in State.Lambda
      for (i <- iUsable;
	   if ((!C(i).isPositive) && 
	       (C(i).eqn.typ != OType) 
	       // We do it also for background types, but make sure
	       // we use reflexivity only for simple substitutions
	       // (Sigma.FGTypes contains C(i).eqn.typ)
	       // (C(i).eqn.typ != State.BGType)
	     ))
	openClausal += (new ExtCUIs(i, State.getXeqXLit(C(i).eqn.typ)) {
	                  val weight = D.weight
		          val priority = 5
		        })
      // Establish invariant (1)
      updateOpen(State.Lambda)
    }
    
    // Update the openClausal list of this by adding to open all potential 
    // Clausal inferences with K. 
    // Recall that inferences with X=X have been added above by initOpenClausal,
    // if applicable.
    def updateOpen(clits: Seq[CLit]) {
      // println("==> UpdateOpen: " + this + " with " + clits)

      def rAdjust(p: Int) = math.max((p - (R.length.toFloat / p)).toInt, 0)

      // Update the open list of this with the inferences that involve K.
      // (Recall that ExtCUI inferences with negative selected literals have been
      //  added at creation time.)
      def doUpdateOpen(K: CLit) {
	// println("doUpdateOpen: " + this + ", where K = " + K)
	if (K.isAssertLit) {
	  // ExtCUIs with Assert - makes only sense if all literals are selected
	  // todo: more fine-grained analysis
	  if (Flags.negAssert.value != "off" && allUsable) 
	    for (i <- iUsable;
		 if (!C(i).isPositive))
	      if ( (Flags.negAssert.value == "all") ||
		   (Flags.negAssert.value == "eq" && C(i).eqn.typ != OType) ||
		   (Flags.negAssert.value == "non-eq" && C(i).eqn.typ == OType) )
		openClausal += new ExtCUIs(i, K) {
			      val weight = D.weight
			      val priority = if (allUsable) 10 else 3
			      // val weight = math.max(D.weight,K.depth)
			      // val priority = rAdjust(if (allUsable) 10 else 3)
			      }

	} else if (K.isNegVLit) {
	  // K is negative and a pseudo literal.
	  // Add CUI computation with K for all positive literals
	  for (i <- iUsable;
	       if (C(i).isPositive))
	    openClausal += new ExtCUIs(i, K)  {
			      val weight = D.weight
			      val priority = if (allUsable) 10 else 3
			      // val weight = math.max(D.weight,K.depth)
			      //  val priority = rAdjust(if (allUsable) 10 else 3)
			       }
	} else if (K.isPositive) {
	    // Proper equation - add superposition inferences
	  if (K.eqn.typ != OType) {
	    if ((!K.eqn.isTrivial)) {
	      for (i <- iUsable) {
		if (C(i).isPositive)
		  openClausal += new InfSupPos(i, K) { 
		                    val weight = D.weight
				    val priority = if (allUsable) 8 else 3
				    // val weight = math.max(D.weight,K.depth)
				    // val priority = rAdjust(if (K.eqn.isOrdered) 8 else 4)
				}
		else
		  openClausal += new InfSupNeg(i, K) { 
		                    val weight = D.weight
				    val priority = if (allUsable) 9 else 6
				    // val weight = math.max(D.weight,K.depth)
				    // val priority = rAdjust(if (K.eqn.isOrdered) 9 else 6)
				}
	      }
	    }
	  } else {
	    // K is a predicate - add ExtCUI inferences
	      // println("==> here")
	      for (i <- iUsable; 
		   if ((!C(i).isPositive) && 
		       C(i).eqn.typ == OType && 
		       C(i).eqn.samePredSym(K.eqn))) // and hence K is OType
		openClausal += new ExtCUIs(i, K) {
		              val weight = D.weight
			      val priority = if (allUsable) 10 else 3
			      // val weight = math.max(D.weight,K.depth)
			      // val priority = rAdjust(if (allUsable) 10 else 3)
			      }
	  }
	} else {
	  // K is negative -- add ExtCUIs inferences
	  if (K.eqn.typ == OType) 
	    for (i <- iUsable; 
		 if (C(i).isPositive && 
		     C(i).eqn.typ == OType && 
		     C(i).eqn.samePredSym(K.eqn)))
	      openClausal += new ExtCUIs(i, K) {
			      val weight = D.weight
			      val priority = if (allUsable) 10 else 3
			      // val weight = math.max(D.weight,K.depth)
			      // val priority = rAdjust(if (allUsable) 10 else 3)
			      }
	  else // K is not a predicative atom
	    for (i <- iUsable; 
		 if (C(i).isPositive && 
		     (C(i).eqn.typ == K.eqn.typ)))
	      openClausal += new ExtCUIs(i, K) {
			      val weight = D.weight
			      val priority = if (allUsable) 10 else 3
			      // val weight = math.max(D.weight,K.depth)
			      // val priority = rAdjust(if (allUsable) 10 else 3)
			      }
	}
      }
      // Body of updateOpen
      for (K <- clits;
	   // Skolem literals are used only for
	   // pairing with isolated literals in CUIs, never for clausal inferences.
	   if K.kind != SS)
	doUpdateOpen(K)
    }
    def updateOpen(K: CLit) { updateOpen(List(K)) }


    // Typically used to remove an inference after it has been carried out.
    def removeOpen(inf: ClausalInference) {
      openClausal -= inf
    }

    // Preserve invariants (1), (3) and (4) after State.Lambda has been extended with K
    def updateInvariants(K: CLit) {
      updateCUIs(K) // Invariants (3) -(4)
      updateOpen(K) // Invariant (1)
    }

    // When a new rigid variable rv is introduced the CUIs need to be extended
    // by all instances of this that involve rv
    def updateInvariants(rv: RVar) {
      extendCUIs(rv)
    }

    // Preserve invariants (1)-(4) after this has been created
    def initInvariants() {
      initCUIs()
      initOpenClausal()
    }

    override def clone() = new ClauseX(D, openClausal.clone(), PUs.clone(), CUIs map { _.clone() })

    override def toString = super.toString
    
    def show() {
      println(D.toString)
      // println("iIsolatedCLits: " + D.iIsolatedCLits.toMyString("{",",","}"))
      println("   Open clausal inferences: " + openClausal.toList.toMyString("{",",","}"))
      println("   PUs:")
      showPUs()
      println("   CUIs:")
      showCUIs()
    }

    /*
     * CUI related stuff
     */
  
    def initCUIs() {
      // Assumes that initDIs has been called before
      assume(CUIs == null, { println("initCUIs: CUIs is not null") })
      // assume(PUs.isEmpty, { println("initCUIs: PUs is not empty") })
      // PUs = new Array[List[Subst]](C.length)
      for(i <- 0 until C.length) PUs(i) = List()

      // The list of CUIs for this D if allUsable
      CUIs = List()
      if (C.isEmpty) {
	// (allUsable is implied trivially.)
	// Extend below cannot compute CUIs when C is empty,
	// as extend needs at least one literal in C.
	// (In fact, extend will never be called then.)
	// Hence we need to take care of this case explicitly:
	// if C is empty there is exactly one context unifier, 
	// the empty substitution, hence "Dsigma = D".
	// Notice that invariant (2) holds trivially.
	for (gamma <- Gamma.DIsubsts(D.c);
	     dGamma = gamma(D);
	     // checked by DIsubsts
	     // if Gamma isConsistentWith dGamma.c;
	     newCUI = new CUI(dGamma, false); 
	     if !newCUI.isNonProductive(State.Lambda))  {
	       // Invariant (3) is maintained for newCUI at creation time.
	       // But still need to check for invariant (4a), as (4b) is trivial.
	       try {
		 newCUI.initIdxContradictoryLits()
		 CUIs ::= newCUI
	       } catch {
		 case _:RedundantCUI => ()
	       }
	     }
      }
    }
  
    /**
     * updateCUIs(K): preserve invariants (3) and (4) after the literal K has been
     * added to State.Lambda.
     */
  
    def updateCUIs(K: CLit) {
      // Invariant (4b) is not affected by extension of State.Lambda with K
      var CUIsChecked = List[CUI]()
      for (CUI <- CUIs) {
	// Invariant (4a)
	if (! CUI.isNonProductive(List(K))) {
	  // Invariant (3)
	  try {
	    CUI.updateIdxContradictoryLits(List(K)) 
	    CUIsChecked ::= CUI 
	  } catch {
	    case _:RedundantCUI => ()
	  }
	} 
      }
      CUIs = CUIsChecked
    }
    
    /**
     * CUIC: the list of non-usable literals C, i.e. the uninstantiated clause part
     * of the CUI. Stricly speaking it is only needed if not all literals are usable.
     * because only then then the CUIs are clauses with non-empty C.
     */

    lazy val CUIC = (for (i <- List.range(0,C.length);
		     if !(D.iUsable contains i)) yield C(i))

   /**
     * CUIR: R extended with the usable literals of C, i.e. the uninstantiated
     * restriction part of the CUI.
     * As above, it is only needed if not all literals are usable.
     * because only then then the CUIs are clauses with non-empty C.
     * Moving a usable literal L from C into R this way makes only sense if L is negative,
     * otherwise L would flip its sign, which cannot be expressed as Restriction literal.
     * However, CUIR will only be used if this is the case, i.e., when all usable 
     * literals are negative. If also positive literals are usable then *all* literals
     * are usable (this is made sure by the selection function) and hence CUIR will
     * not be used.
     */

    lazy val CUIR = (for (i <- D.iUsable; 
		     // Only need to move the predEqns from C into the restriction
		     // part, as the equations pair with X=X.
		     if C(i).eqn.typ == OType) yield C(i).eqn) ::: R.eqns

    /**
     * extendCUIs(iL, K): extend the PUs of C(iL) using K and return the resulting
     * set of clauses if not all literals are usable.
     * If all literals are usable, the CUIs are extended instead and the
     * resulting clause set is empty.
     * Assumptions: C cannot be empty, and iL must be selected.
     * Caller must have assured that.
     * When called repeatedly, with all literals in State.Lambda,
     * invariants (2), (3) and (4) are preserved.
     */

    def extendCUIs(iL: Int, K: CLit) = {
      // Context unifier instances are not computed from Skolem context literals.
      // Assume the caller has assured that.
    
      // The new PUs involving K
      val newPUs = C(iL) mgus K.compl.fresh
      // Build the cross products of all PUs,
      // where newPUs must be chosen instead of the old PUs(i), to be a new one
    
      var newCUs = List(Subst()) // the list of new context unifiers
      if (!newPUs.isEmpty) {
	// So there is a chance to get a new CUI at all
	for (i <- D.iUsable) {
	  if (i == iL) 
	    // fix the new PU for this crossproduct
	    newCUs = combineSubst(newCUs, newPUs)
	  else
	    // take the stack of existing PUs
	    newCUs = combineSubst(newCUs, PUs(i))
	}
	// newPUs becomes old, for next time
	PUs(iL) :::= newPUs
      }
      
      // Distinguish whether all literals are usable or not.
      // If yes, add to CUIs the new context unifier instances,
      // if no, return the new clauses.
      // (In the yes case we could return detouched empty clauses, but keeping
      // the instances with the clause is better, because if the clause is deleted,
      // so are the instances.)
      if (D.allUsable) {
	for (sigma <- newCUs; 
	     if sigma.isSimple(D.c);
	     dSigma = sigma(D);
	     gamma <- Gamma.DIsubsts(dSigma.c);
	     dSigmaGamma = gamma(dSigma);
	     newCUI = new CUI(dSigmaGamma, sigma.actsOn(AAVar)); // may throw Closing
	     // we don't need variants of existing CUIs and we don't need 
	     // persistently non-productive ones
	     if (! (CUIs exists { _ ~ newCUI })) &&  // Invariant (4b)
	        (! newCUI.isNonProductive(State.Lambda))  // Invariant (4a)
	   ) {
	  try {
	    // Invariant (3)
	    newCUI.initIdxContradictoryLits()
	    CUIs ::= newCUI
	  } catch {
	    case _:RedundantCUI => ()
	  }
	}
	// No new clausal results in ths case
	List()
      } else {
	// Return new clauses, for the simple sigmas
	(newCUs filter { _.isSimple(D.c) }) map { sigma => 
	  Clause(clauseCtr.next(), 
		 OClause(sigma(CUIC)), 
		 Restriction(sigma(CUIR)), 
		 sigma(D.c), 
		 D.idxRelevant, "CUI(" + nr + ")") }
      }
    }
  
    // Extend the list of CUIs after a new rigid variable has been introduced.
    // Has to go through all context unfiers extended by the domain substitutions
    // for the resulting instance.
    // Applies also when C is empty
    def extendCUIs(rv: RVar) {
      if (D.allUsable) {
	// we need to combine the context unifiers with the domain substitution
	// that involve rv.
	// println("xxx extendCUIs " + this)
	var CUs = List(Subst()) // the list of all context unifiers
	for (i <- 0 until C.length) {
	  CUs = combineSubst(CUs, PUs(i))
	}
	for (sigma <- CUs; 
	     if sigma.isSimple(D.c);
	     dSigma = sigma(D);
	     gamma <- Gamma.DIsubsts(dSigma.c, rv);
	     dSigmaGamma = gamma(dSigma);
	     newCUI = new CUI(dSigmaGamma, sigma.actsOn(AAVar)); // may throw Closing
	     // we don't need variants of existing CUIs and we don't need 
	     // persistently non-productive ones
	     if (! (CUIs exists { _ ~ newCUI })) &&  // Invariant (4b)
	        (! newCUI.isNonProductive(State.Lambda))  // Invariant (4a)
	   ) {
	  try {
	    // Invariant (3)
	    newCUI.initIdxContradictoryLits()
	    CUIs ::= newCUI
	  } catch {
	    case _:RedundantCUI => ()
	  }
	}
      }
    }


    // Return the open Split inference with the CUIs
    def openSplits() = 
      for (cui <- CUIs;
	   // cui.openSplit() returns Option[Inference]
	   openFromCUI <- cui.openSplit()) yield openFromCUI
  
    // Execute a given clausal inference to this.
    def execClausalInf(inf: ClausalInference) = {
      // We don't need the inference any more in the open list as we're about 
      // to execute it.
      removeOpen(inf)
      inf match {
	  case InfSupNeg(iL, k) => infSup(iL, k)
	  case InfSupPos(iL, k) => infSup(iL, k)
	  case ExtCUIs(iL, k)   => extendCUIs(iL, k)
      }
    }

    def showPUs() {
      for(i <- 0 until C.length) 
	if (!PUs(i).isEmpty)
	  println("   " + i + ":" + PUs(i))
    }

    def showCUIs() {
      for (CUI <- CUIs) {
	println("   " + CUI.toString + ":" + CUI.openSplitFailSafe())
      }
    }
  }


  /**
   * CUI(Dsigma, forAssertOnly) represents the substitution instance sigma(D), where D = C u -R,
   * and all literals in C are usable. C could be empty.
   * At creation time, only invariant (3) is established.
   * Invariant (4) has to be maintained separately, because it involves deletion of CUIs.
   * 
   */

  class CUI(val Dsigma: Clause, 
	    val forAssertOnly: Boolean,
	    val idxContradictoryLits: Array[Int]) {

    def Csigma = Dsigma.C
    def Rsigma = Dsigma.R
    val asOClause = OClause(Csigma.lits ::: Rsigma.compl) // As an ordinary clause

    def this(Dsigma: Clause, forAssertOnly: Boolean) {
      this(Dsigma, forAssertOnly, new Array(Dsigma.C.length + Dsigma.R.length))
    }

    // idxContradictoryLits: 
    // The idxes of the context literals from State.Lambda that pair with literals
    // in asOClause for being contradictory.

    def initIdxContradictoryLits() {
      // Notice that idxContradictoryLits grows monotonically with State.Lambda
      // idxContradictoryLits = new Array[Int](asOClause.length)  
      for (i <- 0 until asOClause.length) 
	// -1 means not contradictory, otherwise the idx of the literal in Lambda
	// that the clause literal is contradictory with
	idxContradictoryLits(i) = -1 
    
      // Maintain invariant (3)
      updateIdxContradictoryLits(State.Lambda)
    }
    
    /**
     * Update the array of contradictory literals by checking against
     * a given list of context literals. 
     */
    def updateIdxContradictoryLits(clits: Seq[CLit]) {
      for (i <- (0 until asOClause.length); 
	   // Check only needed if C(i) is not known to be contradictory yet
	   if idxContradictoryLits(i) == -1;
	   // Find a (one) literal in clits that is contradictory with C(i)
	   // Notice that "find" returns an Option[CLit].
	   // (Option types are Iterables - the power of Scala at work!)
	   k <- if (asOClause.iIsolatedLits contains i) 
	            clits find { _ isContradictory asOClause(i)^UU }
		else
		  clits find { _ isContradictory asOClause(i)^PP } ) 
	idxContradictoryLits(i) = k.idx

      // Check if C is closing. 
      if ((idxContradictoryLits forall (_ != -1)) //&& 
	  // (Gamma isConsistentWithPre Dsigma.c) 
	) {
	    try {
	      Gamma ++= Dsigma.c
	      throw new Closing(idxContradictoryLits.toSet, Dsigma)
	    } catch {
	      case _:BGContextExtensionFail => 
		// Can't do anything, but this CUI is redundant
		throw new RedundantCUI
	    }
	  }
    }

    def ~ (that: CUI) = 
      // No! must take theory part into account, which could be skipped otherwise
      // asOClause ~ that.asOClause &&
      Dsigma ~ that.Dsigma &&
      forAssertOnly == that.forAssertOnly // &&

    /**
     * Return a (don't care nondeterministically selected)
     * possible split inference with this, or None, if no (productive) one exists.
     * Does NOT check for consistency with the background context. It is expensive
     * so we don't do it lightly, the caller is responsible for ensuring consistency
     * if the split is to be carried out.
     */
    def openSplit():Option[InfSplit] = {
      // todo: it is possible if a CUI is not productive we can delete
      // it. Rationale: should it become productive later on again, then
      // it will be recomputed anyway
      // Same if its constraint is not consistent with Gamma
      if (! isProductive(State.Lambda))
	return None
      
      // First see if we can get an implied literal or a decision literal.
      // Not all literals can be contradictory as then the CUI would be closing,
      // which would have been detected earlier.
      val status = 
	if ((idxContradictoryLits count { _ != -1 }) == asOClause.length-1)
	  II // all but one contradictory - Implied literal
	else
	  DD // Decision literal

      // If this is forAssertOnly we must have status == II, by definition of Assert
      if (forAssertOnly && status != II)
	return None
      
      // A decision literal is never dependent on other context literals
      // as the splitting will be complementary. Implied literals depend
      // on the n-1 context literals used to derive them plus the relevant
      // context literals of the underlying clause 
      val idxRelevant = 
	if (status == II) 
	  // collect the relevant literal indexes
	  // todo: could implicitly factor equal literals
	  (idxContradictoryLits filter { _ != -1 }).toSet ++ Dsigma.idxRelevant
	else
	  Set[Int]()
      
      // Search for best split
      var best:Option[InfSplit] = None
      for (i <- 0 until asOClause.length;
	   if (idxContradictoryLits(i) == -1)) {
	     // Found one, potentially, still need to check that the complement
	     // is not contradictory, dependent on the type (we already know
	     // that the CUI literal itself is not contradictory with Lambda)
	     var inf:Option[InfSplit] = None
	     if (asOClause.iIsolatedLits contains i) {
	       val Lc = asOClause(i).compl.sko() ^ SS
	       if (!(Lc isContradictory State.Lambda)) {
		 inf = Some(InfSplit(asOClause(i), Dsigma.c, UU, status, idxRelevant))
		 // if status is II we can stop here
		 if (status == II) {
		   if (inf.get.isOptimalSplit) throw new OptimalSplit(inf.get) else return inf
		 }
	       }
	     } else { 
	       // non-isolated literal
	       if (! forAssertOnly) {
		 // Assert literal shall only be Universal
		 val Lc = asOClause(i).compl ^ PP
		 if (!(Lc isContradictory State.Lambda))
		   inf = Some(InfSplit(asOClause(i), Dsigma.c, PP, status, idxRelevant))
		 // if status is II we can stop here
		 if (status == II) {
		   if (inf.get.isOptimalSplit) throw new OptimalSplit(inf.get) else return inf
		 }
	       }
	     }
	     // See if we found something better
	     if (inf != None && (best == None || (inf.get betterThan best.get))) {
	       best = inf
	       if (best.get.isOptimalSplit) throw new OptimalSplit(best.get)
	     }
	   }
      return best
    }
    
    def openSplitFailSafe():Option[InfSplit] =
      try {
	openSplit()
      } catch {
	case OptimalSplit(inf) => Some(inf)
      }
    
    /**
     * Is this not productive in a context *and all extensions of that context*?
     * If, so the CUI can safely be removed.
     */ 
    def isNonProductive(clits: Seq[CLit]):Boolean = {
      // print("redundancy test: " + this + " -- " + clits + ": ")
      for (i <- 0 until asOClause.length) 
	if (asOClause.iIsolatedLits contains i) {
	  // Only a universal literal makes the Split with isolated literals redundant
	  if (asOClause(i) uin clits) {
	    // println("yes")
	    return true
	  }
	} else {
	  // non-isolated literals. Check for iin is possible
	  if (asOClause(i) iin clits) {
	    // println("yes")
	    return true
	  }
	}
      // println("no")
      return false
    }
    

    /**
     * productive context unifier test, Straight from the definition.
     * Productive context unifiers are defined for positive clauses only,
     * the caller must ensure that.
     * Note: everything seems OK to apply the very same definition also
     * for non-positive clauses. (todo: double check that.)
     * Such cases pop up without selection function.
     */
    def isProductive(Lambda: Seq[CLit]):Boolean = 
      (Rsigma.eqns forall { Lambda produces Lit(true,_) }) &&
       ( (0 until Csigma.length) forall { i =>
	 if ( (  Csigma(i).isPositive  && (  Lambda produces Csigma(i))) || 
	      (!(Csigma(i).isPositive) && (!(Lambda produces Csigma(i).compl))) )
	   (Dsigma.iIsolatedCLits contains i) && !(Csigma(i) uin Lambda)
         else 
	   true 
       })

    override def clone() = new CUI(Dsigma, forAssertOnly, idxContradictoryLits.clone())
    
    override def toString = 
      asOClause.toString + ":" +
    idxContradictoryLits.toList.toMyString("[", ",", "]")
  }

}
