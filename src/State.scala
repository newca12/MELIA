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

object State {

  import Term._
  import Eqn._
  import Literal._
  import Misc._
  import Type._
  import Clauses._
  // import CUIs._
  import ClauseX._
  import Flags._
  import Inference._
  import Integers._
  import Formula._
  import BGContext._
  import Signature._
  import Predefined._
  import Cooper._
  import collection.mutable.ArrayBuffer // for contexts; better use Vector?
  import collection.mutable.ListBuffer // for clause sets


  // FAIL is thrown whenever a state cannot be expanded to a model
  case class FAIL() extends Exception {}

  // REFUTATION is thrown whenever a FAILed state represents a refutation
  // The difference is with the background constraint. FAILed derivations may make
  // unsound assumptions about FreeBGConsts and Params, REFUTATIONs not.
  case class REFUTATION() extends Exception {}


  /**
   * The State represents the current context and the current clause set.
   * There is just *one* state, not a a class State that we draw an instance
   * of. The reason is to be absolutely sure that the "the global context"
   * is uniquely determined, viz., Lambda as defined below.
   */

  // The current clause set
  var Phi = new ArrayBuffer[ClauseX]()

  // The current foreground context
  var Lambda = new ArrayBuffer[CLitX]()

  // The global background context Gamma is set in BGContext.scala

  // The current weight bound
  var weightBound = 1 

  // The number of decision literals to backtrack to
  var decisionLevels = 0

  // The last rigid variable added to rhe background context
  var lastRVarAdded:Option[RVar] = None

  // Starts a completely new refutation, from a set Gamma
  // Throws FAIL if a refutation has been found.
  def MEET(clauses: List[Clause], wb: Int) {
    weightBound = wb
    decisionLevels = 0
    Phi = new ArrayBuffer[ClauseX]()
    Lambda = new ArrayBuffer[CLitX]()

    // Every context contains a pseudo literal
    this += (NegVLit, PP, II, Set(), None)
    // And an assert literal
    this += (AssertLit, PP, II, Set(), None)
  
    // Every context contains X=X.
    // We need to add it for every foreground type.
    for (typ <- Sigma.types; // typ <- Sigma.FGTypes;
         if typ != OType && typ != TType) {
       this += (Lit(true,Eqn(Var("X"),Var("X"),typ)), UU, II, Set(), None)
    }
    try {
      // Only *simplified* clauses are checked for being Tautologies, hence here
      State ++= (clauses filter { ! _.C.isTautology }, true)
      // State ++= (clauses, true)
    } catch {
      // Input clauses set is simplifable to the empty clause 
      // case FAIL() =>     State.exhaust()
      case Closing(idxRelevant,d) => {
      	printlnDebug(Closing(idxRelevant,d).toString)
      	printlnVerbose("Input clause set simplifies to the empty clause")
      	throw new FAIL()
      }
    }
    State.exhaust()
  }

  // throws REFUTATION (or not)
  def MEETOuter(clauses: List[Clause], wb: Int) {

    def initRestrict() {
      // Throw in a rigid variables to start with.
      // Must supply at least one in Gamma.openInfRestrict so that exhaust
      // has a chance to start its loop
      lastRVarAdded = None
      val rv = RVar("$e_" + RVarCounter.next()) 
      Gamma.openInfRestrict ::= InfRestrict(rv)
    }

    Gamma = new BGContext
    if (!Sigma.BGTypes.isEmpty) {
      // We have a background theory
      initRestrict()
    }

    // When we can stop building derivations because of a definitive result
    var haveResult = false
    
    // The BG assumptions to start a derivation with. Will be strengthened in each iteration
    var assumptions:Formula = TrueAtom 

    if (! verbose) println("Proving ...")

    while (! haveResult) {

      if (verbose) {
	println("Starting a new derivation")
	println("=========================")
	Gamma.show()
      }

      try {
	MEET(clauses, wb)
	// If this line is reached we have satisfiability,
	// However, right now, with theories the derivation does not stop as fresh rigid variables
	// are added repeatedly. (Something to work on.)
	haveResult = true
      } catch {
	case FAIL() => {
	  // Must see if in the theory-case Gamma does not make assumptions about parameters
	  // and free BG constants
	  val allformulasN = Gamma.fs ::: (Gamma.eqnsAsFormulas flatMap { Integers.normalize(_) })
	  if (allformulasN.params.isEmpty && allformulasN.freeBGConsts.isEmpty) {
	    // No assumptions!
	    // Should eqns make assumptions on parameters
	    if (verbose && !Sigma.BGTypes.isEmpty) 
	      println("Refutation found under no (further) assumptions")
	    throw new REFUTATION()
	  }
	  // Otherwise eliminate all rigid variables and start again
	  // However, must take eqns into consideration
	  val currentAssumptions = QE(allformulasN.rvars, allformulasN)
	  if (verbose) {
	    println("Current refutation makes these assumptions:")
	    for (f <- currentAssumptions) 
	      println(f)
	  }
	  // update the assumptions to exlude the current one
	  assumptions = 
	    And(assumptions,
		Neg(currentAssumptions.to(TrueAtom, And))).reduceInnermost(elimTrivial)
	  // Prepare the next derivation
	  Gamma = new BGContext
	  initRestrict()
	  try { 
	    Gamma += assumptions
	    // If we come here Gamma could be consistently
	    printlnVerbose("Assumptions successfully strengthened for next derivation")
	  } catch {
	    case _:BGContextExtensionFail => {
	      // That meas the current refutation has not added assumptions
	      printlnVerbose("Assumptions cannot be strengthened (all cases exhausted)")
	      throw new REFUTATION()
	    }
	  }
	}
      }
    }
  }

  /**
   * Adding a context literal K to the current Lambda, or
   * adding a clause D to Phi preserves these invariants:
   * (1): the invariants for ClauseXes are preserved (see ClauseX)
   * (2): all clauses are simplified wrt all context literals in Lambda
   * (3): all clauses are mutually simplified
   */
  
  /**
   * += :  Extend Lambda by a CLitX based on the information given.
   * L: the literal to be added
   * kind: UU or PP
   * status: DD or II
   * savedPhi: a saved clause set, only used when status == DD
   */

  def += (L: Lit, kind: Kind, status: CtxtStatus, idxRelevant: Set[Int], savedPhi: Option[SavedPhi]) {
    // Build the context literal
    val K = L ^ (kind, status, Lambda.length)

    // Add it as an extended context literal to Lambda.
    Lambda += new CLitX(K, idxRelevant, savedPhi)

    if (status == DD)
      decisionLevels += 1
    printlnVerbose(levelString + K)

    // Preserve invariant (2) by simplifying every clause in Phi with K.

    // The simplified versions of the clauses in Phi (note: Clause, not ClauseX)
    var simplifieds = List[Clause]()
    // The clauses in Phi minus the simplified ones
    val newPhi = new ArrayBuffer[ClauseX]()
    // Notice  clauseIndex is currently not usable. Just to be sure...
    // clauseIndex = null
    for (phi <- Phi) 
      try {
	val phiSimplified = phi.simplifyR(K) 
	if (phiSimplified.nr != phi.nr) 
	  // Simplification applied
	  // Remember simplified version for later addition
	  simplifieds ::= phiSimplified
	else
	  // phi was not simplified - keep it
	  newPhi += phi
      } catch {
	// Nothing to do = just forget D
	case _:Redundant => () // printlnVerbose(levelString + "delete: " + phi)
      }
    Phi = newPhi

    // Add all the new simplified clauses to Phi.
    // This will preserve invariant (3) and also rebuild the index
    this ++= (simplifieds, true)

    // Preserve invariant (1).
    Phi foreach { _.updateInvariants(K) }
  }
  

  // Extend the background context by a formula f, which (should) restrict
  // the new rigid variable rv, which is to be included in the signature.
  // This is essentially the Restrict inference rule.
  def += (rv: RVar, f:Formula) {
    Gamma.declare(rv)
    // Caution: Gamm += f could throw an exception - to be caught be the caller
    Gamma += f
    Phi foreach { _.updateInvariants(rv) }
  }

  /**
   * += (D) : add a Clause D to Phi, preserving invariant (3).
   * 
   * Assume that D has been fully simplified wrt the context literals,
   * so that nothing remains to preserve invariant (2).
   * D has to be simplified before put into Phi as a ClauseX.
   * D's idxRelevant list is possibly non-empty, and simplification will
   * respect that.
   * 
   */
  def += (D: Clause, isRSimplified: Boolean) {
    // We maintain two sets of clauses and one selected clause 
    // with certain invariants:
    // Phi: all elements mutually simplified, including absence of variants
    // selectedSimplified: a clause from PhiC simplified by Phi
    // PhiC: no assumption
    // Populating PhiC with new clauses, the goal is to move all
    // clauses from PhiC to Phi via selected, always preserving the invariants
    // Step 1: populate PhiC with the clauses to be added
    // The restriction part of D is possibly not simplified, 
    // hence do that first.

    var PhiC = 
      if (isRSimplified)
	List(D)
      else
	try {
	  List(D.simplifyR(Lambda))
	} catch {
	  case _:Redundant => List() 
	}

    while (!PhiC.isEmpty) {
      // Step 2: Select a clause from PhiC and simplify by Phi, giving selectedSimp
      val selected = PhiC.head
      PhiC = PhiC.tail
      try {
	val selectedSimplified = selected.simplifyC(Phi) 
	// Step 3: move to PhiC the simplified versions of 
	// the clauses from Phi that are simplifiable by selectedSimplified.
	// However, if selectedSimplified is present in Phi as a variant we can forget it
	if (! (Phi exists { _ ~ selectedSimplified })) {
	  val newPhi = new ArrayBuffer[ClauseX]()
	  for (phi <- Phi) 
	    try { 
	      val phiSimplified = phi.simplifyC(selectedSimplified) 
	      if (phi.nr != phiSimplified.nr) {
		// simplification applied, move d to PhiC
		PhiC ::= phiSimplified
	      }
	      else 
		newPhi += phi // keep phi in Phi
	    } catch {
	      case _:Redundant => () 
	    }
	  // Went over Phi, have removed all simplifiables now
	  Phi = newPhi
	  // As a result, here no clause in Phi is simplifiable by selected.
	  // Together with the invariant for selected, Phi u { selectedSimplified }
	  // is mutually simplified. Hence we can move selectedSimplified to Phi,
	  // which preserves the invariant for Phi.
	  
	  printlnVerbose(levelString + selectedSimplified)
	
	  // We need to turn selectedSimplified into a ClauseX to add it to Phi.
	  // Invariant (1) is preserved at creation time.
	  val newphi = new ClauseX(selectedSimplified) 
	  newphi.initInvariants()
	  Phi += newphi
	}
      } catch {
	case _:Redundant => () 
      }
    }
  }

  def ++= (Ds: Seq[Clause], isRSimplified: Boolean) {
    Ds foreach { this += (_, isRSimplified) }
  }
  /**
  * backtrackToDD: Backtracks Lambda to the most recent relevant decision literal K,
  * if there is one, otherwise throws FAIL.
  * More precisely, K is removed from Lambda as well,
  * and the result is the pair (K,idxRelevant), where idxRelevant
  * are the context literals necessary to derive K, which are regressed back
  * from the given set, as usual.
  * Backtrack restores also the clause set Phi that was stored with K.
  * Notice that 'exhaust' saved the clause set exactly before K had been added 
  * to the context. On backtrack, thus, exactly the situation is being restored
  * at the time the Left Split was carried out.
  */
  
  def backtrackToDD(idxRelevant: Set[Int]):(CLitX, Set[Int]) = {
    
    // The accumulated relevant context literals as we regress upwards
    var accIdxRelevant = idxRelevant
    
    while (level > 0) {
      // The last element, the one we are about to skip or stop at
      if (Lambda(level).status == DD)
	decisionLevels -= 1
      if (accIdxRelevant contains level) {
	// Resolution-like union of the relevant indexes,
	// i.e. replace n by the relevant indexes to derive n.
	// accIdxRelevant ++= IdxRelevant(n)
	accIdxRelevant ++= Lambda(level).idxRelevant
	accIdxRelevant -= level
	if (Lambda(level).status == DD) {
	  // Found the decision literal to backtrack to
	  val KX = Lambda(level)
	  Lambda.trimEnd(1)
	  return(KX, accIdxRelevant)
	} 
	// else skipping over an implied literal (which is still relevant)
	// but nothing remains to be done
      }
      // All  action taken - back to the previous level
      Lambda.trimEnd(1)
    }
    // Have backtracked to level 0 
    throw new FAIL()
  }
  
  /**
   * Exhaust the given state under inference rule applications.
   * Throws FAIL if not successful.
   */
  
  def exhaust() {

    var selectedInfOpt = selectInf(Phi) 
    while (selectedInfOpt != None) {
      val selectedInf = selectedInfOpt.get

      // The selection of inferences is such that it selects non-redundant inferences
      // that fit the given weight bound. If the weight is larger than weightBound we
      // can be sure there is no inference below the weightBound.
      if ( (! ((! selectedInf.isInstanceOf[InfSplit]) ||
	       selectedInf.asInstanceOf[InfSplit].isOptimalSplit )) && 
	  selectedInf.weight > weightBound) {
	// We need to adjust the weight bound
	weightBound = selectedInf.weight
	printlnVerbose(levelString + "depth bound increased to " + weightBound)

	// To be more fair to the background reasoner throw in a new rigid variable
	// every now and then. Completely random strategy
	if ((weightBound % 4 == 0) && !Sigma.BGTypes.isEmpty) { 
	  // throw in another rigid variables 
	  val rv = RVar("$e_" + RVarCounter.next()) 
	  Gamma.openInfRestrict ::= InfRestrict(rv) 
	  // The inference will be picked up in the next round
	}
      }


      printlnDebug()
      printlnDebug("==== Main loop entry ====")
      if (Flags.debug.valueBoolean) show
      
      try {
	printlnDebug()
	printlnDebug("Selected inference: " + selectedInf)

	selectedInf match {
	  case InfRestrict(rv) => {
	    Gamma.removeOpenInfRestrict(InfRestrict(rv))
	    printlnVerbose("Adding a fresh rigid variable to the background context")
	    // constrain rv to be greater than the last rv added,
	    // for symmetry elimination
	    val cond = 
	      if (Flags.symmetryElimFlag.valueBoolean) {
		lastRVarAdded match {
		  case None => TrueAtom // no previous variable added
		  case Some(hrv) => Less(hrv, rv)
		}
	      } else TrueAtom
	    lastRVarAdded = Some(rv)
	    this += (rv, cond)
	  }
	  case ExecClausalInference(dx, inf) =>
	    this ++= (dx.execClausalInf(inf), false)
	  case InfSplit(k, c, kind, status, idxRelevant) => {
	    // If we extend with a decision literal we need to remember the current state.
	    // This must be done now, rather than after simplification, because
	    // simplification might depend on the literal added, thus not be justified when
	      // diving into the right branch of the split.
	    
	    // Left split
	    val currentPhiSavedOpt = 
	      if (status == DD) Some(new SavedPhi) else None

	    // Add the constraint to Gamma
	    // Assume it does not throw an exception,
	    // because the split was tested for consistency prior to being
	    // selected.
	    Gamma ++= c 

	    this += (k, kind, status, idxRelevant, currentPhiSavedOpt)
	    // Optional - add k as a unit clause to the current clause set.
	    val addAsUnitClause = kind == UU &&
	      (Flags.unitClause.value match {
		case "pos-eq" => k.isPositive && (k.eqn.typ != OType) && k.eqn.isOrdered
	        case "pos" => k.isPositive && k.eqn.isOrdered
	        case "neg" => !k.isPositive
	        case "all" => !k.isPositive || k.eqn.typ == OType || k.eqn.isOrdered
	        case "off" => false
	      })
	    if (addAsUnitClause) {
	      val cand = Clause(clauseCtr.next(),
				OClause(k), 
				Restriction(),
				Constraint(),
				// hack: there must be a better way
				// to get the index of k
				Set(Lambda.length-1), "Unit-Clause(" + k + ")")
	      // pre-test - applies quite often
	      if (! (Phi exists { cand.isSubsumed(_) }))
		  this += (cand, true)
	    }
	  }
	}
	// Select the next inference
	selectedInfOpt = selectInf(Phi)
	// selectedInfOpt could be None.
	// In this case the clause set is always satisfiable only if we have no background theories.
	// (For, the derivation might just not have had enough rigid variables to continue.)
	// Hence take care of that case
	if (selectedInfOpt == None && !Sigma.BGTypes.isEmpty) { 
	  // throw in another rigid variables 
	  val rv = RVar("$e_" + RVarCounter.next()) 
	  Gamma.openInfRestrict ::= InfRestrict(rv) // this is not redundant
	  // Pick it up
	  selectedInfOpt = selectInf(Phi)
	}
      } catch {
	case Closing(idxRelevant, d) => {
	  printlnDebug(Closing(idxRelevant,d).toString)
	  printlnVerbose(levelString + "close: " + d)
	  val (kx, kxIdxRelevant) = backtrackToDD(idxRelevant)
	  // Restore the clause set Phi as saved above.
	  kx.savedPhi.get.restore()

	  // In the derivation from the left branch the background context 
	  // might have been extended. All clauses in Phi must hence be updated with the
	  // new rigid variables from that derivation. 
	  // This preserves the invariant that the clauses in Phi are in sync with
	  // Gamma. 
	  for (rv <- (Gamma.rvars -- kx.savedPhi.get.savedGammaRVars))
	    Phi foreach { _.updateInvariants(rv) }

	  // Successful, Right split
	  if (kx.kind == UU) {
	    // if Kx is ground we can right split UU, otherwise SS
	    if (kx.vars.isEmpty)
	      selectedInfOpt = Some(InfSplit(kx.compl, Constraint(), UU, II, kxIdxRelevant))
	    else
	      selectedInfOpt = Some(InfSplit(kx.compl.sko(), Constraint(), SS, II, kxIdxRelevant))
	  }
	  else 
	    // Parametric - it can't be skolemized, because
	    // Skolem literals are never decision literals.
	    // (They are used in right splits only)
	    selectedInfOpt = Some(InfSplit(kx.compl, Constraint(), PP, II, kxIdxRelevant))
	}
      }
    }

  }

  /**
   * SavedPhi represent a clone of the clause set Phi at the time
   * SavedPhi was created.
   */
  class SavedPhi {
    val savedGammaRVars = Gamma.rvars
    val savedPhi = new ArrayBuffer[ClauseX]()
    for (i <- 0 until Phi.length)
      savedPhi += Phi(i).clone()
    val weightBoundSaved = weightBound
    // val clauseIndexSaved = clauseIndex
    def restore() {
      Phi = savedPhi
      weightBound = weightBoundSaved
    }    
  }
  
  def showPhi() {
    for (i <- 0 until Phi.length) 
      Phi(i).show()
  }

  def showLambda() {
    for (i <- 0 until Lambda.length) 
      println(i + ": " + Lambda(i).toString)
  }

  def show() {
    println("Lambda:"); showLambda()
    println("Phi:"); showPhi()
    Gamma.show()
  }

  def level = Lambda.length-1
  def levelString = "[" + decisionLevels + "/" + level + "] "

  
  // Search the X=X literal of the given type in the context
  def getXeqXLit(typ: Type):CLit = {
    // Notice: start at 2, because of assert and -v literals 
    // for (i <- 2 until Sigma.FGTypes.size+2)
    for (i <- 2 until Sigma.types.size+2)
      if (Lambda(i).eqn.typ == typ)
	return Lambda(i)
    throw new InternalError("Equation X=X has not been defined for type" + typ)
  }


  /**
   * Context literal augmented with the set of (indices of) context literals 
   * it depends on, and the saved state attached to it in case of a decision literal.
   * That is, idxRelevant = { k1, ..., ki } means that the (previous)
   * context literals Lambda(k1) ... Lambda(ki) are relevant to derive this CLitX.
   */

  class CLitX(K: CLit, val idxRelevant: Set[Int], val savedPhi: Option[SavedPhi]) 
  extends CLit(K, K.kind, K.status, K.idx) {
    // override def toString = 
    //   super.toString + ":" + idxRelevant
  }

  // Counter for freshly introduced rigid variables
  val RVarCounter = new Counter
  

}
