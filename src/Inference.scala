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

object Inference {

  import Term._
  import Literal._
  import ClauseX._
  import Clauses._
  import Formula._
  import BGContext._
  import State._

  /**
   * The Inference class, which provides information about an inference that can be carried out.
   */

  // When an optimal split candidate has been discovered we abort
  // evaluating all candidates and take that split right away.
  case class OptimalSplit(inf: InfSplit) extends Exception {}

  // Splits usually receive a weight penalty, so that they are deprecated
  val splitPenalty = 1

  /**
   * A WeightedInference provides information that allows to compare the inference
   * that extend; used for finding the next selected inference
   */

  trait WeightedInference {
    // The weight - highest priority. To be fair, only finitely many clauses and literals
    // of a given weight must exist, modulo variants.
    val weight: Int 
    val priority: Int // higher number means higher priority

    def betterThan (that: WeightedInference) =
      // lexicographic combination of weight and priority
      (weight < that.weight || (weight == that.weight && priority > that.priority))
  }

  /**
   * ExecInferences is the superclass of inferences that have enough information to execute them
   */

  abstract class ExecInference

  case class InfRestrict(rv: RVar) extends 
      ExecInference with WeightedInference {
	// Just something for the moment
	val weight = 2
	val priority = 2
      }

  case class ExecClausalInference(DX: ClauseX, inf: ClausalInference) extends 
      ExecInference with WeightedInference {
	val weight = inf.weight
	val priority = inf.priority
      }

  abstract class ClausalInference extends WeightedInference

  abstract case class InfSupNeg(iL: Int, K: CLit) extends ClausalInference

  abstract case class InfSupPos(iL: Int, K: CLit) extends ClausalInference 

  abstract case class ExtCUIs(iL: Int, K: CLit) extends ClausalInference 


  // c is the Constraint to be added to Gamma. It is guaranteed to be consistent with Gamma 
  case class InfSplit(K: Lit, c: Constraint, kind: Kind, status: CtxtStatus, 
		      idxRelevant: Set[Int]) extends ExecInference with WeightedInference {

    val weight = K.depth + splitPenalty // 2* : deprecate Splits xxx
    val priority = 
      if (K.vars.isEmpty)
	10
      else 
	(kind, status) match {
	  // could take sign into account
	  case (UU, II) => 8
	  case (SS, II) => 7
	  case (PP, II) => 3 // if (K.eqn.lhs.isVar && K.eqn.rhs.isVar) 1 else 5
	  case (UU, DD) => 5
	  /*
	   case (SS, DD) => 8 // Impossible
	   */
	  case (PP, DD) => 2
	}

    def isOptimalSplit = 
      // Optimal Split literals are allowed to have the same weight as the other
      // inferences
      weight <= State.weightBound+splitPenalty && status == II && 
      K.vars.isEmpty && 
      // (kind == UU || kind == SS) &&
         c.fs.isEmpty // doesn't currently work with constraints, because they are not checked for
    //consistency with Gamma when isOptimalSplit is determined.

  }

  def bestClausalInf(Phi: Seq[ClauseX]) = {
    var res:Option[ExecInference with WeightedInference] = None
    for (phi <- Phi;
	 openFromPhi <- phi.openClausal)
      if (res == None || (openFromPhi betterThan res.get))
	res = Some(ExecClausalInference(phi, openFromPhi))
    // println("==> Selected clausal inference: " + res)
    res
  }

  def bestSplit(Phi: Seq[ClauseX]):Option[InfSplit] = {
    var res:Option[InfSplit] = None
    try {
      for (phi <- Phi;
	   // phi.CUIs.bestSplit() returns Option[Inference]
	   openFromPhi <- phi.openSplits())
	if (res == None || (openFromPhi betterThan res.get)) {
	  if (Gamma isConsistentWith openFromPhi.c) {
	    // found one
	    res = Some(openFromPhi)
	    // if openFromPhi has a consistent (non-empty) constraint and fits the weight bound
	    // we use it immediately, because consistency checking is so expensive
	    if ((!openFromPhi.c.isEmpty) && openFromPhi.weight <= State.weightBound)
	      return res
	  }
	}
      res 
    } catch {
      case OptimalSplit(inf) => Some(inf)
    }
  }

  def selectInf(Phi: Seq[ClauseX]) = 
    if (!Gamma.openInfRestrict.isEmpty)
      // Higest priority
      Some(Gamma.openInfRestrict.head)
    else
      (bestClausalInf(Phi), bestSplit(Phi)) match {
	case (None, None) => None
	case (Some(cInf), None) => Some(cInf)
	case (None, Some(sInf)) => Some(sInf)
	case (Some(cInf), Some(sInf)) => 
	  // prefer the lightest inference
	  if (sInf betterThan cInf) 
	    Some(sInf) 
	  else 
	    Some(cInf) 
      }

}
