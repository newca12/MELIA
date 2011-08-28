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

object Subst {

  import Term._
  import Expression._
  import Clauses._
  import Signature._

  /**
   * Substitutions
   */


  class Subst(env: Map[Var, Term]) {
    // It might be tempting to mixin collection.Map[Var, Term]
    // however apply and + are just too different to make sense

    def isEmpty = env.isEmpty
    def lookup(v: Var) = env.get(v)  // returns Option[Term]
    def actsOn(v: Var) = env.contains(v)
    def actsOn(vs: List[Var]) = vs exists { env.contains(_) }
    def getEnv = env

    // A substitution sigma is simple (for a constraint c) if for every x in vars(c),
    // sigma(x) is a variable or a Rigid Variable. In other words, simple substitutions
    // do not pollute constraints with foreground symbols
    // 
    def isSimple(c: Constraint) = 
      c.vars forall { 
	x => {
	  val t = this(x)
	  t match {
	    case _:Var => true
	    case FunTerm(fun,_) => Sigma.BGOps contains fun
	  }
	  // t.isRVar || t.isParam
	}
      }

    def == (that:Subst) = (env == that.getEnv)

    // Use substitutions as functions:
    // Notice that this works for any Expression
    def apply[T](es: Array[Expression[T]]) = es.map(_.applySubst(this))
    def apply[T](es: List[Expression[T]]) = es.map(_.applySubst(this))
    def apply[T](e: Expression[T]) = e.applySubst(this)

    override def toString = env.mkString("[", ", ", "]")

    // extend with one binding - don't check anything
    def + (xt: (Var, Term)) =  new Subst(env + xt)

    // composition of substitutions
    def ++ (sigma: Subst) = 
      new Subst(
	(env.mapValues(sigma(_)) // apply sigma to all terms,
	 ++                     
         // extend with all bindings from sigma that env does not act on,
	 sigma.getEnv.filter(vt => !env.contains(vt._1)))
	// and delete all trivial bindings
	. filter(vt => vt._1 != vt._2))

    def -- (xs: List[Var]) = new Subst(env -- xs)


    def isRenaming =
      env forall { vt => 
	val (x, y) = (vt._1, vt._2)
        // Check that all terms in the codomain are variables, 
        y.isInstanceOf[Var] && 
	// and that env is injective,
  	(!(env exists { v1t1 => (y == v1t1._2) && (x != v1t1._1) }))
    }

    // combine two unifiers (typically mgus) into one, simultaneous unifier, if possible 
    def combine(that: Subst):Option[Subst] =
      // Take this and extend it to a unifier for each binding in that.
      // The assert substitution can be used at most once.
      // This is a consequence of how the assert bindings are made.
      try {
	var sigma = this // sigma will be the result
	for (bind <- that.getEnv) {
	  // sigma must also be a unifier of the bindings in that,
	  // hence sigma is applied to these bindings before unifying them
	  val s = sigma(bind._1)
	  val t = sigma(bind._2)
	  sigma = sigma ++ s.unify(t) 
	}
	Some(sigma)
      } catch {
	case _:UnifyFail => None
      }
  }

  // Convenience function
  def Subst(bindings: (Var, Term)*) = new Subst(bindings.toMap)

  /**
   * Build the cross product of all unifiers in ss1 and ss2
   * by combining their elements
   */

  def combineSubst(ss1:List[Subst], ss2:List[Subst]):List[Subst] = 
    for (s1 <- ss1; s2 <- ss2; sigma <- (s1 combine s2)) yield sigma

}
