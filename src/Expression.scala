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

object Expression {

  /*
   * Common views on "logical expressions", which contain variables, and can be unified and matched.
   * Use cases are creation of fresh variants and the instantiation ordering.
   */

  import Term._
  import Subst._
  import Misc._

  trait Expression[E] {

    // things to be implemented:

    override def toString: String

    // the free variables in the expression
    val vars:Set[Var]
    val rvars:Set[RVar]
    val params:Set[Param]
    val freeBGConsts:Set[FreeBGConst]

    // the application of a substitution to an expression
    def applySubst(sigma: Subst):E

    def mgus(that: E):List[Subst]

    // Match this to that under a set of pre-existing substitutions gammas;
    // The result consists of all substitutions that match this to that 
    // as an extension of any of the preexisting ones.
    def matchers(that: E, gammas: List[Subst]):List[Subst]

    // Derived stuff.

    // Matchers on lists of Expressions above is one as well.
    // Could also do unification of lists of Expressions, but this is more complicated
    // as the unification algorithm implemented does not have an explicit substitution parameter
    // (unlike matching) which makes it more tricky in the non-unitary case, which we have.

    def fresh = applySubst(mkRenaming(vars))

    // Create a renaming substition from vars to a set of fresh variables
    def mkRenaming(vars: Iterable[Var]) = {
      new Subst((for (Var(x,i) <- vars) yield 
	        (Var(x,i), Var(x,variantCtr.next()))).toMap)
    }
    
    // Handy abbreviation.
    def matchers(that: E):List[Subst] = matchers(that, List(Subst()))

    // With matching available, define the instantiation ordering

    // Variantship. Two Es are variants iff *all* matchers are a renaming. 
    // Is this the Right Thing?
    def ~ (that: E) = {
      // (!(this matchers that).isEmpty) &&
      // (!(that matchers this).isEmpty)
       (this matchers that) exists { _.isRenaming }
    }

    def >~ (that: E) = {
      !(this matchers that).isEmpty
    }

    // Strict instanceship
    def > (that: E) = {
      //      !(this matchers that).isEmpty &&
      //       (that matchers this).isEmpty 
      // this >~ that && (!that >~ this)

     val sigmas = (this matchers that)
     (!sigmas.isEmpty) && (sigmas forall { ! _.isRenaming })
    }
  }


  // Matching of lists of Expressions
  // The caller must makes sure that l2 is at least as long as l1,
  // otherwise unexprected thing may happen.
  def matchers[E <: Expression[E]](l1:List[E], l2:List[E], gammas:List[Subst]):List[Subst] =  {
    var hl1 = l1 // we loop over l1 and
    var hl2 = l2 // we loop over l2
    var hgammas = gammas
    // the result substitution
    while (!hl1.isEmpty) {
      hgammas = hl1.head.matchers(hl2.head, hgammas)
      hl1 = hl1.tail
      hl2 = hl2.tail
    }
    hgammas
  }

  // variantCtr is used to create fresh variants.
  // The invariant is that all variables in all data structures
  // use indices that are less than or equal to variantCtr.

  val variantCtr = new Counter
  
}

