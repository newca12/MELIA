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

object Term {

  import Expression._
  import Predefined._
  import Type._
  import Signature._
  import Subst._
  import Eqn._
  import Clauses._
  import Misc._
  

  case class UnifyFail() extends Exception {}
  case class MatchFail() extends Exception {}

  /**
   * The representation of terms, as used in Formulas, Clauses, Constraints,
   * and Foreground/Background Contexts.
   */

  abstract class Term extends Expression[Term] {

    // Mixin UnifiableExpression
    def mgus(that: Term) = 
      try { val sigma = this.unify(that)
	   List(sigma)
	 } catch {
	   case _:UnifyFail => List()
	 }
    
    def matchers(that: Term, gammas:List[Subst]) = 
      for (gamma <- gammas;
	   sigma <- try { 
		     // Some(this.matchTo(that,gamma).removeTrivial)
		     // No - we must keep trivial bindings otherwise
		     // test for variantship based on matchers will not work!
		     Some(this.matchTo(that,gamma))
		    } catch {
		      case _:MatchFail => None
		    }) yield sigma


    // Use cases - we know that the result of unifiers or matchers is empty 
    // or a singleton
    def mgu(that: Term) = 
      (this mgus that) match {
	case Nil => None
	case List(sigma) => Some(sigma)
      }

    def matcher(that:Term) = 
      (this matchers that) match {
	case Nil => None
	case List(sigma) => Some(sigma)
      }
    
    // Turn the term into one whose operators are all foreground symbols
    // or all background symbols, extract offending subterms and also return
    // equations defining these.
    def purify: (Term, List[Eqn])

    def applyCSubst(rv: (SymBGConst, FunTerm)):FunTerm

    // Various type testing predicates
    def isVar = isInstanceOf[Var] 
    def isRVar = isInstanceOf[RVar]
    def isParam = isInstanceOf[Param]
    def isBGLitConst = isInstanceOf[BGLitConst]

    def isPred: Boolean


    // Ordered paramodulation, giving a list of terms and substitutions,
    // where each such term/substitution pair is obtained from this by 
    // exactly one paramodulation step on this and the substitution.
    def para(E: Eqn): List[(Term,Subst,Eqn)]

    /**
     * demodulate this with the
     * ordered unit clause among the given Simplifiers.
     * Returns the pair consisting of the result of demodulation and the
     * set of idx's of the given clauses or None if demodulation resulted in
     * the same term.
     * See Literal.demodulate for an explanation of topLevelT
     */

    def demodulate(Ss: Seq[(Eqn,Set[Int])], topLevelT: Option[Term]):(Term, Option[Set[Int]])

    val depth: Int  // The depth of the term

    val vars: Set[Var] // The variables occuring in this
    val rvars: Set[RVar] // The rigid variables occuring in this
    val params: Set[Param] // The parameters occuring in this
    val freeBGConsts: Set[FreeBGConst] // The free constants occuring in this
    
    // Unify this with t; may raise an exception UnifyFail
    def unify(t: Term):Subst

    // Match this to t under a pre-existing substitution sigma
    // defined so far. sigma is to be extended to the sought matcher.
    def matchTo(t: Term, sigma: Subst):Subst

    // Term ordering

    /**
     * Definition of LPO:
     *
     * s >_lpo t iff
     * (1) t \in vars(s) and t /= s, or
     * (2) s = f(s_1,...,s_m), t = g(t_1,...,t_n) and
     *     (a) s_i >=_lpo t for some i, 
     *     (b) f > g and s >_lpo t_j for all j, or
     *     (c) f = g, s >_lpo t_j for all j, and
     *         (s_1,...,s_m) (>_lpo)_lex (t_1,...,t_n)
     */

    // Straight from the defintion
    def gtr_lpo(t: Term): Boolean = 
      (this,t) match {
	case (s:FunTerm, t:Var) => t occursIn s
	case (_:Var, _) => false
	// Make RVars least in ordering
	case (v:RVar, w:RVar) => v.name > w.name // lexicographic on name
	case (_:FunTerm, _:RVar) => true
	case (FunTerm(f, fArgs), FunTerm(g, gArgs)) => 
	  fArgs.exists( _ geq_lpo t ) ||
	( gtr_prec(f, fArgs.length, g, gArgs.length) && 
         gArgs.forall ( this gtr_lpo _ ) ) ||
	( f == g && gtr_lpo_lex(this, fArgs, gArgs))
	case (_, _) => false
      }

    def geq_lpo(t: Term): Boolean = 
      this == t || (this gtr_lpo t)


    // Lexicographic extension of lpo.
    // Of course one could define it more generally, 
    // parametric in the base ordering
    def gtr_lpo_lex(hs: Term, ss: List[Term], ts: List[Term]): Boolean = {
      (ss,ts) match {
	// case (s::sRest, Nil) => true 
	case (Nil, Nil) => false
	// the above case can never occur in the application above
	case (s::sRest, t::tRest) => 
	   ((s gtr_lpo t) && (tRest.forall(hs gtr_lpo _))) ||
	   ( s == t && gtr_lpo_lex(hs, sRest, tRest) )
	case (_, _) => false
      }
    }
    
    /**
     * Precedence on function symbols
     * Hard-coded for now: symbols of higher arity have precedence over lower arity
     * ones, use lexicographic ordering (on String) to break the ties.
     */ 
/*
    def gtr_prec(f:String, fArity:Int, g:String, gArity:Int) =
      fArity > gArity || 
    ( fArity == gArity && f > g )
*/

    // Make constants minimal, for non-constants let lex ordering of names decide
    def gtr_prec(f:String, fArity:Int, g:String, gArity:Int) =
      (fArity, gArity) match {
	case (0,0) => (f > g) 
	case (_,0) => true
	case (0,_) => false
	case (_,_) => f > g
      }
  }

  // There are two kinds of Terms: Variables and FunTerms:

  // A variable is determined by its name and an index
  // We use the index to generate (fresh) variants of terms in a convenient way
  
  case class Var(name: String, index:Int) extends Term {  
    override def toString = name + (if (index > 0) "_" + index else "")

    val depth = 0

    val vars = Set(this)
    val rvars = Set[RVar]()
    val params = Set[Param]()
    val freeBGConsts = Set[FreeBGConst]()

    // def isPredTerm = false // Variables are always proper terms

    def isPred = false

    def purify = (this, List())

    def para(E: Eqn) = List() // never paramodulate into variables

    def demodulate(Ss: Seq[(Eqn,Set[Int])], topLevelT: Option[Term]):(Term, Option[Set[Int]]) = (this, None)

    def occursIn(t: Term): Boolean =
      t match {
	case Var(x,i) => name == x && index == i
	case FunTerm(fun, args) => args.exists(occursIn _)
      }

    def applySubst(s: Subst) = 
      s.lookup(this) match {
	case Some(t) => t
	case None => this
      }
    
    // This should never be called
    def applyCSubst(rvt: (SymBGConst, FunTerm)) = {
      assert(false, 
	     { println("applyCSubst on variable should never happen: " + this + " " + rvt) })
      // Dummy
      rvt._1
    }

    def unify(t: Term) = 
      t match {
	case Var(x,i) => 
	  if (name == x && index == i) Subst() else Subst(this -> t)
	case t:FunTerm =>
	  if ( // t.isPredTerm || ill-sorted case - we do not need to check it,
	       // caller makes sure this never happens
	      (this occursIn t)) 
	    throw new UnifyFail() 
	  else Subst(this -> t)
    }

    def matchTo(t: Term, sigma: Subst) = 
      if (sigma.actsOn(this)) 
	// check if the term bound to x is equal to t, if so nothing
	// needs to be done, otherwise fail
	if (sigma(this) == t) sigma else throw new MatchFail()      
      else sigma + (this, t)
  }

  // Handy abbreviation:
  def Var(name: String):Var = Var(name,0)

  case class FunTerm(fun: String, args:List[Term]) extends Term {  

    // The depth of a compound term is the max of its arguments plus 1.
    // That is, we take the tree depth
    val depth = if (args.isEmpty) 0 else (args map { _.depth }).max + 1

    // lazy val vars = args.foldLeft(Set[Var]())(_ union _.vars)
    // Expression provides us with vars of list of Expressions
    lazy val vars = args.vars

    // This can be overriden below, see RVar and Param

    lazy val rvars = args.rvars
    lazy val params = args.params
    lazy val freeBGConsts = args.freeBGConsts

    def hasBGType = Sigma.BGTypes contains Sigma(fun).resType
    def isPred = Sigma(fun).resType == OType
    def isBGOp = Sigma.BGOps contains fun

    // This also applies to rigid variables, literal constants and parameters
    // no need to overwrite
    def purify = {

      def hpurify(t: Term, okOps: Set[String]): (Term,List[(Var,FunTerm)]) = {
	// println("==> hpurify: " + t + " " + flip)
	t match {
	  case v:Var => (v, List())
	    // Const-case will preserve Params, RVars etc
	  case tc:Const => 
	    if (okOps contains tc.name) 
	      (tc, List())
	    else {
	      // t itself is offending
	      val name = Var("X",variantCtr.next())
	      (name, List((name, tc)))
	    }
	  case FunTerm(fun, args) => 
	    // assert(!t.isRVar, { println("Bang!") })
	    if (okOps contains fun) {
	      // t is allowed to stay, but purify args
	      var (argsPurified, argsDefs) = (List[Term](), List[(Var,FunTerm)]())
	      for (arg <- args) {
		val (a, ds) = hpurify(arg, okOps)
		argsPurified ::= a
		argsDefs :::= ds
	      }
	      (FunTerm(fun, argsPurified.reverse), argsDefs)
	    } else {
	      // t itself is offending
	      val name = Var("X",variantCtr.next())
	      (name, List((name, t.asInstanceOf[FunTerm])))
	    }
	}
      }

      if (this == TT)
	(TT, List()) // belongs to both FG and BG - purification not necessary
      else {
	val thisOps = if (Sigma.BGOps contains fun) Sigma.BGOps else Sigma.FGOps
	val (thisPure, thisDefs) = hpurify(this, thisOps)
	var open = thisDefs
	var done = List[Eqn]()
	while (!open.isEmpty) {
	  // Select the first open element 
	  val (x, t) = open.head
	  //println("==> selected = " + selected)
	  open = open.tail
	  // We call hpurify so that it leaves the toplevel operator in place.
	  // This guarantees termination.
	  val tOps = if (Sigma.BGOps contains t.fun) Sigma.BGOps else Sigma.FGOps
	  val (tPure, tDefs) = hpurify(t, tOps)
	  done ::= Eqn(x, tPure, Sigma.typeOf(t))
	  open :::= tDefs
	}
	(thisPure, done)
      }
    }


    // override def toString = fun + args.toMyString("","(",",",")")
    override def toString = Sigma.getFormatFn(fun)(args)

    // One-Step ordered paramodulation from E into this, in all possible ways
    // The result is a list of triples (this', sigma, E')
    // where this' is the result of a paramodulation step to this with 
    // a fresh variant E' of E and sigma is the underlying mgu.
    // Neither this' nor E' have sigma applied to it.
    // (The rationale is to facilitate integration of Para in a wider context)
    // Notice that E' cannot have been used against the ordering, this is checked for
    def para(E: Eqn) = {
      if (this == TT)
	// Because TT is (considered) the smallest term it is impossible to do an
	// ordered paramodulation step into it.
	// This case is actually impossible because we never create InfSup inferences 
	// that would make paramodulation possible
	List()
      else {
	// What if this is a Skolem constant, one that has been introduced during proof search?
	// This is impossible, as Skolem constants never appear in clauses, the are used only
	// in CUI computation.
	// What if E contains Skolem constants? This is impossible, as Skolem context literals (SS)
	// are explicitly never used for paramodulation.
	// In conclusion we need not worry about typing Skolem constants
	// first we do top-level paramodulation
	// from lhs to rhs
	val topParaLR = { 
	  if (Sigma.typeOf(this) != E.typ)
	    // ill-sorted case -- cannot do top level paramodulation
	    // This applies in particular if this is a Parameter. No *ordered* paramodulation
	    // into a Parameter is possible because only another parameter could be smaller
	    // than this. But then E would be between two different parameters, and so E
	    // would not be a foreground equation, it would instead be moved into the 
	    // constraint part. 
	    List()
	  else {
	    val e1 = E.fresh
	    // top-level paramodulation with e1 from left to right
	    (this mgu e1.lhs) match {
	      case None => List()
	      case Some(sigma) => { 
		// if sigma(e1) is ordered than the second disjunct holds true,
		// so we do not need to check it explicitly
		if (E.isOrdered || !(sigma(e1.rhs) geq_lpo sigma(e1.lhs)))
		  List((e1.rhs, sigma, e1))
		else
		  // ordering constraint violated
		  List()
	      }
	    } 
	  }
	}
	// from rhs to lhs
	val topParaRL = 
	  if (E.isOrdered || Sigma.typeOf(this) != E.typ)
	    // ordering constraint would be violated - can't use E from right to left then
	    // or ill-sorted case -- cannot do top level paramodulation, as above
	    List()
	  else {
	    val e1 = E.fresh
	    // top-level paramodulation with e1 from right to left
	    (this mgu e1.rhs) match {
	      case None => List()
	      case Some(sigma) => { 
		// check ordering constraint
		if (!(sigma(e1.lhs) geq_lpo sigma(e1.rhs)))
		  List((e1.lhs, sigma, e1))
		else 
		  List()
	      }
	    }
	  }

	// finally, the paramodulants into the proper substerms
	val argsPara =  
	  if (E.typ == OType)
	    // non-equational atoms can be applied at top-level position only
	    List()
	  else
	    for ((args1, sigma, e1) <- paraList(args, E)) yield
	      (FunTerm(fun, args1), sigma, e1)
       // Grand collection
      topParaLR ::: topParaRL ::: argsPara
      }
    }
      
    // the list of termlist/substitution/from-equation triples resulting 
    // from all one-step paramodulations  
    // from E into the given non-empty list of term ts  
    def paraList(ts: List[Term], E:Eqn):List[(List[Term],Subst,Eqn)] =
      ts match { 
	case Nil => List()
	case t::tt => {
	  // first possibility: leave t untouched
	  // and combine with all results of paras into tt
	  ( for ((tt1, sigma, e1) <- paraList(tt, E)) yield
	      (t :: tt1, sigma, e1) ) :::
	  // second case: leave the rest untouched
	  // and combine with all results of paras into t
	  ( for ((t1, sigma, e1) <- t.para(E)) yield 
	      (t1 :: tt, sigma, e1) )
	}
      }

    def demodulate(Ss: Seq[(Eqn,Set[Int])], topLevelT: Option[Term]):(Term, Option[Set[Int]]) = {
      if (isRVar)
	// never
	return (this, None)

      // Assume that the clauses used for demodulation are not OTyped - 
      // this is OK as unitSimpResol and subsumption takes care of OTyped literals
      // println("==> demodulate " + this)
      var argsIdxRelevant = Set[Int]()
      var argsSimplified = List[Term]()
      var argsDemodulated = false
      // First we demodulate the args, i.e. innermost strategy.
      // It is always OK to demodulate the arguments.
      for (arg <- args.reverse) {
	val (argSimplified, argIdxRelevant) = arg.demodulate(Ss, None)
	argsSimplified ::= argSimplified
	argIdxRelevant match {
	  case None => () // nothing to update
	  case Some(idxs) => {
	    argsIdxRelevant ++= idxs
	    argsDemodulated = true
	  }
	}
      }
      val hSimplified = 
	// the distinction here is important, as hSimplified will be a
	// a Param or RVar if this is (otherwise hSimplified would be lifted to
	// a less specific FunTerm)
	// No - Params are impossible, they can occur only in constraints,
	// and the case of RVars has been checked above.
	// Nevertheless don't build a new term if not necessary.
	if (argsDemodulated)
	  FunTerm(fun, argsSimplified)
	else
	  this
      // See if hSimplified can be Demodulated at the toplevel
      for ((e, eIdxRelevant) <- Ss;
	   // if !e.isPredEqn; -- predicate atoms are treated by subsumption
	   // Type-checking
	   if Sigma.typeOf(hSimplified) == e.typ;
	   sigma <- (e.lhs matchers hSimplified);
	   eRhsInst = sigma(e.rhs)) {
	     // Can only demodulate at toplevel if the (instantiated) e.rhs is smaller
	     // than topLevelT (if given)
	     if (topLevelT == None || (topLevelT.get gtr_lpo eRhsInst)) {
	       val (rhsInstSimplified,rhsInstIdxRelevant) = 
		 eRhsInst.demodulate(Ss,None)
	       val rhsInstIdxRelevantAsSet = 
		 rhsInstIdxRelevant match { 
		   case None => Set[Int]() // No demodulation - no dependencies
		   case Some(idxs) => idxs // Some demodulation - take the indexes resulting from that
		 }
	       return((rhsInstSimplified, Some(rhsInstIdxRelevantAsSet ++ eIdxRelevant ++ argsIdxRelevant)))
	     }
	   }
      // Nothing found
      (hSimplified, if (argsDemodulated) Some(argsIdxRelevant) else None)
      // println("==> demodulate of " + this + " = " + res)
    }

    def applySubst(sigma: Subst) =  FunTerm(fun, sigma(args))

    // to be overriden by subclasses of SymBGConst below
    def applyCSubst(rvt: (SymBGConst, FunTerm)) = FunTerm(fun, args map { _.applyCSubst(rvt) })


    def unify(t: Term) = {
      // Unification of lists of terms:
      // Invariant as above: sigma has already been applied to l1 and l2
      def unifyList(l1:List[Term], l2:List[Term]):Subst =  {
	var hl1 = l1 // we loop over l1 and
	var hl2 = l2 // we loop over l2
	var sigma = Subst() 
	// the result substitution
	// invariant: sigma has still to be applied to all terms in hl1 and hl2
	while (!hl1.isEmpty) {
	  sigma = sigma ++ (sigma(hl1.head).unify(sigma(hl2.head)))
	  hl1 = hl1.tail
	  hl2 = hl2.tail
	}
	sigma
      }

      t match {
	case Var(x,i) => Var(x,i).unify(this) // turn around and take Var-case above
	case FunTerm(fun, args) =>
	  if (this.fun == fun) 
	    unifyList(this.args, args) 
	  else 
	    throw new UnifyFail()
      }
    }
    
    def matchTo(t: Term, sigma: Subst) = {

      // Matching of lists of terms:
      def matchToList(l1:List[Term], l2:List[Term], sigma:Subst):Subst =  {
	var hl1 = l1 // we loop over l1 and
	var hl2 = l2 // we loop over l2
	var hsigma = sigma 
	// the result substitution
	while (!hl1.isEmpty) {
	  hsigma = hl1.head.matchTo(hl2.head, hsigma)
	  hl1 = hl1.tail
	  hl2 = hl2.tail
	}
	hsigma
      }

      t match {
	case Var(x,i) => throw new MatchFail()
	case FunTerm(fun, args) =>
	  if (this.fun == fun) 
	    matchToList(this.args, args, sigma) 
	  else 
	    throw new MatchFail()
      }
    }
  }

  /**
   * Foreground constants or background constants. The latter are
   * free constants (from Skolemisation), Parameters, literal constants
   * (integer numbers in particular) and rigid variables.
   * See below for further classification
   */
  abstract class Const(val name: String) extends FunTerm(name, List()) {

    override def isPred = false

    def == (that: Const) = name == that.name

  }

  object Const {
    // Create a constant, when the type is suppose to be defined in Sigma already
    def apply(name: String) = FunTerm(name, List())
    def unapply(t: Term) = 
      t match { 
	// case FunTerm(name, Nil) => Some(name)
	case t:Const => Some(t.name)
	case _ => None
      }
  }


  /**
   * Here come the different kinds of constants that belong to the background signature
   * We single out Symbolic Background Constants.
   * Todo: this should more appropriately go to a more theory-specific module.
   */

  abstract class SymBGConst(name: String) extends Const(name) {

    def == (that: SymBGConst) = name == that.name

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = 
      if (this == rvt._1) rvt._2 else this

  }


  // Rigid Variables
  class RVar(name: String) extends SymBGConst(name) {
 
    override def toString =  name //  + "^r"

    override def applySubst(sigma: Subst) = this

    override lazy val rvars = Set(this)
    override lazy val params = Set[Param]()
    override lazy val freeBGConsts = Set[FreeBGConst]()

  }

  object RVar {
    def apply(name: String) = new RVar(name)
    def unapply(t: Term) = 
      t match {
	case t:RVar => Some(t.name)
	case _ => None
      }
  }

  class Param(name: String) extends SymBGConst(name) {
 
    override def toString =  name + "^p"

    override def applySubst(sigma: Subst) = this

    override lazy val rvars = Set[RVar]()
    override lazy val params = Set[Param](this)
    override lazy val freeBGConsts = Set[FreeBGConst]()

  }

  object Param {
    def apply(name: String) = new Param(name)
    def unapply(t: Term) = 
      t match {
	case t:Param => Some(t.name)
	case _ => None
      }
  }

  class FreeBGConst(name: String) extends SymBGConst(name) {
 
    override def applySubst(sigma: Subst) = this

    override def toString =  name

    override lazy val rvars = Set[RVar]()
    override lazy val params = Set[Param]()
    override lazy val freeBGConsts = Set(this)

    def this(name: String, typ: Type) { 
      this(name) 
      Sigma = Sigma addBG (name -> Rank0(typ))
    }
  }

  object FreeBGConst {
    def apply(name: String) = new FreeBGConst(name)
    // def apply(name: String, typ: Type) = new FreeBGConst(name, typ)
    def unapply(t: Term) = 
      t match {
	case t:FreeBGConst => Some(t.name)
	case _ => None
      }
  }

  /**
   * Literal constants, like numbers.
   * Notice, not a subclass of SYmBGConst
   */

  class BGLitConst(val value: Int) extends Const(value.toString) {
 
    // Hard-coded: assume that the Background type is IntType
    // This should be done more principled of course
    // def asInt = name.toInt

    override def toString =  value.toString

    override def applySubst(sigma: Subst) = this

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = this


    override lazy val rvars = Set[RVar]()
    override lazy val params = Set[Param]()
    override lazy val freeBGConsts = Set[FreeBGConst]()
 
  }

  object BGLitConst {
    def apply(n: Int) = new BGLitConst(n)
    // def apply(name: String, typ: Type) = new BGLitConst(name, typ)
    def unapply(t: Term) = 
      t match {
	case t:BGLitConst => Some(t.value)
	case _ => None
      }
  }

  def pair(s: Term, t: Term) = FunTerm("$pair", List(s, t))

}
