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

object Formula {

  import Term._
  import Predefined._
  import Eqn._
  import Literal._
  import Clauses._
  import Misc._
  import Expression._
  import Subst._
  import Signature._
  import Type._

  /**
   * Representation of first-order formulas (not: clauses)
   */
  

  // Thrown when a set of Formulas is detected as inconsistent
  class Inconsistent extends Exception 

  // Rewrites rules for CNF conversion (as partial functions).
  // Notice that a FormulaRewriteRules may embody several rewrite rules
  // (several cases), hence the plural
  type FormulaRewriteRules = PartialFunction[Formula,Formula] 

  val elimIffNot : FormulaRewriteRules = { 
    case IffNot(f1, f2) => Neg(Iff(f1, f2))
  }

  val elimIff : FormulaRewriteRules = { 
    case Iff(f1, f2) => And(Implies(f1, f2), Implies(f2, f1)) 
  }

  val pulloutQuants : FormulaRewriteRules = {
    case Neg(QuantForm(q, xs, f)) => QuantForm(q.dual, xs, Neg(f))
    
    case And(g, QuantForm(q, xs, f)) => {
      val (rho,xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, And(g,rho(f)))
    }

    case And(QuantForm(q, xs, f), g) => {
      val (rho,xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, And(rho(f),g))
    }

    case Or(g, QuantForm(q, xs, f)) => {
      val (rho,xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, Or(g, rho(f)))
    }

    case Or(QuantForm(q, xs, f), g) => {
      val (rho,xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, Or(rho(f),g))
    }

// Not needed - assume eliminated earlier
/*
    case Implies(QuantForm(q, xs, f), g) => {
      val rho = QuantForm(q, xs, f).mkRenaming(xs)
      QuantForm(q.dual, rho(xs).asInstanceOf[List[Var]], Implies(rho(f),g))
    }
    case Implies(g, QuantForm(q, xs, f)) => {
      val rho = QuantForm(q, xs, f).mkRenaming(xs)
      QuantForm(q, rho(xs).asInstanceOf[List[Var]], Implies(g,rho(f)))
    }

    case Implied(QuantForm(q, xs, f), g) => {
      val rho = QuantForm(q, xs, f).mkRenaming(xs)
      QuantForm(q, rho(xs).asInstanceOf[List[Var]], Implied(rho(f),g))
    }
    case Implied(g, QuantForm(q, xs, f)) => {
      val rho = QuantForm(q, xs, f).mkRenaming(xs)
      QuantForm(q.dual, rho(xs).asInstanceOf[List[Var]], Implied(g,rho(f)))
    }
*/
  }

  val elimImpl : FormulaRewriteRules = { 
    case Implies(f1, f2) => Or(Neg(f1), f2)
    case Implied(f2, f1) => Or(Neg(f1), f2)
  }

  val elimNegNeg : FormulaRewriteRules = { 
    case Neg(Neg(f1)) => f1
  }

  // Pushes all negation symbols in front of atoms.
  // Assume that => and <= have been eliminated before
  val pushdownNeg : FormulaRewriteRules = { 
    case Neg(Neg(f1)) => f1
    case Neg(Or(f1, f2)) => And(Neg(f1), Neg(f2))
    case Neg(And(f1, f2)) => Or(Neg(f1), Neg(f2))
    // Implicit negation symbol in IffNot !
    case Neg(Iff(f1, f2)) => 
      (f1, f2) match {
      // try to get ORs: 
	case (And(_,_), _) => Iff(Neg(f1), f2)
	case (_, And(_,_)) => Iff(f1, Neg(f2))
      // try to not disrupt the structure: 
	case (Neg(_), _) => Iff(Neg(f1), f2)
	case (_, Neg(_)) => Iff(f1, Neg(f2))
	// Default
	case (_, _) => Iff(f1, Neg(f2))
      }
    case Neg(QuantForm(q, xs, f)) => QuantForm(q.dual, xs, Neg(f))
  }

  val pushdownOr : FormulaRewriteRules = { 
    case Or(And(f1, f2), f3) => And(Or(f1, f3), Or(f2, f3))
    case Or(f1, And(f2, f3)) => And(Or(f1, f2), Or(f1, f3))
  }

  val elimTrivial : FormulaRewriteRules = { 
    case And(f, TrueAtom) => f
    case And(TrueAtom, f) => f
    case And(f, FalseAtom) => FalseAtom
    case And(FalseAtom, f) => FalseAtom
    case Or(f, TrueAtom) => TrueAtom
    case Or(TrueAtom, f) => TrueAtom
    case Or(f, FalseAtom) => f
    case Or(FalseAtom, f) => f
    case Neg(FalseAtom) => TrueAtom
    case Neg(TrueAtom) => FalseAtom
  } 

  // Exploit Associativity
  val flattenAndOr : FormulaRewriteRules = { 
   case And(And(f,g),h) => And(f,And(g,h))
   case Or(Or(f,g),h) => Or(f,Or(g,h))
  } 

/*
 // todo: implement this
  // Exploit Commutativity to sort, useful as preparation to exploit idempotency
  // but not yet implemented yet either.
  val sortAndOr : FormulaRewriteRules = { 
    // Assume in right-associative order
  } 
*/


  val normalizeQuantifiers : FormulaRewriteRules = { 
   case Exists(xs1, Exists(xs2, f)) => Exists(xs1 ::: xs2, f)
   case Forall(xs1, Forall(xs2, f)) => Forall(xs1 ::: xs2, f)
  } 

  abstract class Formula extends Expression[Formula] {

    // Take the arguments as a substitution rv -> t and apply it to this
    def applyCSubst(rvt: (SymBGConst, FunTerm)): Formula

    // Apply a collection of of such substitutions to this 
    def applyCSubst(rvts: Iterable[(SymBGConst, FunTerm)]): Formula = {
      var res = this
      for (rvt <- rvts) res = res.applyCSubst(rvt)
      res
    }

    // Assume that only a universal quantifier is present, if at all
    def matrix = 
      this match {
	case Forall(xs, f) => (f, xs)
	case f => (f, List())
      }

    def skolemize:Formula = {
      val normalized = reduceInnermost(normalizeQuantifiers)
      normalized match {
	case Forall(xs1, Exists(xs2, f)) => {
	  var sigma = Subst() // The skolemization substitution, for all vars in xs2
	  // The extended signature
	  // var resSig = sig 
	  for (x2 <- xs2) {
	    val skoFun = "skf_" + skfCtr.next()
	    val skoTermRank = Rank(xs1.typesOf -> x2.typeOf)
	    // See if the skolem term goes into BG or into FG
	    val skoTerm = 
	      if ((Sigma.BGTypes contains skoTermRank.resType) && 
		  skoTermRank.argsTypes.isEmpty &&
		  Flags.paramsOpSet.value == "BG") {
		Sigma = Sigma addBG (skoFun -> skoTermRank)
		FreeBGConst(skoFun)
	      } else {
		Sigma += (skoFun -> skoTermRank)
		FunTerm(skoFun, xs1.varsOf)
	      }
	    sigma += (x2.varOf -> skoTerm)
	  }
	  Forall(xs1,sigma(f)).skolemize
	}
	// Case of one single row of exists-quantifier, without forall in front.
	// todo: factor out common code
	case Exists(xs2, f) => {
	  var sigma = Subst() // The skolemization substitution, for all vars in xs2
	  // The extended signature
	  // var resSig = sig 
	  for (x2 <- xs2) {
	    val skoFun = "skc_" + skfCtr.next()
	    val skoTerm = 
	      if ((Sigma.BGTypes contains x2.typeOf) && 
		  Flags.paramsOpSet.value == "BG") {
		Sigma = Sigma addBG (skoFun -> Rank0(x2.typeOf))
		FreeBGConst(skoFun)
	      } else {
		Sigma += (skoFun -> Rank0(x2.typeOf))
		Const(skoFun)
	      }
	  }
	  sigma(f).skolemize
	}
	case f => f // no quantifiers 
      }
    }
  
    def toClausesOptimized = {
      // First, Tseitin transformation, which gives a list of formulas.
      val fs1 = this.
          reduceInnermost(elimIffNot).
          reduceInnermost(elimImpl).
          Tseitin
      // Second, each obtained formula is turned into a set of clauses using
      // standard transformations.
      // Tseitin results in a formula all whose quantifiers are universal
      // and appear in postiive polarity only. This is important below.
      fs1 flatMap { f1 =>
	val f2 = f1.
	    // May introduce Negations again (but quantifiers remain positive)
	    reduceInnermost(elimIff). 
	    reduceInnermost(elimImpl).
	    // Only now quantifiers can be pulled out, as <=> has been eliminated
	    reduceInnermost(pulloutQuants).
	    // remove double quantifiers
	    reduceInnermost(normalizeQuantifiers)
	// Need to remember the types of the variables, which are 
	// stored with the quantifiers .
	val (f2matrix, f2varTypes) = f2.matrix
	val f3s = (f2matrix.
		   // The matrix now is made from Neg, And, and Or,
	           // convert to CNF
	           reduceInnermost(pushdownNeg).
     		   reduceInnermost(elimNegNeg).
		   reduceInnermost(pushdownOr).
		   reduceInnermost(flattenAndOr).
	           reduceInnermost(elimTrivial).
	           toList(And) map { _.toClause(f2varTypes) })
        f3s filterNot { _.C.isTautology}
      }
    }

    // Not recommended
    def toClausesStandard = {
      val f1 = this.
         reduceInnermost(elimIffNot).
         reduceInnermost(elimIff).
         reduceInnermost(elimImpl).
	 // Only now quantifiers can be pulled out, as arrows have been eliminated
	 reduceInnermost(pulloutQuants).
	 // Skolemize now
	 skolemize
      // Need to remember the types of the variables, which are 
      // stored with the quantifiers .
      val (f1matrix, f1varTypes) = f1.matrix
      val f2s = (f1matrix.
		 // Only universal quantifiers in front now - remove
		 // The matrix now is made from Neg, And, and Or,
		 // convert to CNF
		 reduceInnermost(pushdownNeg orElse
     				 elimNegNeg orElse 
				 pushdownOr orElse 
				 flattenAndOr).
		 reduceInnermost(elimTrivial).
		 toList(And) map { _.toClause(f1varTypes) })
      f2s filterNot { _.C.isTautology}
    }


    def toClauses =
      if (Flags.cnfConversion.value == "optimized") 
	toClausesOptimized
      else
	toClausesStandard
       
    // Mixin (parts of) Expression
    def mgus(that: Formula) = {
      assert(false, { println("Formula.scala: mgus not implemented") })
      List()
    }

    // delegate to subclasses
    def matchers(that: Formula, gammas: List[Subst]):List[Subst]

    def compl = this match {
      case Neg(f) => f
      case _ => Neg(this)
    }

    def toLiteral(varTypes: List[TypedVar]) = {
      // The FalseAtom does not have a representation in the clause language
      assume(this != FalseAtom, { println("Unexpected FalseAtom in toLiteral") })
      this match {
	// Isn't the first case covered anyway?
	case Atom("$true", Nil) => TrueLit // better use unapply for TrueAtom
	case Atom(p, args) => Lit(true, Atom(p, args).toEqn(varTypes))
	case Neg(Atom(p, args)) => Lit(false, Atom(p, args).toEqn(varTypes))
      }
    }

    def toClause(varTypes: List[TypedVar]): Clause = {
      // Assume this is an Or of literals.
      // If this contains a FalseAtom, it will in fact be a singleton, but we don't
      // rely on that.
      // println("toClause: " + this)
      // Convert this to a list of Literals and simplify it.
      var asLiterals = List[Lit]()
      for (fss <- toList(Or).tails;
	   if !fss.isEmpty;
	   f = fss.head;
	   fs = fss.tail) 
	if (fs contains f.compl)
	  return TrueClause
	else if ((! (fs contains f)) && (f != FalseAtom))
	  asLiterals ::= f.toLiteral(varTypes)

      // Put together the clause consisting of a C part and a c part
      // by going over asLiterals, purifying them and put the result into either
      // C or c

      var CLits = List[Lit]()
      var cLits = List[Formula]()
      var open = asLiterals
      while (! open.isEmpty) {
	// Take the next literal
	val l = open.head
	open = open.tail
	// Purify it, gives the pure literal together with the definitions
	// (equations) resulting from purification
	val (lPure, lDefs) = l.purify 
	if (lPure.isBGLiteral)
	  // Goes into the constraint part. Notice constraint part is implicitly
	  // negated
	  cLits ::= lPure.compl.toFormula  
	else
	  CLits ::= lPure // into the foreground part
	// lDefs are equations, but we need literals
	open :::= lDefs map { Lit(false, _) }
      }
      Clause(OClause(CLits), Constraint(cLits), "input")
    }


    // Convert this, a nested formula of operators op, to a list.
    // This is always possibly, the result will be a singleton of the operator
    // in this does not match.
    def toList(op: BinOp):List[Formula] = 
      this match {
	case BinOpForm(hop, f1, f2) => {
	  if (op == hop) 
	    f1 :: f2.toList(op) 
	  else
	    List(this)
	}
	case _ => List(this)
      }

    def isComment = isInstanceOf[Atom] && asInstanceOf[Atom].pred == "$comment"

    def isLiteral = this match {
      case Atom(_,_) => true
      case Neg(Atom(_,_)) => true
      case _ => false
    }
    def nameFor = Atom("def_" + defCtr.next(), vars.toList)

    def univClosure(varTypes: List[TypedVar]) = 
      if (vars.isEmpty)
	this
      else
	Forall(vars.toList map { x => (x,varTypes(x)) }, this)
    
    /**
     * Todo: following comments no longer accurate.
     * 
     * Structure-preserving elimination of nested operators that would cause
     * exponential blow-up when multipled out. Inspired by Tseitin's transformation.
     * Assume that Negation has been pushed inwards and double negation has been
     * eliminated, so that it can occur in front of atoms only.
     * Also assume that IffNot and, Implies and Implied have been eliminated
     * And that all quantifier alternations are proper, i.e. no forall-forall and no exists-exists
     */

    def Tseitin:List[Formula] = {

      def norm(f: Formula) = 
	f.reduceInnermost(pushdownNeg orElse elimNegNeg)

      // open is a list of triples (name, body, varTypes) where
      // - name simple (see below), 
      // - body needs possibly Tseitinisation, and 
      // - varTypes is a list of variables governing both the variables
      //   in name and body.
      // hTseitin may extend open as it proceeds.
      var open = List[(Formula, Formula, List[TypedVar])]((TrueAtom, norm(this), List()))
      var done = List[Formula]()


      def hTseitin(f: Formula, embeddingOp: Option[BinOp], varTypes: List[TypedVar]):Formula = {
	// f is the formula whose complex proper subterms are to be extracted.
	// Assume f has been 'norm'alized, so that negation can occur only in front
	// of atoms.
	// embeddingOp can be And or Or only.
	// varTypes is a list of free variables that contains (at least) each free 
	// variable in f.

	def ExistsMaybe(xs: List[TypedVar], f: Formula) = 
	  if (xs.isEmpty) f else Exists(xs, f)

	// Returs name, for convenience
	def definition(positive: Boolean, name: Atom, body: Formula, varTypes: List[TypedVar]) = {
	  val Atom(pred, vars) = name
	  Sigma += (pred -> Rank((vars.asInstanceOf[List[Var]] 
				  map { varTypes(_) }) -> OType))
	  if (positive)
	    open ::= (name, body, varTypes)
	  else
	    open ::= (norm(Neg(name)), norm(Neg(body)), varTypes)
	  name
	}

	def isSimplePos(f: Formula):Boolean =
	  f match {
	    case Atom(_, _) => true
	    case Neg(Atom(_, _)) => true
	    // Quantifiers OK, as long as there's a simple formula underneath
	    case Forall(_, f) => isSimplePos(f)
	    case _ => false
	  }

	def isSimpleNeg(f: Formula):Boolean =
	  f match {
	    case Atom(_, _) => true
	    case Neg(Atom(_, _)) => true
	    // Quantifiers OK, as long as there's a simple formula underneath
	    case Exists(_, f) => isSimplePos(f)
	    case _ => false
	  }

	// Body of hTseitin
	if (isSimplePos(f)) 
	  f 
	else f match {
	  case Forall(xs, f1) => {
	    // Continue descending
	    Forall(xs, hTseitin(f1, embeddingOp, varTypes ++ xs))
	  }
	  case Exists(xs, Or(f1, f2)) => 
	    // Distribute exists
	    hTseitin(Or(Exists(xs, f1), Exists(xs, f2)),
		     embeddingOp,
		     varTypes)
	  case Exists(xs, f1) => {
	    // Try to distribute over And
	    f1 match { 
	      case And(f2l, f2r) => {
		// try to distribute Exists xs over f2l and f2r
		// This can be done for the variables that occur in f2l (resp f2r) only
		val f2lRelVars = (xs restrictTo f2l.vars) restrictToNot(f2r.vars)
		val f2rRelVars = (xs restrictTo f2r.vars) restrictToNot(f2l.vars)
		val f2SharedVars = xs restrictToNot (f2lRelVars ::: f2rRelVars).varsOf.toSet
		if (f2SharedVars.length < xs.length) 
		  // Successfully shifted some of xs variables down
		  return hTseitin(ExistsMaybe(f2SharedVars,
					      And(ExistsMaybe(f2lRelVars, f2l),
						  ExistsMaybe(f2rRelVars, f2r))),
				  embeddingOp,
				  varTypes)
	      }
	      // If the above is not successful or f is not of the form Exists-And
	      // we do Skolemization
	      case _ => ()
	    }
	    // The skolemization substitution, for all vars in xs
	    var sigma = Subst() 
	    for (x <- xs) {
	      // As an invariant of descending into the formula, varTypes
	      // contains all free variables in f, however possible more.
	      // It is clear that the skolem term constructed here needs to be
	      // parametrized only in the free variables of f, which could be
	      // fewer than in varTypes. Hence we collect these as the relevant 
	      // variables first.
	      val relVarTypes = varTypes restrictTo f.vars
	      val skoFun = "skf_" + skfCtr.next()
	      val skoTermRank = Rank(relVarTypes.typesOf -> x.typeOf)
	      // See if we get a BG or a FG term
	      if ((Sigma.BGTypes contains skoTermRank.resType) && 
		  skoTermRank.argsTypes.isEmpty && // i.e. a constant
		  Flags.paramsOpSet.value == "BG") {
		Sigma = Sigma addBG (skoFun -> skoTermRank)
		sigma += (x.varOf -> FreeBGConst(skoFun))
	      }
	      else {
		// Foreground Term
		Sigma += (skoFun -> skoTermRank)
		sigma += (x.varOf -> FunTerm(skoFun, relVarTypes.varsOf))
	      }
	    }
	    hTseitin(sigma(f1), embeddingOp, varTypes)
	  }

	  case Iff(f1, f2) => {
	    // f is of the form f1 <=> f2
	    // The result is (f1Pos => f2Pos) /\ (f2Neg => f1Neg)
	    // where open is extended by
	    // Neg(f1Pos) => Neg(f1)     (contrapositive of f1 => f1Pos)
	    // f2Pos => f2
	    // f1Neg => f1
            // Neg(f2Neg) => Neg(f2)     (contrapositive of f2 => f2Neg)
	    // If f1 is simple then f1Neg, f1Pos don't have to be built,
	    // similarly for f2.
	    // todo: skolemize in place if isSimple
	    val f1Pos = if (isSimpleNeg(f1)) f1 else definition(false, f1.nameFor, f1, varTypes)
	    val f2Pos = if (isSimplePos(f2)) f2 else definition(true,  f2.nameFor, f2, varTypes)
	    val f1Neg = if (isSimplePos(f1)) f1 else definition(true,  f1.nameFor, f1, varTypes)
	    val f2Neg = if (isSimpleNeg(f2)) f2 else definition(false, f2.nameFor, f2, varTypes)
	    And(Implies(f1Pos, f2Pos), Implies(f2Neg, f1Neg))
	  }

	  case BinOpForm(op, f1, f2) => {
	    // op can be And or Or only
	    if (embeddingOp == None || (embeddingOp == Some(op))) 
	      // Continue descending
	      BinOpForm(op, 
			hTseitin(f1, Some(op), varTypes), 
			hTseitin(f2, Some(op), varTypes))
	    else 
	      // embeddingOp is different to op, so we need to extract.
	      // Context can only be a positive one, as all negation has been pushed
	      // inwards and we're not inside an Iff
	      definition(true, f.nameFor, f, varTypes)
	  }
	}
      }

      // Body of Tseitin
      while (!open.isEmpty) {
	// Select the first open element 
	// Invariant: 
	val (selectedName, selectedBody, varTypes) = open.head
	//println("==> selected = " + selected)
	open = open.tail
	done ::= Implies(selectedName, hTseitin(selectedBody, None, varTypes)).
	         univClosure(varTypes)
      }
      done
    }

    /**
     * Apply a given list of FormulaRewriteRules, innermost-first order
     */
    def reduceInnermost(rules: FormulaRewriteRules):Formula = {
      // Rewrite the subformulas of this
      // println("rewrite: " + this)
      val h = this match {
	case Atom(_, _) => this
	case UnOpForm(op, f) => UnOpForm(op, f.reduceInnermost(rules))
	case BinOpForm(op, f1, f2) => BinOpForm(op, f1.reduceInnermost(rules), 
						    f2.reduceInnermost(rules))
	case QuantForm(q, xs, f) => QuantForm(q, xs, f.reduceInnermost(rules))
      }
      // Rule applicable at top-level?
      if (rules isDefinedAt h) 
	// Apply it, and start over
	rules(h).reduceInnermost(rules)
      else
	// No rule is applicable at top level
	// and as all subformulas are rewritten we can stop
	h
    }

    /**
     * Apply a given list of FormulaRewriteRules, outermost-first order
     */
    def reduceOutermost(rules: FormulaRewriteRules):Formula = {

      def hReduceOutermost(f: Formula):Option[Formula] =
	if (rules isDefinedAt f)
	  // apply it, and this is the result
	  Some(rules(f))
	else f match {
	  case Atom(_, _) => None
	  case UnOpForm(op, g) => { 
	    hReduceOutermost(g) match {
	      case None => None
	      case Some(gRes) => Some(UnOpForm(op, gRes))
	    }
	  }
	  case BinOpForm(op, g1, g2) => { 
	    hReduceOutermost(g1) match {
	      case None => { 
		hReduceOutermost(g2) match {
		  case None => None
		  case Some(g2Res) => Some(BinOpForm(op, g1, g2Res))
		}
	      }
	      case Some(g1Res) => Some(BinOpForm(op, g1Res, g2))
	    }
	  }
	  case QuantForm(q, xs, g) => { 
	    hReduceOutermost(g) match {
	      case None => None
	      case Some(gRes) => Some(QuantForm(q, xs, gRes))
	    }
	  }
	  case x => {
	    println("should not get " + x)
	    None
	  }
	}

      // Body of reduceOutermost
      var f = this
      var fReduced = hReduceOutermost(f)
      while (fReduced != None) {
	f = fReduced.get
	fReduced = hReduceOutermost(f)
      }
      f
    }
  }

  /**
   * The syntactic classes of all formulas
   */
  
  case class Atom(pred: String, args:List[Term]) extends Formula {
    val vars = args.vars
    val rvars = args.rvars
    val params = args.params
    val freeBGConsts = args.freeBGConsts

    def matchers(that: Formula, gammas:List[Subst]) = 
      that match {
	case Atom(thatpred, thatargs) => 
	  if (pred == thatpred)
	    Expression.matchers(args, thatargs, gammas)
	  else 
	    List()
	case _ => List()
      }

    def applySubst(sigma: Subst) = Atom(pred, sigma(args))

    def applyCSubst(rvt: (SymBGConst, FunTerm)) = Atom(pred, args map { _.applyCSubst(rvt) })

    override def toString = 
      if (pred == "=") 
	"(" + args(0).toString + " ≈ " + args(1).toString + ")" 
      else
	Sigma.getFormatFn(pred)(args)
	// pred + args.toMyString("","(",",",")")

    // Convert an Atom to an equation.
    // Assume it is wel-typed.
    def toEqn(varTypes: List[TypedVar]) = 
      if (pred == "=") {
	// We need to figure out the type of the equation.
	// The critical case is an equation between two variables.
	// This is when the varTypes map in sig is needed.
	// Because we assume well-typedness it suffices to look at one argument
	val typ = Sigma.typeOf(args(0), varTypes)
	// val typ = IType
	Eqn(args(0),args(1), typ) 
      }
      else 
	Eqn(FunTerm(pred, args), TT, OType)
	// PredEqn(pred,args) 
  }

  // Equations *are* atoms (with predicate symbol "=")
  // Equality is polymorphic, and the type of Eqn in the clausal form later
  // will be determined in the clause normalform transformation later
  object Equation {
    def apply(s: Term, t:Term) = new Atom("=", List(s, t)) 
    def unapply(f: Formula) = f match {
      case Atom("=", s :: t :: Nil) => Some((s,t))
      case _ => None
    }
  }

  // Disequations are currently used internally by QE only.
  // Handy to introduce them here generally.
  object DisEquation {
    def apply(s: Term, t:Term) = new Atom("!=", List(s, t)) 
    def unapply(f: Formula) = f match {
      case Atom("!=", s :: t :: Nil) => Some((s,t))
      case _ => None
    }
  }


  def Comment(s: String) = Atom("$comment", List(Const(""""""" + s + """"""")))


  case class UnOpForm(op: UnOp, f: Formula) extends Formula  {
    val vars = f.vars
    val rvars = f.rvars
    val params = f.params
    val freeBGConsts = f.freeBGConsts

    def matchers(that: Formula, gammas:List[Subst]) = 
      that match {
	case UnOpForm(thatop, thatf) => 
	  if (op == thatop) f.matchers(thatf, gammas) else List()
	case _ => List()
      }

    def applySubst(sigma: Subst) = UnOpForm(op, sigma(f))

    def applyCSubst(rvt: (SymBGConst, FunTerm)) = UnOpForm(op, f.applyCSubst(rvt))

    override def toString = op + f.toString
  }

  abstract class Op

  abstract class UnOp extends Op{
    override def toString: String
  }
  object Neg extends UnOp {
    override def toString = "¬"
    def apply(f: Formula) = UnOpForm(Neg, f)
    def unapply(g: Formula) = 
      g match {
	case UnOpForm(Neg, f) => Some(f)
	case _ => None
      }
  }

  case class BinOpForm(op: BinOp, f1: Formula, f2: Formula) extends Formula {
    val vars = f1.vars union f2.vars
    val rvars = f1.rvars union f2.rvars
    val params = f1.params union f2.params
    val freeBGConsts = f1.freeBGConsts union f2.freeBGConsts

    def matchers(that: Formula, gammas:List[Subst]) = 
      that match {
	case BinOpForm(thatop, thatf1, thatf2) => 
	  if (op == thatop)
	    Expression.matchers(List(f1,f2), List(thatf1,thatf2), gammas)
	  else 
	    List()
	case _ => List()
      }
				

    override def toString = "(" + f1.toString + " " + op.toString + " " + f2.toString + ")"
    def applyCSubst(rvt: (SymBGConst, FunTerm)) = BinOpForm(op, f1.applyCSubst(rvt), f2.applyCSubst(rvt))

    def applySubst(sigma: Subst) = BinOpForm(op, sigma(f1), sigma(f2))

  }

  abstract class BinOp extends Op { override def toString: String  }

  object And extends BinOp {
    override def toString = "∧"
    def apply(f1: Formula, f2: Formula) = BinOpForm(And, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(And, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }
  object Or extends BinOp {
    override def toString = "∨"
    def apply(f1: Formula, f2: Formula) = BinOpForm(Or, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(Or, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }

  object Iff extends BinOp {
    override def toString = "⇔"
    def apply(f1: Formula, f2: Formula) = BinOpForm(Iff, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(Iff, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }

  object IffNot extends BinOp {
    override def toString = "⇎"
    def apply(f1: Formula, f2: Formula) = BinOpForm(IffNot, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(IffNot, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }


  object Implies extends BinOp {
    override def toString = "⇒"
    def apply(f1: Formula, f2: Formula) = BinOpForm(Implies, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(Implies, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }

  object Implied extends BinOp {
    override def toString = "⇐"
    def apply(f1: Formula, f2: Formula) = BinOpForm(Implied, f1, f2)
    def unapply(g: Formula) = 
      g match {
	case BinOpForm(Implied, f1, f2) => Some((f1, f2))
	case _ => None
      }
  }

  case class QuantForm(q: Quantifier, xs: List[TypedVar], f:Formula) extends Formula {
    assume(!xs.isEmpty, { println("Empty list of variables in quantification") })
    val vars = f.vars -- xs.varsOf
    val rvars = f.rvars
    val params = f.params
    val freeBGConsts = f.freeBGConsts

    def matchers(that: Formula, gammas: List[Subst]) = {
      assert(false, { println("Formula.scala: matchers on quantified formulas not implemented") })
      List()
    }

    // As usual, unintended capturing of variables in the range of sigma by quantified
    // variable must be avoided. Renaming away the quantified variable before applying sigma
    // solves the problem.
    def applySubst(sigma: Subst) = {
      val (rho, xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, sigma(rho(f)))
    }

    def applyCSubst(rvt: (SymBGConst, FunTerm)) = {
      val (rho, xsrho) = xs.mkRenaming()
      QuantForm(q, xsrho, rho(f).applyCSubst(rvt))
    }


    override def toString = "(" + q + " " + (xs map { _.toMyString }).toMyString(""," ","") + " " + f + ")"
  }

    abstract class Quantifier { 
    def dual: Quantifier
    override def toString: String  
  }

  object Forall extends Quantifier {
    override def toString = "∀"
    def dual = Exists
    def apply(xs: List[TypedVar], f:Formula) = QuantForm(Forall, xs, f)
    def unapply(g: Formula) = 
      g match {
	case QuantForm(Forall, xs, f) => Some((xs, f))
	case _ => None
      }
  }

  object Exists extends Quantifier {
    override def toString = "∃"
    def dual = Forall
    def apply(xs: List[TypedVar], f:Formula) = QuantForm(Exists, xs, f)
    def unapply(g: Formula) = 
      g match {
	case QuantForm(Exists, xs, f) => Some((xs, f))
	case _ => None
      }
  }

  val skfCtr = new Counter

  val defCtr = new Counter


  
  // def varsTypes(vts: List[(Var,Type)]) = vts map { _._2 }

} 

