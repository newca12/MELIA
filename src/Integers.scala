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

object Integers {

  // Todo: clear modularization of background reasoning,
  // including modularizing the QE procedure, which is currently Cooper, hard-coded.
  // A bit of a mess currently.

  import Predefined._
  import Term._
  import Formula._
  import Misc._
  import Subst._
  import Cooper._

  // these classes could be used by the parser as well, but no need to

  object LessEq {
    def apply(s: Term, t: Term) = Atom("$lesseq", List(s, t))
    def unapply(f: Formula) = 
      f match { 
	case Atom("$lesseq", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  object Less {
    def apply(s: Term, t: Term) = Atom("$less", List(s, t))
    def unapply(f: Formula) = 
      f match { 
	case Atom("$less", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  object GreaterEq {
    def apply(s: Term, t: Term) = Atom("$greatereq", List(s, t))
    def unapply(f: Formula) = 
      f match { 
	case Atom("$greatereq", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  object Greater {
    def apply(s: Term, t: Term) = Atom("$greater", List(s, t))
    def unapply(f: Formula) = 
      f match { 
	case Atom("$greater", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  /**
   * Terms
   */

  object Sum {
    def apply(s: Term, t: Term) = FunTerm("$sum", List(s, t))
    def unapply(t: Term) = 
      t match { 
	case FunTerm("$sum", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  /**
   * Varyadic
   */
  object Sums {
    def apply(ts: List[Term]) = FunTerm("$sum", ts)
    def unapply(t: Term) = 
      t match { 
	case FunTerm("$sum", ts) => Some(ts)
	case _ => None
      }
  }

  object Difference {
    def apply(s: Term, t: Term) = FunTerm("$difference", List(s, t))
    def unapply(t: Term) = 
      t match { 
	case FunTerm("$difference", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  object Product {
    def apply(s: Term, t: Term) = FunTerm("$product", List(s, t))
    def unapply(t: Term) = 
      t match { 
	case FunTerm("$product", s :: t :: Nil) => Some((s,t))
	case _ => None
      }
  }

  object UMinus {
    def apply(s: Term) = FunTerm("$uminus", List(s))
    def unapply(t: Term) = 
      t match { 
	case FunTerm("$uminus", s :: Nil) => Some((s))
	case _ => None
      }
  }

  val One = BGLitConst(1)
  val Zero = BGLitConst(0)
  val MinusOne = BGLitConst(-1)


/**
 * Monomials and Polynomials as a canonical representation of terms within inequalities
 * (ZeroLTPoly)
 */

  case class Monomial(k: Int, c: SymBGConst) {

    // * is only well-defined if n is non-zero
    def * (n: Int) = {
      assume(n != 0, { println("Multiplying a monomial by 0 should never occur") })
      Monomial(k*n, c)
    }

    // assume k is divisible
    def / (n: Int) = {
      assume(k % n == 0, { println("Dividing a monomial by a non-factor: " + this + " / " + n) })
      Monomial(k/n, c)
    }

    
    def toTerm = if (k == 1) c else Product(BGLitConst(k), c)

    // assume n is not zero
    override def toString = 
      k match {
	case 1 => c.toString
	case -1 => "-" + c.toString
	case k => k + c.toString
      }
  }

  // n is the constant in the polynome, ms is its (linear) monomials.
  // Invariant: each monomial is over a different variable
  case class Polynomial(k: Int, ms: List[Monomial]) {
    
    def gcdCoeffs = {
      val ks = (if (k == 0) List() else List(math.abs(k))) ::: (ms map { m => math.abs(m.k) })
      // println("GCD of " + ks)
      if (ks.isEmpty)
	1 // useful because 1 divides everything
      else {
	val res = ks reduceLeft { gcd(_, _) } 
	// println(res)
	res
      }
    }

    val symBGConsts = (ms map { _.c }).toSet[SymBGConst] // the "variables" in this polynomial

    // add a monomial, while preserving the invariant
    def + (m: Monomial):Polynomial = {
      // Iterate over ms and update or extend
      var skippedMs = List[Monomial]() 
      var oldMs = ms // Iteration variable
      while (!oldMs.isEmpty) {
	val hm = oldMs.head
	oldMs = oldMs.tail
	if (hm.c == m.c)  
	  // found it, update the coefficient
	  return Polynomial(k, skippedMs.reverse ::: 
			    ( if (hm.k + m.k == 0) 
			      oldMs
			     else 
			       Monomial(hm.k + m.k, m.c)  :: oldMs))
        else
	  skippedMs ::= hm
      }
      // Coming here means that m was not found - add it
      return Polynomial(k, m :: ms)
    }
    // add an integer constant to a polynomial
    def + (n: Int):Polynomial = Polynomial(k+n, ms)

    // Subtraction of monomials
    def - (n: Int):Polynomial = Polynomial(k-n, ms)
    def - (m: Monomial):Polynomial = this + (m * -1)

    // Addition of a polynomial
    def + (p: Polynomial):Polynomial = {
      var res = this + p.k // the constant in p
      // add one monomial in p after the other
      p.ms foreach { m => res += m }
      res
    }

    // Multiplication by a constant 
    def * (n: Int):Polynomial = 
      n match { 
	case 0 => Polynomial(0, List())
	case 1 => this
	case n => Polynomial(k*n, ms map { _ * n })
      }

    // Division by a constant 
    // assume every coefficient and the constant are divisble by it.
    def / (n: Int):Polynomial = 
      n match { 
	case 1 => this
	case n => Polynomial(k / n, ms map { _ / n })
      }

    def factorize = this / gcdCoeffs


    // Subtraction of a polynomial
    def - (p: Polynomial):Polynomial = this + (p * -1)

    override def toString = 
      if (ms.isEmpty) 
	k.toString
      else 
	ms.toMyString("", " + ", "") + (if (k == 0) "" else " + " + k)

    def toTerm = Sums((if (k == 0) List() else List(BGLitConst(k))) ::: (ms map { _.toTerm }))

    // extract the monomial with the given rv from this.
    // Return the pair of that extracted monomial and the remainder polynomial
    def extract(rv: SymBGConst) = 
      // Scala is incredible:
      ms partition { _.c == rv } match {
	case (m :: Nil, newms) => (m, Polynomial(k, newms))
	  case _ => throw new InternalError("extract: cannot extract monomial with symbolic constant " + rv + " from " + this)
      }
  }
  
  /**
   * Turn t into a polynomial
   */
  def toPolynomial(t: Term):Polynomial = {
    // println("toPoly: " + t)
    t match {
      case BGLitConst(n) => Polynomial(n, List())
      case c:SymBGConst => Polynomial(0, List(Monomial(1, c)))
      case Sums(ts) => ts.foldLeft (Polynomial(0,List())) (_ + toPolynomial(_))
      case Product(hs, ht) => { 
	(toPolynomial(hs), toPolynomial(ht)) match {
	  case (Polynomial(n, Nil), ts) => ts * n
	  case (ts, Polynomial(n, Nil)) => ts * n
	  case (_, _) => 
	    throw new SyntaxError("Cannot normalize into a linear term: " + t)
	}
      }
      case Difference(hs, ht) => toPolynomial(hs) - toPolynomial(ht)
      // Rules to eliminate UMinus
      case UMinus(ht) => toPolynomial(ht) * -1
      // The above should cover all cases
      // case t => throw new SyntaxError("toPolynomial: cannot normalize this term: " + t)
    }
  }


  /*
   * normalize(f): f is a variable-free formula over the background signature (currently) without
   * quantifiers and whose only operators are And, Or and Neg. The result is a list of (positive) formulas, implicitly
   * conjoined, without Neg 
   * and where all predicates except Less have been removed. All Less predicates are in fact ZeroLTPoly predicates, i.e., 
   * are of the form 0 < p, where p is a Polynomial.
   */

  def normalize(f: Formula):List[Formula] = {

    def simplifyAndList(fs: List[Formula]) =
    // May result in empty List
      if (fs contains FalseAtom) List(FalseAtom) else (fs filter { _ != TrueAtom })

    def hnorm(f: Formula):List[Formula] =
      f match {
	case TrueAtom             => List()
	case FalseAtom            => List(f)
	case Less(s, t)           => 
	  ZeroLTPoly(toPolynomial(t) - toPolynomial(s)) match {
	    case TrueAtom => List()
	    case other => List(other) // including case of FalseAtom
	  }
	case LessEq(s, t)         => hnorm(Less(s, Sum(t, One)))
	case GreaterEq(s, t)      => hnorm(Less(t, Sum(s, One)))
	case Greater(s, t)        => hnorm(Less(t, s))
	case Neg(Less(s, t))      => hnorm(GreaterEq(s, t))
	case Neg(LessEq(s, t))    => hnorm(Greater(s, t))
	case Neg(Greater(s, t))   => hnorm(LessEq(s, t))
	case Neg(GreaterEq(s, t)) => hnorm(Less(s, t))
	// s = t => 0 = t - s
/*
  case Equation(s, t) => hnorm(And(GreaterEq(s, t),
					 GreaterEq(t, s)))
	case Neg(Equation(s, t)) => 
	    hnorm(Or(Less(s, t), Less(t, s)))
*/
	case Equation(s, t) => 
	   ZeroEQPoly(toPolynomial(t) - toPolynomial(s)) match {
	     case TrueAtom => List()
	     case other => List(other) // including case of FalseAtom
	   }
	case DisEquation(s, t) => 
	   ZeroNEPoly(toPolynomial(t) - toPolynomial(s)) match {
	     case TrueAtom => List()
	     case other => List(other) // including case of FalseAtom
	   }
	case Neg(Equation(s, t)) => 
	  ZeroNEPoly(toPolynomial(t) - toPolynomial(s)) match {
	    case TrueAtom => List()
	    case other => List(other) // including case of FalseAtom
	  }
	case Neg(DisEquation(s, t)) => 
	  ZeroEQPoly(toPolynomial(t) - toPolynomial(s)) match {
	    case TrueAtom => List()
	    case other => List(other) // including case of FalseAtom
	  }
	case Or(f1, f2) => 
	  (hnorm(f1), hnorm(f2)) match {
	    case (FalseAtom :: Nil, f2n) => f2n
	    case (f1n, FalseAtom :: Nil) => f1n
	    // Nil is logically seen TrueAtom
	    case (Nil, _) => List()
	    case (_, Nil) => List()
	    case (f1n, f2n) => List(Or(f1n.to(TrueAtom, And), 
				       f2n.to(TrueAtom, And)))
	  }
	case Neg(Neg(f)) => hnorm(f)
	case Neg(Or(f1, f2)) => hnorm(And(Neg(f1), Neg(f2)))
	case And(f1, f2) => simplifyAndList(hnorm(f1) ::: hnorm(f2))
	case Neg(And(f1, f2)) => hnorm(Or(Neg(f1), Neg(f2)))
	case Divides(n, p) => List(Divides(n, p))
	case Neg(Divides(n, p)) => 
	  List(Neg(Divides(n, p)).reduceInnermost(elimTrivial))
	// Divisibility predicates will occur only positively.
	// But at the time hnorm is called, Divides atoms should not
	// occur anyway in f
      }

    // Body of normalize
    // println("==> normalize: " + f)
    val res = hnorm(f)
    // println("==> result: " + res)
    if (res contains FalseAtom)
      throw new Inconsistent
    else
      res
  }
      

  // For QE we assume that the formulas in the background context are always 
  // normalized. The atoms will always be ZeroLTPoly atoms or Divides atoms.
  // Invariant: must make sure that these atoms remain normalized if applyCSubst is applied.

  // ZeroLTPoly(p) stands for 0 < p
  class ZeroLTPoly(val p: Polynomial) extends Atom("$less", List(Zero, p.toTerm)) {

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = 
      if (!(p.symBGConsts contains rvt._1))
      // pre-test - rvt won't act on this, so don't bother with normalization
	this
      else {
	// println(" --> applyCSubst: " + rvt + " applied to " + this + " gives ... ")
	// println(p.toTerm)
	// println((p.toTerm.applyCSubst(rvt)))
	val res = ZeroLTPoly(toPolynomial(p.toTerm.applyCSubst(rvt)))
	// val res = ZeroLTPoly(toPolynomial(p.toTerm))
	// println(" --> applyCSubst: " + rvt + " applied to " + this + " gives " + res)
	res
      }

    override def applySubst(sigma: Subst) = {
      assert(false, { println("Trying to apply a substitution to a ZeroLTPoly literal should never be necessary") })
      // Dummy
      this
    }

    // We could use the infix declaration with Less, but this one looks lighter
    override def toString = "0 < " + p.toString

  }
  
  object ZeroLTPoly {
    def apply(p: Polynomial) =
      // Check for trivial cases first 
      p match {
	case Polynomial(k, Nil) =>
	  if (k > 0) TrueAtom else FalseAtom
	case p => new ZeroLTPoly(p.factorize)
      }

    def unapply(f: Formula) = 
      f match {
	case f:ZeroLTPoly => Some(f.p)
	case _ => None
      }
  }


  // ZeroEQPoly(p) stands for 0 = p
  class ZeroEQPoly(val p: Polynomial) extends Atom("=", List(Zero, p.toTerm)) {

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = 
      if (!(p.symBGConsts contains rvt._1))
	// pre-test - rvt won't act on this, so don't bother with normalization
	this
      else if (rvt._2 == MinValueBGLitConst)
	// Building the -infinity elimination formula
	FalseAtom
      else
	ZeroEQPoly(toPolynomial(p.toTerm.applyCSubst(rvt)))

    override def applySubst(sigma: Subst) = {
      assert(false, { println("Trying to apply a substitution to a ZeroEQPoly literal should never be necessary") })
      // Dummy
      this
    }

    // We could use the infix declaration with Less, but this one looks lighter
    override def toString = "0 = " + p.toString

  }
  
  object ZeroEQPoly {
    def apply(p: Polynomial) =
      // Check for trivial cases first 
      p match {
	case Polynomial(k, Nil) =>
	  if (k == 0) TrueAtom else FalseAtom
	case p => new ZeroEQPoly(p.factorize)
      }

    def unapply(f: Formula) = 
      f match {
	case f:ZeroEQPoly => Some(f.p)
	case _ => None
      }
  }

  // ZeroNEPoly(p) stands for 0 != p
  class ZeroNEPoly(val p: Polynomial) extends Atom("!=", List(Zero, p.toTerm)) {

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = 
      if (!(p.symBGConsts contains rvt._1))
	// pre-test - rvt won't act on this, so don't bother with normalization
	this
      else if (rvt._2 == MinValueBGLitConst)
	// Building the -infinity elimination formula
	TrueAtom // xxx - is this correct?
	// this
      else
	ZeroNEPoly(toPolynomial(p.toTerm.applyCSubst(rvt)))

    override def applySubst(sigma: Subst) = {
      assert(false, { println("Trying to apply a substitution to a ZeroNEPoly literal should never be necessary") })
      // Dummy
      this
    }

    // We could use the infix declaration with Less, but this one looks lighter
    override def toString = "0 != " + p.toString

  }
  
  object ZeroNEPoly {
    def apply(p: Polynomial) =
      // Check for trivial cases first 
      p match {
	case Polynomial(k, Nil) =>
	  if (k == 0) FalseAtom else TrueAtom
	case p => new ZeroNEPoly(p.factorize)
      }

    def unapply(f: Formula) = 
      f match {
	case f:ZeroNEPoly => Some(f.p)
	case _ => None
      }
  }



  // Assume that fs is a list of normalized formulas
  def checkConsistency(fs: List[Formula]) {

    // println("==> Consistency check:")
    // for (f <- fs) 
    //   println(f)

    if (fs contains FalseAtom) {
      // println("==> inconsistent")
      throw new Inconsistent
    }

    val fsrvars = fs.rvars
    if (!fsrvars.isEmpty) 
      checkConsistency(QE(fsrvars.head, fs))
    else {
      val fsfreeBGConsts = fs.freeBGConsts
      if (!fsfreeBGConsts.isEmpty) 
	checkConsistency(QE(fsfreeBGConsts.head, fs))
      else {
	val fsparams = fs.params
	if (!fsparams.isEmpty) 
	  checkConsistency(QE(fsparams.head, fs))
	else {
	  // None of the above.
	  // All formulas without rvars, freebgconsts and params
	  // are directly evaluable, and because fs is normalized
	  // have been evaluated. Hence we get the result immediately
	  if (fs map { _.reduceInnermost(elimTrivial) } contains FalseAtom) {
	    // println("==> inconsistent")
	    throw new Inconsistent
	  }
	}
      }
    }
  }
}


