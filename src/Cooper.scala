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

object Cooper {


  import Term._
  import Predefined._
  import Formula._
  import Misc._
  import Integers._
  import Subst._
  import Int._

  /**
   * Quantifier elimination a la Cooper
   * Quite basic, over <, = and != atoms.
   * Notice the =-atoms that can be used as rewrite rules are handled extraneously
   * in BGContext.scala
   */

  // The representation of -infinity
  val MinValueBGLitConst = BGLitConst(MinValue)

  // Divisibility constraints n|t
  // Notice we introduce a new subclass of Atom, which is necessary to hold the polynomial
  class Divides(val n: Int, val p:Polynomial) extends Atom("$divides", List(BGLitConst(n), p.toTerm)) {

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = 
      // Ugly: first convert to a term, do the replacement, then convert back to a Polynomial
      // Notice the normalization invariant is preserved.
      
      if (rvt._2 == MinValueBGLitConst)
	// This indicates we are going to construct the elimination formula for -infinity.
	// Don't modify the divisibility constraint then.
	this
      else if (p.symBGConsts contains rvt._1)
	Divides(n, toPolynomial(p.toTerm.applyCSubst(rvt)))
      else
	// don't bother looking into terms
	this

    override def applySubst(sigma: Subst) = {
      assert(false, { println("Trying to apply a substitution to a Divisibility constraint, which should never be necessary") })
      // Dummy
      this
    }
    // not necessary - have a format definition for $divides in Predefined
    // override def toString = n + "|" + t
  }
  
  object Divides {
    // def apply(n: Int, p: Polynomial) = 
    // 	  new Divides(n, p)
    def apply(n: Int, p: Polynomial) = {
      p match { 
    	case Polynomial(k, Nil) =>
    	  // Constant case
     	  if ((k % n) == 0) TrueAtom else FalseAtom
     	case p => {
     	  // Undecided case
	  val h = (math.abs(n) :: (p.ms map { m => math.abs(m.k) })) reduceLeft { gcd(_, _) }
	  if (h == n)
	    if (p.k % n == 0)
	      TrueAtom
	    else
	      FalseAtom
	  else {
	    val g = gcd(math.abs(n), p.gcdCoeffs)
     	    val res = 
	      if (math.abs(n / g) == 1)
		TrueAtom
	      else if (n < 0) 
		new Divides(n / -g, p / -g) // g is always positive
	      else
		new Divides(n / g, p / g) // g is always positive
	    // println(res)
	    res
	  }
	}
      }
    }

    def unapply(f: Formula) = 
      f match {
	case d:Divides => Some((d.n, d.p))
	case _ => None
      }
  }

  // MonoLTPoly(m,p) stands for m < p where m is a monomial and p is a polynomial.
  // Assume that the variable in m does not occur in p.
  class MonoLTPoly(val m: Monomial, val p: Polynomial) extends Atom("$less", List(m.toTerm, p.toTerm)) {

    // applyCSubst: applies only if the RVar to be eliminated is the one in m, 
    // and m has a unit coefficient
    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = {
      assume(m.c == rvt._1 && m.k == 1, { println("applyCSubst on non-appropriate monomial: " + this) })
      if (rvt._2 == MinValueBGLitConst)
	// Building the -infinity elimination formula
	TrueAtom
      else
	ZeroLTPoly(p - toPolynomial(rvt._2))
    }

    override def toString = m.toString + " < " + p.toString

  }
  
  object MonoLTPoly {
    def apply(m: Monomial, p: Polynomial) = {
      val g = gcd(math.abs(m.k), p.gcdCoeffs)
      new MonoLTPoly(m / g , p / g)
    }

    def unapply(f: Formula) = 
      f match {
	case f:MonoLTPoly => Some(f.m, f.p)
	case _ => None
      }
  }

  // PolyLTMono(p,m) stands for p < m where m is a monomial and p is a polynomial.
  // Assume that the variable in m does not occur in p.
  class PolyLTMono(val p: Polynomial, val m: Monomial) extends Atom("$less", List(p.toTerm, m.toTerm)) {

    override def applyCSubst(rvt: (SymBGConst, FunTerm)) = {
      assume(m.c == rvt._1 && m.k == 1, { println("applyCSubst on non-appropriate monomial: " + this) })
      if (rvt._2 == MinValueBGLitConst)
	// Building the -infinity elimination formula
	FalseAtom
      else
	ZeroLTPoly(toPolynomial(rvt._2) - p)
    }

    override def toString = p.toString + " < " + m.toString
  }
  
  object PolyLTMono {
    def apply(p: Polynomial, m: Monomial) = {
      val g = gcd(math.abs(m.k), p.gcdCoeffs)
      new PolyLTMono(p / g, m / g)
    }

    def unapply(f: Formula) = 
      f match {
	case f:PolyLTMono => Some(f.p, f.m)
	case _ => None
      }
  }


  /**
   * rearrange(f: Formula, x: SymBGConst, lcm: Int)
   * Rearrange the LessX atoms in f into
   * MonoLTPoly or PolyLTMono atoms, depending on the given rv,
   * and separate out rv with a positive *unit* coefficient.
   * If k is the coefficient of rv in f then multiply the remaining
   * polynomial with lcm/k.
   * Leave a LessX atom untouched if it does not contain rv.
   *
   * More formally:
   * given 0 < p + kx and assume k|lcm, and let d = lcm/k
   * Consider
   *   -dp < dkx if k is positive (and so is d), and
   *   dkx < -dp if k is negative (and so is d)
   * Both cases are equivalent to the given one.
   * In the first case return -dp < x and in the second case return x < -dp
   * That is, x gets a unit coefficient, and that is ok if the divisibility
   * constraint lcm | x is satisfied
   *
   * For divisibility constraints transform
   * n | p + kx
   * into
   * dn | dp + x
   *
   * For equational constraints transform
   *  0 = p + kx
   * into
   *  0 =  dp + x
   * Because d is positive iff k is, dp will always have the right sign
   * (and x has a positive unit coefficient)
   *
   * Disequations: similarly
   */

  def rearrange(f: Formula, x: SymBGConst, lcm: Int):Formula =
    f match {
      case BinOpForm(op, f1, f2) => 
	BinOpForm(op, rearrange(f1, x, lcm), rearrange(f2, x, lcm))
      case ZeroEQPoly(hp) =>
	if (! (hp.symBGConsts  contains x))
	  // nothing to rearrange
	  f
	else {
	  val (kx, p) = hp.extract(x)
	  val d = lcm / kx.k
	  // give the new monomial a unit coefficient
	  val onex = Monomial(1, kx.c)
	  val dp = p * d
	  ZeroEQPoly(dp + onex)
	}
      case ZeroNEPoly(hp) =>
	if (! (hp.symBGConsts  contains x))
	  // nothing to rearrange
	  f
	else {
	  val (kx, p) = hp.extract(x)
	  val d = lcm / kx.k
	  // give the new monomial a unit coefficient
	  val onex = Monomial(1, kx.c)
	  val dp = p * d
	  ZeroNEPoly(dp + onex)
	}
      case Divides(n, hp) =>
	if (! (hp.symBGConsts  contains x))
	  // nothing to rearrange
	  f
	else {
	  val (kx, p) = hp.extract(x)
	  val d = lcm / kx.k
	  // give the new monomial a unit coefficient
	  val onex = Monomial(1, kx.c)
	  val dp = p * d
	  Divides(d*n, dp + onex) // d*n could be negative, but not a problem
	}
      case ZeroLTPoly(hp) =>
	if (! (hp.symBGConsts  contains x))
	  // nothing to rearrange
	  f
	else {
	  val (kx, p) = hp.extract(x)
	  val d = lcm / kx.k
	  // give the new monomial a unit coefficient
	  val onex = Monomial(1, kx.c)
	  val minusdp = p * -d
	  if (kx.k > 0)
	    PolyLTMono(minusdp, onex)
	  else
	    // d is negative, use -d to be positive again
	    MonoLTPoly(onex, minusdp)
	}
      case f => f
    }

  // return the coefficients of x in f
  def coeffs(f: Formula, x: SymBGConst):List[Int] =
    f match {
      case BinOpForm(op, f1, f2) => coeffs(f1, x) ::: coeffs(f2, x)
      case Divides(n, p) => 
	(p.ms find { _.c == x }) match {
	  case Some(Monomial(k,_)) => List(k)
	  case None => List()
	}
      case ZeroEQPoly(p) => 
	(p.ms find { _.c == x }) match {
	  case Some(Monomial(k,_)) => List(k)
	  case None => List()
	}
      case ZeroNEPoly(p) => 
	(p.ms find { _.c == x }) match {
	  case Some(Monomial(k,_)) => List(k)
	  case None => List()
	}
      case ZeroLTPoly(p) => 
	(p.ms find { _.c == x }) match {
	  case Some(Monomial(k,_)) => List(k)
	  case None => List()
	}
      case _ => List()
    }

  // return the constants of the divisibility atoms in f that contain x
  def divisibilityConsts(f: Formula, x: SymBGConst):List[Int] =
    f match {
      case BinOpForm(op, f1, f2) => divisibilityConsts(f1, x) ::: divisibilityConsts(f2, x)
      case Divides(n, p) => if (p.symBGConsts contains x) List(n) else List()
      case _ => List()
    }

  /**
   * Return the set of lower bounds polynomials of rv in f.
   * Assume that f has been rearranged for x
   */
  def lowerBounds(f: Formula, x: SymBGConst):Set[Polynomial] =
    f match {
      case BinOpForm(op, f1, f2) => 
	lowerBounds(f1, x) union lowerBounds(f2, x)
      case PolyLTMono(p, m) => if (m.c == x) Set(p) else Set()
      case ZeroNEPoly(hp) => 
	if (hp.symBGConsts contains x) {
	  val (onex, p) = hp.extract(x)
	  Set(p * -1)
	} else Set() // does not provide a lower bound
      case ZeroEQPoly(hp) => 
	if (hp.symBGConsts contains x) {
	  val (onex, p) = hp.extract(x)
	  Set((p + 1) * -1)
	} else Set() // does not provide a lower bound
      case _ => Set() // Because normalized for x we can ignore 
      // ZeroLTPoly atoms, those that had contained x have been rearranged into
      // PolyLTMono or MonoLTPoly atoms.
    }

  // Eliminate the rigid variable rv from the (conjunction of the) formulas fs.
  // Return a sequence of formulas that is satisfiable if and only if fs is.
  def QE(x: SymBGConst, fs: List[Formula]):List[Formula] = {

    // println("--> QE, formulas ")
    // for (f <- fs)
    //   println(f)

    // println("--> Eliminating " + x)
    // Isolate the relevant formulas in f, those that contain rv
    val (fsX, fsNoX) = {
      x match {
	case x:Param => fs partition { _.params contains x }
	case x:RVar => fs partition { _.rvars contains x }
	case x:FreeBGConst => fs partition { _.freeBGConsts contains x }
      }
    }

    if (fsX.isEmpty)
      return fsNoX

    // Get the coefficients of x in fsX
    val xCoeffs = fsX flatMap { coeffs(_, x) }
    // println("--> coefficients of " + x + ": " + xCoeffs)

    // Their LCM
    val xCoeffsLCM = xCoeffs.foldLeft(1)((m,n) => lcm(m, math.abs(n)))
    // println("--> LCM is " + xCoeffsLCM)

    // Rearrange for x and add the divisibility constraint.
    // This gives the elimination formula.
    val fsXforX = Divides(xCoeffsLCM, Polynomial(0, List(Monomial(1,x)))) :: (fsX map { rearrange(_, x, xCoeffsLCM) })
    // println("--> fs rearranged for " + x)
    // for (f <- fsXforX) 
    //   println("      " +f)

    val elimForm = fsXforX.to(TrueAtom,And)

    val elimFormDivConsts = divisibilityConsts(elimForm, x)
    // println("--> its divisibilty constants: " + elimFormDivConsts)

    // Their LCM
    val delta = elimFormDivConsts.foldLeft(1)((m,n) => lcm(m, math.abs(n)))
    // println("--> LCM delta is " + delta)

    // The -infinity formula
    val elimFormMInfty = 
      elimForm.applyCSubst(x -> MinValueBGLitConst).reduceInnermost(elimTrivial)
    // println("--> -infinity formula: " + elimFormMInfty)

    if (elimFormMInfty == TrueAtom)
      return fsNoX

    val B = lowerBounds(elimForm, x)
    // println("--> lower bounds: " + B)

    // println("--> instantiated -infinity formula, for " + 1 + " .. " + delta)
    val or1AsList = 
      for (j <- 1 to delta;
	   h = elimFormMInfty.applyCSubst(x, BGLitConst(j)).reduceInnermost(elimTrivial)) yield {
	     // println("    " + h)
	     if (h == TrueAtom)
	       return fsNoX
	     h
	   }

    // println("--> instantiated elimination formula, for " + 1 + " .. " + delta + " and lower bound " + B)
    val or2AsList = 
      for (j <- 1 to delta;
	   b <- B;
	   h = elimForm.applyCSubst(x, (b + j).toTerm).reduceInnermost(elimTrivial)) yield {
	     // println("--> j = " + j + ", b = " + b)
	     // println(h)
	     if (h == TrueAtom)
	       return fsNoX
	     h
    }

    // Finally, the result
    val or = (or1AsList ++ or2AsList).to(FalseAtom, Or).reduceInnermost(elimTrivial)
    val res = 
      if (or == FalseAtom)
	List(FalseAtom)
      else or :: fsNoX
    // println("--> result")
    // println(res)
    res
  }

  // remove all xs from the given list of normalized formulas
  def QE(xs: Iterable[SymBGConst], fs: List[Formula]):List[Formula] = {
    var current = fs
    for (x <- xs) {
      current = QE(x, current)
      if (current contains FalseAtom)
	return List(FalseAtom)
    }
    return current
  }

}
