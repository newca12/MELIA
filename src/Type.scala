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

object Type {


  import Term._
  import Subst._

  // In the formuals below, variables are typed, i.e., the quantified variables
  // come with a type with their declaration.
  type TypedVar = (Var,Type)

  import Predefined._
  import Misc._
  import Formula._

  /**
   * The signature of the current clause sey.
   * Kept globally, for simplicity
   */

  case class Type(name: String) {
    override def toString = name
  }

  // Predefined types: $i: individuals, $o: truth values
  // var types = Set(IType, OType, IntType, raTType, RealType)

  /**
   * Rank: The signature of individual function (and predicate) symbols.
   */

  case class Rank(rank: (List[Type], Type)) {
    def argsTypes = rank._1
    def resType = rank._2
    override def toString = 
      (if (argsTypes.isEmpty) "" else  (argsTypes.toMyString("", " × ", "") + " → ")) + resType

  }

  // Convenience functions

  def Rank0(r: Type) = new Rank(List() -> r)
  def Rank1(r: (Type, Type)) = new Rank(List(r._1) -> r._2)
  def Rank2(r: ((Type, Type), Type)) = new Rank(List(r._1._1, r._1._2) -> r._2)
  def Rank3(r: ((Type, Type, Type), Type)) = new Rank(List(r._1._1, r._1._2, r._1._2) -> r._2)



  implicit def toMyTypedVar(x: TypedVar) = new MyTypedVar(x)
  implicit def toMyTypedVars(xs: List[TypedVar]) = new MyTypedVars(xs)

  class MyTypedVar(x: TypedVar) {
    def varOf = x._1
    def typeOf = x._2
    def toMyString = varOf + (if (typeOf == IType) "" else  ":" + typeOf)
  }

    // Would it pay off to introduce an explict class for lists of TypeVar?
    // And to represent it as a Map?
  class MyTypedVars(xs: List[TypedVar]) {
    def varsOf = (xs map { _.varOf })
    def typesOf = (xs map { _.typeOf })

    // mkRenaming: We cannot directly take mkRenaming from Expression as that
    // works with untyped variables.
    def mkRenaming():(Subst, List[TypedVar]) = {
      // Create an ordinary (untyped) renaming substitution
      // TrueLit just because to find the function mkRenaming in Expression
      val rho = TrueLit.mkRenaming(xs map { _.varOf })
      // Create the typed version of xs renamed. The type of course remains the same
      val xsrho = xs map { x => (rho(x._1).asInstanceOf[Var], x._2) }
      (rho, xsrho)
    }

    def restrictTo(vs: Set[Var]) = 
      for (x <- xs;
	   if vs contains x.varOf) yield x

    def restrictToNot(vs: Set[Var]) = 
      for (x <- xs;
	   if !(vs contains x.varOf)) yield x

    // def existsVar(x: Var) = varsOf contains x

    // Find the type of a given variable in xs
    // Can only be applied if x is defined in xs
    def apply(x: Var) = (xs find { _.varOf == x }) match { 
      case Some(vt) => vt.typeOf 
      case None => throw new InternalError("Internal error: variable " + x + " is not defined in " + this)
    }

    // Extend xs with a given list of typed vars
    def ++ (xs: List[TypedVar]) = { 
      var res = xs
      for (x <- xs) { 
	require((! (res.varsOf contains x.varOf)) || res(x.varOf) == x.typeOf, 
		{ println("Error: double declaration of variable " + x + ", have " + xs) })
	res ::= x
      }
      res
    }

    // override def toString = xs.toMyString("[",", ","]")
  }

}
