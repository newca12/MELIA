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

object Flags {

  import Misc._

  case class CmdlineError(s:String) extends Exception {}

  /**
   * Each Flag fits the following class, which makes it easy to write
   * code for parsing and printing usage information once and for all.
   */

  abstract class Flag[T] {
    val option: String
    val default: T
    var value: T
    def setValue(v: String):Unit 
    def toString1: String
    def toString2: String
    // def valueInt = value.toInt // use with caution
    // def valueBoolean = value != "off" // use with caution
  }

  // Currently there are only two Flags, for multiple choice and Int values
  case class ChoiceFlag(option: String, 
			values: List[String], 
			doc: String) extends Flag[String] {
    val default = values.head
    var value = default
    def setValue(v: String) {
      if (values contains v)
	value = v
	else
	  throw new CmdlineError("Bad value for flag " + option + ": " + v)    
    }
    def toString1 = option + " " +  values.toMyString("[", "|", "]")
    def toString2 = doc + ", default: " + default
    def valueBoolean = value != "off" // use with caution
  }

  case class IntFlag(option: String, 
		     doc: String, 
		     default: Int) extends Flag[Int] {
    var value = default
    def setValue(v: String) {
      value = v.toInt
    }
    
    def toString1 = option + " " + "Integer"
    def toString2 = doc + ", default: " + default
  }

  // Whether negative literals in clauses are selected.
  // If yes, the selected negative literal is the sole literal in the clause
  // that is subject to an inference, SupNeg or Ref (Ref does not apply to
  // non-equational literals, but SupNeg does).
  // If no, every literal in the clause is subject to a SupNeg or SupPos inference
  // from an equational literal (SupPos inferences from non-equational literals
  // would result in tautologies, and SupNeg inferences from non-equational literals
  // are supplanted by CUIs using these (positive) context literals instead.)
  // Instead of Ref the context literal X=X is used. 
  // The benefit is that the CUIs are obtained by simultaneous mgus *only after
  // all SupNeg inferences have been carried out*. Thus, permutations of 
  // Sup-Neg and Ref inferences are avoided. With Selection, however, chances
  // are better to derive positive clauses with isolated literals.

  val selectionFunction = ChoiceFlag("-sel", 
				     List("auto", "all", "one", "off"),
				     "selection of negative clause literals")

  // Whether to turn positive universal context literals into unit clauses.
  // This way, they can be used to simplify clauses (demodulation, subsumption).
  // Corresponds to the Unit-Clause rule.
  val unitClause = ChoiceFlag("-uci", 
			      List("pos-eq", "pos", "neg", "all", "off"),
			      "Unit-Clauses inference rule")

  val simplifyingUnitResolution = ChoiceFlag("-sur", 
			      List("on", "off"),
			      "simplifying unit resolution")

  // Whether negative literals in context unifiers instances are asserted.
  val negAssert = ChoiceFlag("-nac", 
			     List("non-eq", "all", "eq", "off"),
			     "assert negative literals derived from clauses")

  val paramsOpSet = ChoiceFlag("-params", 
			     List("BG", "FG"),
			     "whether (integer) parameters are background or foreground operators")

  val verboseFlag = ChoiceFlag("-v", 
			   List("on", "off"),
			   "verbose")

  val symmetryElimFlag = ChoiceFlag("-sym", 
			   List("off", "on"),
			   "symmetry elimination for rigid variables by linearly ordering them")

  val weightBoundFlag = IntFlag("-wb", 
			   "initial weight bound", 2)

  val formatFlag = ChoiceFlag("-format", 
			   List("auto", "tff-int", "tme", "cnf", "fof", "tff"),
			   "format of input formulas")

  val cnfConversion = ChoiceFlag("-cnf", 
			   List("optimized", "standard", "FLOTTER"),
			   "flags for built-in CNF conversion")

  val debug = ChoiceFlag("-d", 
			 List("off", "on"),
			 "debug")

  val flags = 
    List(selectionFunction, unitClause, negAssert, paramsOpSet, simplifyingUnitResolution, 
	 weightBoundFlag, symmetryElimFlag, formatFlag, cnfConversion, verboseFlag, debug)

  def usage() {
    println("flags:")
    for (flag <- flags) {
      println("  " + flag.toString1)
      println("  " + flag.toString2)
      println()
    }
  }

  // Returns the index past parsing the flags in args
  def parseFlags(args: Array[String]) = {
    var i=0
    var done = false
    while (i < args.length && !done) {
      (flags find { _.option == args(i) }) match {
	case None => 
	  if (args(i)(0) == '-') throw new CmdlineError("Unknown flag: " + args(i)) 
	  else done = true
	case Some(flag) => { i += 1; flag.setValue(args(i)); i +=1 }
      }
    }
    i
  }
}
