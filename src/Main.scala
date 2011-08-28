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

object Main {

  import scala.util.matching.Regex
  import Literal._
  import Misc._
  import Term._
  import Predefined._
  import TMEParser._
  import TPTPTParser._
  import Clauses._
  import Inference._
  import Signature._
  import BGContext._
  import Cooper._
  import Formula._
  import ClauseX._
  import State._
  import Flags._
  import Integers._
  import java.lang._
  import java.io._

  val versionString = "0.1.2"

  case class InternalError(s: String) extends Exception

  def usage() {
    println("Usage: melia [flags] filename")
    Flags.usage()
  }

  def main(args: Array[String]) {

    println("This is MELIA, version " + versionString)

    def szsStatus(status: String, file: String) {
      println()
      println("% SZS status " + status + " for " + file)
    }

    def fileNameSplit(inputFileName: String) =
      if (inputFileName endsWith ".p") 
	(inputFileName dropRight 2, ".p")
      else if (inputFileName endsWith ".tme") 
	(inputFileName dropRight 4, ".tme")
      else if (inputFileName endsWith ".tptp") 
	(inputFileName dropRight 5, ".tptp")
      else 
	throw new CmdlineError("Unknown extension in input file name '" + inputFileName + "'. Use -format FORMAT where FORMAT is other than 'auto'.")


    // Determines whether we SZS output "Theorem" or "Unsatisfiable"
    var haveConjecture = false

    try { 
      val fileIndex = Flags.parseFlags(args)
      // parseFlags return the index of the first non-flag parameter
      if (fileIndex >= args.length)
	throw new CmdlineError("Incomplete commandline")
      // See if we have a TPTP file or a tme file
      val inputFileName = args(fileIndex)
      // We need to determine the input format and, depending on that,
      // the parser to use
      val format = 
	if (Flags.formatFlag.value == "auto") {
	  // Try to get the appropriate format from the file name
	  // todo: could use regex parsing here for elegance
	  val (basename, extension) = fileNameSplit(inputFileName)
	  if (extension == ".tme") 
	    // an easy case
	    "tme"
	  else { 
	    // Extension mut be .p or .tptp as per the test above.
	    // Get the format from the basename
	    // val CharInd = new Regex(""".*[A-Z][A-Z][0-9]+(.)[0-9].*""")
	    val CharInd = new Regex(""".*([-+_=]).*""")
	    val f = basename match { 
	      case CharInd("-") => "cnf"
	      case CharInd("+") => "fof"
	      case CharInd("_") => "tff"
	      case CharInd("=") => "tff-int"
	      case _ => 
		throw new CmdlineError("Format of input clauses not obvious from file name. Please use '-format'.")
	    }
	    f
	  }
	} else 
	  Flags.formatFlag.value

      // The global signature needs to be set before parsing,
      // because parsing extends it
      Sigma = signatureEmpty // the "most likely" default

      val clauses = format match {
	case "tme" => 
	  parseTMEFile(inputFileName)
	case "cnf" => {
	  exec(List("tptpFO2tme", inputFileName))
	  val (basename, extension) = fileNameSplit(inputFileName)
	  parseTMEFile(basename + ".tme")
	}
	case "fof" | "tff" | "tff-int" => 	
	  if (Flags.cnfConversion.value == "FLOTTER") {
	    if (format != "fof") 
	      throw new CmdlineError("Flags '-cnf FLOTTER' and '-format" + format + "' are not compatible") 
	    exec(List("tptpFO2tme", inputFileName))
	    val (basename, extension) = fileNameSplit(inputFileName)
	    parseTMEFile(basename + ".tme")
	  } else {
	    // Set the global signature preliminarily already now,
	    // so that arith expressions will be formatted nicely.
	    if (format == "tff-int") Sigma = signatureInt
	    val (fs,h) = parseTPTPTFile(inputFileName)
	    haveConjecture = h
	    // Convert each formula to clausal form, which possibly extends the signature
	    println("Input formulas:")
	    println("===============")
	    fs foreach { println(_) }
	    println()
	    println("With signature:")
	    println("===============")
	    Sigma.show()
	    println()
	    fs flatMap { _.toClauses }
	  }
	case _ => {
	  throw new CmdlineError("Format " + format + " not yet implemented")
	}
      }

      if (verbose) {
	println("Input clause set:")
	println("=================")
	clauses foreach { println(_) }
	println()
	println("With signature:")
	println("===============")
	Sigma.show()
	println()
      }
      
      try { 
	MEETOuter(clauses, Flags.weightBoundFlag.value) 
	if (verbose) {
	  State.show
	}
	(Sigma.BGTypes.isEmpty, haveConjecture) match {
	  case (false, _)    => szsStatus("Unknown", inputFileName)
	  case (true, false) => szsStatus("Satisfiable", inputFileName)
	  case (true, true)  => szsStatus("CounterSatisfiable", inputFileName)
	}
      } catch {
	case REFUTATION() => {
	  if (verbose && !Sigma.BGTypes.isEmpty) {
	    println("Final background context")
	    println("========================")
	    Gamma.show()
	  }
	if (haveConjecture) 
	  szsStatus("Theorem", inputFileName)
	else
	  szsStatus("Unsatisfiable", inputFileName)
	}
      }
    } catch {
      case CmdlineError(s:String) => { 
	println(s)
	usage()
      }
      case s:FileNotFoundException => { 
	println(s)
	usage()
      }
      case SyntaxError(s:String) => 
	println(s)
    }
  }
}
