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


/**
 * Stuff that is not very specific to anything
 */

object Misc {

  import java.io.{FileOutputStream, InputStream, OutputStream, InputStreamReader}
  import java.io.{BufferedReader, BufferedWriter, File, FileReader, FileWriter}

  import Term._
  import Expression._
  import Literal._
  import Formula._
  // import collection.mutable.{Set => MSet}


  /**
   * Implicit conversion of e.g. lists of expressions to an ExpressionSeq allows us
   * to write operations on expressions more naturally, as method application
   */
  class MyExpressionSeq[T] (es: Seq[Expression[T]]) {
    val vars = es.foldLeft(Set[Var]())(_ union _.vars)
    val rvars = es.foldLeft(Set[RVar]())(_ union _.rvars)
    val params = es.foldLeft(Set[Param]())(_ union _.params)
    val freeBGConsts = es.foldLeft(Set[FreeBGConst]())(_ union _.freeBGConsts)
  }
  implicit def toMyExpressionSeq[T](es: Seq[Expression[T]]) = new MyExpressionSeq(es)

  class MyCLitSeq (clits: Seq[CLit]) {
    def produces(L: Lit) = clits exists { _.produces(L,clits) }
  }
  implicit def toMyCLitSeq(clits: Seq[CLit]) = new MyCLitSeq(clits)



  class MySet[T] (s: Set[T]) {
    // set intersection emptyness test - not directly in the scala API it seems:
    def intersects(s1:Set[T]) = s exists { s1.contains(_) }
  }
  implicit def toMySet[T](s: Set[T]) = new MySet(s)

  class MyList[T] (l: List[T]) {

    def deleteDuplicates = 
      for (xs <- l.tails;
	   if !xs.isEmpty;
	   x = xs.head;
	   if !(xs.tail contains x)) yield x


    def removeNth(n:Int) = {
      def hRemoveNth(l: List[T], n:Int):List[T] = {
	// could do a better non-tail recursive version
	if (n == 0)
	  l.tail
	else
	  l.head :: hRemoveNth(l.tail, n-1)
      }
      hRemoveNth(l, n)
    }

    def replaceNth(n:Int, x:T) = {
      def hReplaceNth(l: List[T], n:Int, x:T):List[T] = {
	// could do a better non-tail recursive version
	if (n == 0)
	  x :: l.tail
	else
	  l.head :: hReplaceNth(l.tail, n-1, x)
      }
      hReplaceNth(l, n, x)
    }

    def toMyString(ifEmpty:String, lsep:String, isep: String, rsep:String):String =
      if (l.isEmpty)
	ifEmpty
      else
	lsep + l.map(_.toString).reduceLeft(_ + isep + _) + rsep

    // Convenience function:
    def toMyString(lsep:String, isep: String, rsep:String):String =
      toMyString(lsep + rsep, lsep, isep, rsep)
  }
  implicit def toMyList[T](l: List[T]) = new MyList(l)


  class MyFormulaSeq(fs: Seq[Formula]) {

    def to(neutral: Formula, op: BinOp) = 
      // (Don't use foldLeft - it would give formulas that always include neutral)
      if (fs.isEmpty)
	neutral
    else if (fs.tail.isEmpty)
      fs.head
    else
      fs reduceRight { BinOpForm(op,_,_) }
  }

  implicit def toMyFormulaSeq(fs: Seq[Formula]) = new MyFormulaSeq(fs)


  def printlnDebug(s: String) {
    if (Flags.debug.valueBoolean)
      println("[debug] " + s)
  }

  def printlnDebug() {
    if (Flags.debug.valueBoolean) println()
  }

  def verbose = Flags.verboseFlag.valueBoolean

  def printlnVerbose(s: String) {
    if (verbose) println(s)
  }

  def printlnVerbose() {
    if (verbose) println()
  }

  class Counter {
    var ctr = 0;
    def next() = { 
      ctr += 1; 
      ctr
    }
  }


  // Execute a unix command

  def exec(args: Seq[String], env: Seq[String]) {
    val proc =
      if (env == null || env.size == 0) Runtime.getRuntime.exec(args.toArray)
      else Runtime.getRuntime.exec(args.toArray, env.toArray)
    val is = new BufferedReader(new InputStreamReader(proc.getInputStream))
    val es = new BufferedReader(new InputStreamReader(proc.getErrorStream))
    var line = is.readLine()
    while (line != null) {
      println(line)
      line = is.readLine()
    }
    // Do both streams in one loop for long-lived processes.
    line = es.readLine(); 
    while (line != null) {
      System.err.println(line)
      line = es.readLine()
    }
    proc.waitFor
  }

  def exec(args: Seq[String]) { exec(args, null) }


  def gcd(a: Int, b: Int) = gcd1(a max b, a min b)
  def gcd1(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)
  def lcm(a: Int, b: Int) = a * (b / gcd(a, b))


  case class SyntaxError(s: String) extends Exception

}
