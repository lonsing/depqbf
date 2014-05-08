/*
 This file is part of DepQBF4J.

 DepQBF4J, a tool that enables Java applications to use DepQBF as a library.

 Copyright 2014 Martin Kronegger and Andreas Pfandler
 Vienna University of Technology, Vienna, Austria.

 DepQBF4J is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 DepQBF4J is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with DepQBF4J. If not, see <http://www.gnu.org/licenses/>.
*/

package depqbf4j;

public class DepQBF4J {
	public static byte QTYPE_EXISTS = -1;
	public static byte QTYPE_UNDEF = 0;
	public static byte QTYPE_FORALL = 1;

	public static byte RESULT_UNKNOWN = 0;
	public static byte RESULT_SAT = 10;
	public static byte RESULT_UNSAT = 20;

	public static byte ASSIGNMENT_FALSE = -1;
	public static byte ASSIGNMENT_UNDEF = 0;
	public static byte ASSIGNMENT_TRUE = 1;

	static {
		System.loadLibrary("depqbf4j");
	}

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void create();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void delete();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native String configure(String config);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void adjustVars(int num);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int getMaxScopeNesting();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int pop();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void gc();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int push();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int newScope(byte quantifierType);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int newScopeAtNesting(byte quantifierType, int nesting);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void addVarToScope(int varId, int nesting);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int hasVarActiveOccs(int varId);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void add(int litId);

	/**
	 * See qdpll.h from DepQBF for details.
	 * 
	 * @return one of the following values: <br>
	 * {@link DepQBF4J#RESULT_SAT}, <br>
	 * {@link DepQBF4J#RESULT_UNSAT}, <br>
	 * {@link DepQBF4J#RESULT_UNKNOWN}
	 */
	public static native byte sat();

	/**
	 * See qdpll.h from DepQBF for details.
	 * 
	 * @return one of the following values: <br>
	 * {@link DepQBF4J#ASSIGNMENT_TRUE}, <br>
	 * {@link DepQBF4J#ASSIGNMENT_FALSE}, <br>
	 * {@link DepQBF4J#ASSIGNMENT_UNDEF}
	 */
	public static native byte getValue(int varId);

	/**
	 * Print QBF to stdout using QDIMACS format.
	 */
	public static native void printToStdOut();

	/**
	 * Print QBF to the file 'filename' using QDIMACS format.
	 * @param filename 
	 */
	public static native void printToFile(String filename);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void printQdimacsOutput();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void initDeps();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void resetDeps();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int varDepends(int varId1, int varId2);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void printDeps(int varId);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int getMaxDeclaredVarId();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int isVarDeclared(int varId);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int getNestingOfVar(int varId);

	/**
	 * See qdpll.h from DepQBF for details.
	 * 
	 * @return one of the following values: <br>
	 * {@link DepQBF4J#QTYPE_EXISTS}, <br>
	 * {@link DepQBF4J#QTYPE_FORALL}, <br>
	 * {@link DepQBF4J#QTYPE_UNDEF}
	 */
	public static native byte getScopeType(int nesting);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void dumpDepGraph();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void printStats();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void reset();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void resetStats();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void resetLearnedConstraints();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native void assume(int litId);

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int[] getAssumptionCandidates();

	/**
	 * See qdpll.h from DepQBF for details.
	 */
	public static native int[] getRelevantAssumptions();
}