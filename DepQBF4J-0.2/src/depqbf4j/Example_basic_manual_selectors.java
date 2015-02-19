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

public class Example_basic_manual_selectors {
	
	public static void main(String[] args) {
		Example_basic_manual_selectors ex = new Example_basic_manual_selectors();
		ex.run();
	}
	
	/**
	 * This is the java version of the 'basic-manual-selectors.c' example contained in DepQBF.
	 */
	private void run() {
		/* Please see also the file 'basic-api-example.c' for more comments. The
		   example below is similar to 'basic-api-example.c' but it does not make use
		   of the push/pop API functions. Instead, clauses are added to and deleted
		   from the formula based on selector variables. The selector variables are
		   existentially quantified in the leftmost quantifier block. Each added clause
		   gets a selector variable, which is assigned as an assumption before the
		   actual solving starts. This way, clauses are enabled and disabled by
		   selector variables. We argue that the use of the push/pop API functions is
		   less error-prone from the user's perspective. */
		
		DepQBF4J.create();
		DepQBF4J.configure("--dep-man=simple");
		/* Enable incremental solving. */
		DepQBF4J.configure("--incremental-use");
		
		/* Add and open a new leftmost existential block at nesting level 1. 
		   Selector variables are put into this block. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 1);
		/* Add selector variables with IDs 100 and 200. */
		DepQBF4J.add(100);
		DepQBF4J.add(200);
		/* Close open block. */
		DepQBF4J.add(0);
		
		/* Add and open a new leftmost universal block at nesting level 2. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_FORALL, 2);
		/* Add a variable with ID == 1, which is part of the actual encoding. */
		DepQBF4J.add(1);
		DepQBF4J.add(0);
		
		/* Add and open a new existential block at nesting level 3. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 3);
		/* Add a variable with ID == 2, which is part of the actual encoding. */
		DepQBF4J.add(2);
		DepQBF4J.add(0);
		
		/* Add clause: 100 1 -2 0 with selector variable 100. */
		DepQBF4J.add(100);
		DepQBF4J.add(1);
		DepQBF4J.add(-2);
		DepQBF4J.add(0);
		
		/* Add clause: 200 -1 2 0 with selector variable 200. */
		DepQBF4J.add(200);
		DepQBF4J.add(-1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);
		
		DepQBF4J.printToStdOut();
		
		/* Enable all clauses: set selector variables to false as assumptions. */
		DepQBF4J.assume(-100);
		DepQBF4J.assume(-200);
		
		byte res = DepQBF4J.sat();
		assert res == DepQBF4J.RESULT_SAT;
		/* res == 10 means satisfiable, res == 20 means unsatisfiable. */
		System.out.println("result is: " + res);
		
		DepQBF4J.reset();
		
		/* Add new selector variable with ID == 300 to leftmost block. */
		DepQBF4J.addVarToScope(300, 1);
		
		/* Add clause: 300 1 2 0 with selector variable 300. This makes the formula
		   unsatisfiable. */
		DepQBF4J.add(300);
		DepQBF4J.add(1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);
		
		DepQBF4J.printToStdOut();
		
		/* Enable all clauses: set selector variables to false as assumptions. */
		DepQBF4J.assume(-100);
		DepQBF4J.assume(-200);
		DepQBF4J.assume(-300);
		
		res = DepQBF4J.sat();
		assert res == DepQBF4J.RESULT_UNSAT;
		System.out.println("result is: " + res);
		
		DepQBF4J.reset();
		
		/* Discard the most recently added clause '300 1 2 0' by setting the
		   selector variable 300 to true. */
		DepQBF4J.assume(-100);
		DepQBF4J.assume(-200);
		DepQBF4J.assume(300);
		
		DepQBF4J.printToStdOut();
		
		res = DepQBF4J.sat();
		assert res == DepQBF4J.RESULT_SAT;
		System.out.println("result after disabling the clause '300 1 2 0' is: " + res);
		
		DepQBF4J.delete();
	}
}