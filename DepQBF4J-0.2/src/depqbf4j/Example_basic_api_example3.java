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

public class Example_basic_api_example3 {
	
	public static void main(String[] args) {
		Example_basic_api_example3 ex = new Example_basic_api_example3();
		ex.run();
	}
	
	/**
	 * This is the java version of the 'basic-api-example3.c' example contained in DepQBF.
	 */
	private void run() {
		/* The header file 'qdpll.h' has some comments regarding the usage of the
	       API. */
		
		/* Please see also the file 'basic-manual-selectors.c'. */
		
		/* Create solver instance. */
		DepQBF4J.create();
		
		/* Use the linear ordering of the quantifier prefix. */
		DepQBF4J.configure("--dep-man=simple");
		/* Enable incremental solving. */
		DepQBF4J.configure("--incremental-use");
		
		/* Add and open a new leftmost universal block at nesting level 1. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_FORALL, 1);
		
		/* Add a fresh variable with 'id == 1' to the open block. */
		DepQBF4J.add(1);
		DepQBF4J.add(99);
		/* Close open scope. */
		DepQBF4J.add(0);
		
		assert DepQBF4J.isVarDeclared(1);
		assert DepQBF4J.isVarDeclared(99);
		assert !DepQBF4J.isVarDeclared(50);
		assert !DepQBF4J.isVarDeclared(51);
		assert !DepQBF4J.isVarDeclared(52);
		
		/* Add a new existential block at nesting level 2. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 2);
		/* Add a fresh variable with 'id == 2' to the existential block. */
		DepQBF4J.add(2);
		/* Close open scope. */
		DepQBF4J.add(0);
		
		/* Add clause: 1 -2 0 */
		DepQBF4J.add(1);
		DepQBF4J.add(-2);
		DepQBF4J.add(0);
		
		/* Add clause: -1 2 0 */
		DepQBF4J.add(-1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);
		
		/* At this point, the formula looks as follows:
		   p cnf 2 3 
		   a 1 0
		   e 2 0
		   1 -2 0
		   -1 2 0 */
		
		/* Print formula. */
		DepQBF4J.printToStdOut();
		
		byte res = DepQBF4J.sat();
		/* Expecting that the formula is satisfiable. */
		assert res == DepQBF4J.RESULT_SAT;
		/* res == 10 means satisfiable, res == 20 means unsatisfiable. */
		System.out.println("result is: " + res);
		
		/* Must reset the solver before adding further clauses or variables. */
		DepQBF4J.reset();
		
		/* Var 99 still is declared although no clauses were added containing literals of 99 before. */
		assert DepQBF4J.isVarDeclared(1);
		assert DepQBF4J.isVarDeclared(99);
		assert !DepQBF4J.isVarDeclared(50);
		assert !DepQBF4J.isVarDeclared(51);
		assert !DepQBF4J.isVarDeclared(52);
		
		/* Open a new frame of clauses. Clauses added after the 'push' can be
		   removed later by calling 'pop'. */
		DepQBF4J.push();
		
		/* Add clause: 1 2 0 */
		DepQBF4J.add(1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);
		
		System.out.println("added clause '1 2 0' to a new stack frame.");
		
		/* At this point, the formula looks as follows:
		   p cnf 2 3 
		   a 1 0
		   e 2 0
		   1 -2 0
		   -1 2 0 
		   1 2 0 */
		
		DepQBF4J.printToStdOut();
		
		res = DepQBF4J.sat();
		/* Expecting that the formula is unsatisfiable due to the most recently
		   added clause. */
		assert res == DepQBF4J.RESULT_UNSAT;
		System.out.println("result is: " + res);
		
		/* Print partial countermodel as a value of the leftmost universal variable. */
		
		byte a = DepQBF4J.getValue(1);
		System.out.println("partial countermodel - value of 1: " + (a == DepQBF4J.ASSIGNMENT_UNDEF ? "undef" : 
	          (a == DepQBF4J.ASSIGNMENT_FALSE ? "false" : "true")));
		
		DepQBF4J.reset();
		
		/* Discard the clause '1 2 0' by popping off the topmost frame. */
		DepQBF4J.pop();
		
		System.out.println("discarding clause '1 2 0' by a 'pop'.");
		
		/* At this point, the formula looks as follows:
		   p cnf 2 3 
		   a 1 0
		   e 2 0
		   1 -2 0
		   -1 2 0 */
		
		res = DepQBF4J.sat();
		/* The formula is satisfiable again because we discarded the clause '1 2 0'
		   by a 'pop'. */
		assert res == DepQBF4J.RESULT_SAT;
		System.out.println("result after pop is: " + res);
		
		/* Delete solver instance. */
		DepQBF4J.delete();
	}
}
