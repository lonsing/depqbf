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

public class Example_basic_api_example2 {
	
	public static void main(String[] args) {
		Example_basic_api_example2 ex = new Example_basic_api_example2();
		ex.run();
	}
	
	/**
	 * This is the java version of the 'basic-api-example2.c' example contained in DepQBF.
	 */
	private void run() {
		DepQBF4J.create();
		
		DepQBF4J.configure("--dep-man=simple");
		DepQBF4J.configure("--incremental-use");

		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 1);
		DepQBF4J.add(1);
		DepQBF4J.add(0);

		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_FORALL, 2);
		DepQBF4J.add(2);
		DepQBF4J.add(0);

		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 3);
		DepQBF4J.add(3);
		DepQBF4J.add(0);

		DepQBF4J.add(3);
		DepQBF4J.add(0);

		DepQBF4J.push();

		DepQBF4J.add(-1);
		DepQBF4J.add(-2);
		DepQBF4J.add(0);

		DepQBF4J.add(1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);

		DepQBF4J.printToStdOut();

		/* Internally, variable 2 has universal-reduced from the added clauses. See
		   the output of the above 'qdpll_print'. However, the variable is still
		   present in the prefix of the formula. We can check this by calling
		   'qdpll_is_var_declared', passing the respective variable ID. */
		assert DepQBF4J.isVarDeclared(1);
		assert DepQBF4J.isVarDeclared(2);
		assert DepQBF4J.isVarDeclared(3);

		/* For example, we did not declare a variable with ID 99. */
		assert !DepQBF4J.isVarDeclared(99);

		/* Some assertions which demonstrate how to inspect the current prefix. */
		assert DepQBF4J.getScopeType(1) == DepQBF4J.QTYPE_EXISTS;
		assert DepQBF4J.getScopeType(2) == DepQBF4J.QTYPE_FORALL;
		assert DepQBF4J.getScopeType(3) == DepQBF4J.QTYPE_EXISTS;
		assert DepQBF4J.getMaxDeclaredVarId() == 3;
		assert DepQBF4J.getMaxScopeNesting() == 3;
		assert DepQBF4J.getNestingOfVar(1) == 1;
		assert DepQBF4J.getNestingOfVar(2) == 2;
		assert DepQBF4J.getNestingOfVar(3) == 3;

		byte res = DepQBF4J.sat();
		assert res == DepQBF4J.RESULT_UNSAT;
		System.out.println("result is: " + res);

		DepQBF4J.reset();

		DepQBF4J.pop();

		/* The previous 'qdpll_pop' removed the clauses '-1 -2 0' and '-1 -2 0' and
		   the variables 1 and 2 do not occur in clauses any more. However, these
		   variables are still present in the prefix, and the prefix remains
		   unchanged. */
		assert DepQBF4J.isVarDeclared(1);
		assert DepQBF4J.isVarDeclared(2);
		assert DepQBF4J.isVarDeclared(3);
		assert DepQBF4J.getScopeType(1) == DepQBF4J.QTYPE_EXISTS;
		assert DepQBF4J.getScopeType(2) == DepQBF4J.QTYPE_FORALL;
		assert DepQBF4J.getScopeType(3) == DepQBF4J.QTYPE_EXISTS;
		assert DepQBF4J.getMaxDeclaredVarId() == 3;
		assert DepQBF4J.getMaxScopeNesting() == 3;

		if (true) {
			/* IMPORTANT NOTE: we demonstrate the use of 'qdpll_gc' and functions to
			   manipulate the quantifier prefix. The function 'qdpll_gc' cleans up the
			   prefix and removes variables which do not occur in any clauses in the
			   current formula. It also removes empty quantifier blocks. DO NOT call
			   'qdpll_gc' unless you really want to clean up the quantifier prefix! */

			/* If we call 'qdpll_gc' here then the variables 1 and 2 will be removed
			   from the prefix (and also their quantifier blocks because they become
			   empty). Before we add the clauses "1 -2 0" and "-1 2 0" below, we must
			   restore the original prefix.  Otherwise, when adding these clauses the
			   solver will interpret the variables 1 and 2 (which do not occur in the
			   prefix at the time when the clauses are added) as free variables. Free
			   variables by default are put into an existential quantifier block at the
			   left end of the quantifier prefix. */
			DepQBF4J.gc();

			/* Variables 1 and 2 have been deleted by 'qdpll_gc', including their
			   quantifier blocks because these blocks became empty. */
			assert !DepQBF4J.isVarDeclared(1);
			assert !DepQBF4J.isVarDeclared(2);
			/* Variable 3 still occurs in a clause and hence 'qdpll_gc' does not clean
			   it up. */
			assert DepQBF4J.isVarDeclared(3);
			/* The current prefix consists of the existential block containing variable
			   3 only. This block is now at nesting level 1 because the other blocks
			   have been deleted by 'qdpll_gc'. */
			assert DepQBF4J.getMaxScopeNesting() == 1;
			assert DepQBF4J.getNestingOfVar(3) == 1;
			assert DepQBF4J.getMaxDeclaredVarId() == 3;

			/* We have to restore the original prefix and insert variables 1 and 2 and
			   their respective quantifier blocks. */ 
			/* Add new existential block at
			   nesting level 1 and new variable with ID 1 to this block. */
			DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 1);
			DepQBF4J.add(1);
			DepQBF4J.add(0);
			assert DepQBF4J.isVarDeclared(1);

			assert DepQBF4J.getNestingOfVar(1) == 1;
			/* The block of variable 3 now appears at nesting level 2 because we added a
			   new existential block at nesting level 1.*/
			assert DepQBF4J.getNestingOfVar(3) == 2;

			/* Add new universal block at nesting level 2 and new variable with ID 2 to
			   this block. */
			DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_FORALL, 2);
			DepQBF4J.add(2);
			DepQBF4J.add(0);
			assert DepQBF4J.isVarDeclared(2);

			assert DepQBF4J.getNestingOfVar(1) == 1;
			assert DepQBF4J.getNestingOfVar(2) == 2;
			/* The block of variable 3 now appears at nesting level 3 because we added a
			   new existential and universal block at nesting levels 1 and 2.*/
			assert DepQBF4J.getNestingOfVar(3) == 3;
			assert DepQBF4J.getScopeType(1) == DepQBF4J.QTYPE_EXISTS;
			assert DepQBF4J.getScopeType(2) == DepQBF4J.QTYPE_FORALL;
			assert DepQBF4J.getScopeType(3) == DepQBF4J.QTYPE_EXISTS;

			/* Now the original prefix is restored and we can proceed with adding
			   further clauses containing variables 1 and 2. */
		}

		DepQBF4J.add(1);
		DepQBF4J.add(-2);
		DepQBF4J.add(0);

		DepQBF4J.add(-1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);

		DepQBF4J.printToStdOut();

		res = DepQBF4J.sat();
		assert res == DepQBF4J.RESULT_UNSAT;
		System.out.println("result is: " + res);

		DepQBF4J.delete();
	}
}
