/*
 This file is part of DepQBF4J.

 DepQBF4J, a tool that enables Java applications to use DepQBF as a library.

 Copyright 2014, 2015 Martin Kronegger and Andreas Pfandler
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

public class Example_basic_clause_groups_api_example {
	
	public static void main(String[] args) {
		Example_basic_clause_groups_api_example ex = new Example_basic_clause_groups_api_example();
		ex.run();
	}
	
	/**
	 * This is the java version of the 'basic-api-example.c' example contained in DepQBF.
	 */
	private void run() {
		/* The header file 'qdpll.h' has some comments regarding the usage of the API. */

		/* Please see also the file 'basic-clause-groups-api-example.c'. */

		/* Create solver instance. */
		DepQBF4J.create();
                
		/* Use the linear ordering of the quantifier prefix. */
		DepQBF4J.configure("--dep-man=simple");
		/* Enable incremental solving. */
		DepQBF4J.configure("--incremental-use");

                /* Given the following unsatisfiable formula:
                   
                   p cnf 4 3
                   a 1 2 0
                   e 3 4 0
                   -1 -3 0
                   1 2 4 0
                   1 -4 0
                   
                   The first clause will be put in one clause group and the last two clauses in
                   another group. That last two clauses are unsatisfiable, thus deleting the
                   first clause preserves unsatisfiability.
                */

                /* Declare outermost universal block with variables 1 and 2. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_FORALL, 1);
		DepQBF4J.add(1);
		DepQBF4J.add(2);
		DepQBF4J.add(0);

                /* Declare existential block with variables 3 and 4. */
		DepQBF4J.newScopeAtNesting(DepQBF4J.QTYPE_EXISTS, 2);
		DepQBF4J.add(3);
		DepQBF4J.add(4);
		DepQBF4J.add(0);

                /* Create a new clause group with ID 'id1'. The ID of a clause group is used
                   as its handle and can be passed to API functions. */
                int id1 = DepQBF4J.newClauseGroup();
                /* Newly created clause groups are closed. */
                assert DepQBF4J.getOpenClauseGroup() == 0;
                /* A clause group must be opened before clauses can be added to it. Only one
                   clause group can be open at a time. */
                DepQBF4J.openClauseGroup(id1);
                assert DepQBF4J.getOpenClauseGroup() == id1;
                /* Add the clause '-1 -3 0' to the currently open clause group 'id1'. */
		DepQBF4J.add(-1);
		DepQBF4J.add(-3);
		DepQBF4J.add(0);
                /* The currently open clause group must be closed before creating or opening
                   another clause group. */
                DepQBF4J.closeClauseGroup(id1);
                assert DepQBF4J.getOpenClauseGroup() == 0;

                /* Create another clause group 'id2'. */
                int id2 = DepQBF4J.newClauseGroup();
                assert DepQBF4J.getOpenClauseGroup() == 0;
                DepQBF4J.openClauseGroup(id2);
                assert DepQBF4J.getOpenClauseGroup() == id2;
                /* Add the clauses '1 2 4 0' and '1 -4 0' to the currently open clause group
                   'id2'. */
		DepQBF4J.add(1);
		DepQBF4J.add(2);
		DepQBF4J.add(4);
		DepQBF4J.add(0);
		DepQBF4J.add(1);
		DepQBF4J.add(-4);
		DepQBF4J.add(0);
                DepQBF4J.closeClauseGroup(id2);
                assert DepQBF4J.getOpenClauseGroup() == 0;

		/* Print formula. */
		DepQBF4J.printToStdOut();

		byte res = DepQBF4J.sat();
		/* Expecting that the formula is unsatisfiable. */
		assert res == DepQBF4J.RESULT_UNSAT;
		/* res == 10 means satisfiable, res == 20 means unsatisfiable. */
		System.out.println("result is: " + res);

                /* Get a list of those clause groups which contain clauses used by solver to
                   determine unsatisfiability. This amounts to an unsatisfiable core of the
                   formula. */
                int[] relevant_clause_groups = DepQBF4J.getRelevantClauseGroups();
                /* We must reset the solver AFTER retrieving the relevant groups. */
                DepQBF4J.reset();
                /* In our example, the clauses in the group 'id2' are relevant for
                   unsatisfiability. (The clause '-1 -3 0' in 'id1' cannot be part of a resolution
                   refutation found by the solver.) */
                assert relevant_clause_groups.length == 1;
                assert relevant_clause_groups[0] == id2;

		System.out.println("relevant clause group: " + relevant_clause_groups[0]);
                /* Temporarily remove the clause group 'id2' by deactivating it. */
                System.out.println("deactivating clause group " + relevant_clause_groups[0]);
                DepQBF4J.deactivateClauseGroup(relevant_clause_groups[0]);

                /* Calling 'gc()' removes superfluous variables and
                   quantifiers from the prefix. HOWEVER, in this case, we have
                   deactivated -- not deleted -- group 'id2' and hence calling
                   'gc()' has no effect. */
                DepQBF4J.gc();
		DepQBF4J.printToStdOut();

                /* The formula where group 'id2' has been deactivated is satisfiable. */
                res = DepQBF4J.sat();		
		assert res == DepQBF4J.RESULT_SAT;
		System.out.println("result is: " + res);
                DepQBF4J.reset();
                /* Activate group 'id2' again, which makes the formula unsatisfiable. */
                System.out.println("activating clause group " + relevant_clause_groups[0]);
                DepQBF4J.activateClauseGroup(relevant_clause_groups[0]);

                /* Permanently remove the group 'id1'. This operation cannot be undone and
                   is in contrast to deactivating a group. */
                System.out.println("deleting clause group " + id1);
                DepQBF4J.deleteClauseGroup(id1);
                /* Deleting a group invalidates its ID, which can be checked by
                   'qdpll_exists_clause_group'. */
                assert !DepQBF4J.existsClauseGroup(id1);

                /* Different from the first call of 'qdpll_gc' above, this time variable 3
                   will be removed from the quantifier prefix. We deleted group 'id1' which
                   contains the only clause where variable 3 occurs. Hence calling 'qdpll_gc'
                   removes variable 3 because it does not occur any more in the formula. */
                DepQBF4J.gc();
                assert !DepQBF4J.isVarDeclared(3);
		DepQBF4J.printToStdOut();

                /* After deleting the group 'id1', the formula consisting only of the
                   clauses in group 'id2' is unsatisfiable. */
                res = DepQBF4J.sat();		
		assert res == DepQBF4J.RESULT_UNSAT;
		System.out.println("result is: " + res);

		/* Delete solver instance. */
		DepQBF4J.delete();
	}
}
