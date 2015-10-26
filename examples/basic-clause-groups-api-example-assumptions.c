#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"

static void
print_relevant_assumptions (LitID *assumptions)
{
  LitID *p;
  for (p = assumptions; *p; p++)
    printf ("%d ", *p);
  printf ("0");
}

static unsigned int
count_relevant_assumptions (LitID *assumptions)
{
  unsigned int cnt = 0;
  LitID *p;
  for (p = assumptions; *p; p++)
    cnt++;
  return cnt;
}

int main (int argc, char** argv)
{
  QDPLL *depqbf = qdpll_create ();

  qdpll_configure (depqbf, "--dep-man=simple");
  qdpll_configure (depqbf, "--incremental-use");

/* This example is similar to 'basic-clause-groups-api-example.c'. However,
   instead of using DepQBF's clause group API, we emulate clause groups by
   augmenting the clauses of the formula with fresh selector variables.

   The use of selector variables is common in incremental SAT and QBF solving.

   ***********************************************************************
   PLEASE NOTE: the purpose of this example is to demonstrate the difference
   between incremental solving by selector variables and the clause group and
   push/pop APIs of DepQBF. 
   For incremental solving by DepQBF, it is RECOMMENDED to ALWAYS use either
   the clause group API or the push/pop API. The clause group API is general
   enough to implement any tasks which can be implemented by selector
   variables but its use is more comfortable.
   ***********************************************************************

   Given the following unsatisfiable formula (same as in
   'basic-clause-groups-api-example.c'):

     p cnf 4 3
     a 1 2 0
     e 3 4 0
     -1 -3 0
     1 2 4 0
     1 -4 0
     
   To effectively put the variables into groups, we add the variable '5' to
   the first clause and the variable '6' to the last two clauses. The fresh
   selector variables 5 and 6 are existentially quantified at the left end
   of the quantifier prefix.

   Formula with selector variables looks as follows:

    p cnf 6 3
    e 5 6 0
    a 1 2 0
    e 3 4 0
    5 -1 -3 0
    6 1 2 4 0
    6 1 -4 0
 */

  /* Add existential quantifier block with selector variables 5 and 6. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  qdpll_add (depqbf, 5);
  qdpll_add (depqbf, 6);
  qdpll_add (depqbf, 0);

  /* Add quantifier blocks and variables of the original formula. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 2);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 3);
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);

  /* Add first clause augmented with selector variable 5. */
  qdpll_add (depqbf, 5);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -3);
  qdpll_add (depqbf, 0);

  /* Add second and third clause augmented with selector variable 6. */
  qdpll_add (depqbf, 6);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);  
  qdpll_add (depqbf, 4);
  qdpll_add (depqbf, 0);
  //---------------------
  qdpll_add (depqbf, 6);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -4);  
  qdpll_add (depqbf, 0);

  /* By adding the selector variables to the clauses, we have effectively
     separated the clauses into two separate groups. 
     In the following, we must assign the selector variables MANUALLY as
     assumptions through the solver API to enable/disable the desired
     groups. This must be done before solving the formula by calling
     'qdpll_sat'. */
  qdpll_print (depqbf, stdout);

  /* Enable both groups by setting both selector variables to false. */
  qdpll_assume (depqbf, -5);  
  qdpll_assume (depqbf, -6);

  /* Formula is expected to be unsatisfiable. */
  QDPLLResult res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is %d\n", res);
  /* Get a list of those selector variables which appear in clauses used by
     the solver to determine unsatisfiability. */
  LitID *relevant_assumptions = 
    qdpll_get_relevant_assumptions (depqbf);
  qdpll_reset (depqbf);
  assert (count_relevant_assumptions (relevant_assumptions) == 1);
  printf ("printing zero-terminated relevant assumptions: ");
  print_relevant_assumptions (relevant_assumptions);
  printf ("\n");
  /* Caller must free memory of array returned by
     'qdpll_get_relevant_assumptions'. */
  free (relevant_assumptions);

  /* Deactivate the group which contains the last two clauses by setting the
     selector variable to true. This way, these clauses will be permanently
     satisfied in the fortcoming solver run after calling 'qdpll_sat' and
     hence are effectively removed from the formula. Note that selector
     variable 5 has to be set to false again to enable the first clause. */
  printf ("deactivating group 2 with clauses 1 2 4 0 and 1 -4 0 by assumption 6\n");

  qdpll_assume (depqbf, -5);  
  qdpll_assume (depqbf, 6);

  qdpll_print (depqbf, stdout);

  /* The formula where the last two clauses are disabled is expected to be
     satisfiable. */
  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_SAT);
  printf ("result is %d\n", res);
  qdpll_reset (depqbf);

  /* By setting the selector variables 5 to true and 6 to false, respectively,
     we deactivate the first clause and activate the last two, which results in
     an unsatisfiable formula. */
  printf ("deactivating group 1 with clause -1 -3 0\n");

  qdpll_assume (depqbf, 5);  
  qdpll_assume (depqbf, -6);

  qdpll_print (depqbf, stdout);

  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is %d\n", res);

  qdpll_delete (depqbf);
}
