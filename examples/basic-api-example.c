#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"

int main (int argc, char** argv)
{
  /* The header file 'qdpll.h' has some comments regarding the usage of the
     API. */

  /* Please see also the file 'basic-manual-selectors.c'. */

  /* Create solver instance. */
  QDPLL *depqbf = qdpll_create ();

  /* Use the linear ordering of the quantifier prefix. */
  qdpll_configure (depqbf, "--dep-man=simple");
  /* Enable incremental solving. */
  qdpll_configure (depqbf, "--incremental-use");

  /* Add and open a new leftmost universal block at nesting level 1. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 1);

  /* Add a fresh variable with 'id == 1' to the open block. */
  qdpll_add (depqbf, 1);
  /* Close open scope. */
  qdpll_add (depqbf, 0);

  /* Add a new existential block at nesting level 2. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 2);
  /* Add a fresh variable with 'id == 2' to the existential block. */
  qdpll_add (depqbf, 2);
  /* Close open scope. */
  qdpll_add (depqbf, 0);

  /* Add clause: 1 -2 0 */
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);

  /* Add clause: -1 2 0 */
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  /* At this point, the formula looks as follows:
     p cnf 2 3 
     a 1 0
     e 2 0
     1 -2 0
     -1 2 0 */

  /* Print formula. */
  qdpll_print (depqbf, stdout);

  QDPLLResult res = qdpll_sat (depqbf);
  /* Expecting that the formula is satisfiable. */
  assert (res == QDPLL_RESULT_SAT);
  /* res == 10 means satisfiable, res == 20 means unsatisfiable. */
  printf ("result is: %d\n", res);

  /* Must reset the solver before adding further clauses or variables. */
  qdpll_reset (depqbf);

  /* Open a new frame of clauses. Clauses added after the 'push' can be
     removed later by calling 'pop'. */
  qdpll_push (depqbf);

  /* Add clause: 1 2 0 */
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  printf ("added clause '1 2 0' to a new stack frame.\n");

  /* At this point, the formula looks as follows:
     p cnf 2 3 
     a 1 0
     e 2 0
     1 -2 0
     -1 2 0 
     1 2 0 */

  qdpll_print (depqbf, stdout);

  res = qdpll_sat (depqbf);
  /* Expecting that the formula is unsatisfiable due to the most recently
     added clause. */
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is: %d\n", res);

  /* Print partial countermodel as a value of the leftmost universal variable. */

  QDPLLAssignment a = qdpll_get_value (depqbf, 1);
  printf ("partial countermodel - value of 1: %s\n", a == QDPLL_ASSIGNMENT_UNDEF ? "undef" : 
          (a == QDPLL_ASSIGNMENT_FALSE ? "false" : "true"));

  qdpll_reset (depqbf);

  /* Discard the clause '1 2 0' by popping off the topmost frame. */
  qdpll_pop (depqbf);

  printf ("discarding clause '1 2 0' by a 'pop'.\n");


  /* At this point, the formula looks as follows:
     p cnf 2 3 
     a 1 0
     e 2 0
     1 -2 0
     -1 2 0 */
  qdpll_print (depqbf, stdout);

  res = qdpll_sat (depqbf);
  /* The formula is satisfiable again because we discarded the clause '1 2 0'
     by a 'pop'. */
  assert (res == QDPLL_RESULT_SAT);
  printf ("result after pop is: %d\n", res);

  /* Delete solver instance. */
  qdpll_delete (depqbf);
}
