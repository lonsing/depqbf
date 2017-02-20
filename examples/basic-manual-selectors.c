#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"

int main (int argc, char** argv)
{

  /* Please see also the file 'basic-api-example.c' for more comments. The
  example below is similar to 'basic-api-example.c' but it does not make use
  of the push/pop API functions. Instead, clauses are added to and deleted
  from the formula based on selector variables. The selector variables are
  existentially quantified in the leftmost quantifier block. Each added clause
  gets a selector variable, which is assigned as an assumption before the
  actual solving starts. This way, clauses are enabled and disabled by
  selector variables. We argue that the use of the push/pop API functions is
  less error-prone from the user's perspective. */

  QDPLL *depqbf = qdpll_create ();

  qdpll_configure (depqbf, "--dep-man=simple");
  /* Enable incremental solving. */
  qdpll_configure (depqbf, "--incremental-use");

  /* Add and open a new leftmost existential block at nesting level 1. 
     Selector variables are put into this block. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  /* Add selector variables with IDs 100 and 200. */
  qdpll_add (depqbf, 100);
  qdpll_add (depqbf, 200);
  /* Close open block. */
  qdpll_add (depqbf, 0);

  /* Add and open a new leftmost universal block at nesting level 2. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 2);
  /* Add a variable with ID == 1, which is part of the actual encoding. */
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 0);

    /* Add and open a new existential block at nesting level 3. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 3);
  /* Add a variable with ID == 2, which is part of the actual encoding. */
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  /* Add clause: 100 1 -2 0 with selector variable 100. */
  qdpll_add (depqbf, 100);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);

  /* Add clause: 200 -1 2 0 with selector variable 200. */
  qdpll_add (depqbf, 200);
  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_print (depqbf, stdout);

  /* Enable all clauses: set selector variables to false as assumptions. */
  qdpll_assume (depqbf, -100);
  qdpll_assume (depqbf, -200);

  QDPLLResult res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_SAT);
  /* res == 10 means satisfiable, res == 20 means unsatisfiable. */
  printf ("result is: %d\n", res);

  qdpll_reset (depqbf);

  /* Add new selector variable with ID == 300 to leftmost block. */
  qdpll_add_var_to_scope (depqbf, 300, 1);

  /* Add clause: 300 1 2 0 with selector variable 300. This makes the formula
     unsatisfiable. */
  qdpll_add (depqbf, 300);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_print (depqbf, stdout);

  /* Enable all clauses: set selector variables to false as assumptions. */
  qdpll_assume (depqbf, -100);
  qdpll_assume (depqbf, -200);
  qdpll_assume (depqbf, -300);

  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is: %d\n", res);

  qdpll_reset (depqbf);

  /* Discard the most recently added clause '300 1 2 0' by setting the
     selector variable 300 to true. */
  qdpll_assume (depqbf, -100);
  qdpll_assume (depqbf, -200);
  qdpll_assume (depqbf, 300);

  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_SAT);
  printf ("result after disabling the clause '300 1 2 0' is: %d\n", res);

  qdpll_delete (depqbf);
}
