#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "../qdpll.h"

int main (int argc, char** argv)
{
  QDPLL *depqbf = qdpll_create ();

  qdpll_configure (depqbf, "--dep-man=simple");
  qdpll_configure (depqbf, "--incremental-use");

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 0);

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 2);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 3);
  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 0);

  qdpll_add (depqbf, 3);
  qdpll_add (depqbf, 0);

  qdpll_push (depqbf);

  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);

  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_print (depqbf, stdout);

  /* Internally, variable 2 has universal-reduced from the added clauses. See
     the output of the above 'qdpll_print'. However, the variable is still
     present in the prefix of the formula. We can check this by calling
     'qdpll_is_var_declared', passing the respective variable ID. */
  assert (qdpll_is_var_declared (depqbf, 1));
  assert (qdpll_is_var_declared (depqbf, 2));
  assert (qdpll_is_var_declared (depqbf, 3));
  /* For example, we did not declare a variable with ID 99. */
  assert (!qdpll_is_var_declared (depqbf, 99));
  /* Some assertions which demonstrate how to inspect the current prefix. */
  assert (qdpll_get_scope_type (depqbf, 1) == QDPLL_QTYPE_EXISTS);
  assert (qdpll_get_scope_type (depqbf, 2) == QDPLL_QTYPE_FORALL);
  assert (qdpll_get_scope_type (depqbf, 3) == QDPLL_QTYPE_EXISTS);
  assert (qdpll_get_max_declared_var_id (depqbf) == 3);
  assert (qdpll_get_max_scope_nesting (depqbf) == 3);
  assert (qdpll_get_nesting_of_var (depqbf, 1) == 1);
  assert (qdpll_get_nesting_of_var (depqbf, 2) == 2);
  assert (qdpll_get_nesting_of_var (depqbf, 3) == 3);

  QDPLLResult res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is: %d\n", res);

  qdpll_reset (depqbf);

  qdpll_pop (depqbf);

  /* The previous 'qdpll_pop' removed the clauses '-1 -2 0' and '-1 -2 0' and
     the variables 1 and 2 do not occur in clauses any more. However, these
     variables are still present in the prefix, and the prefix remains
     unchanged. */
  assert (qdpll_is_var_declared (depqbf, 1));
  assert (qdpll_is_var_declared (depqbf, 2));
  assert (qdpll_is_var_declared (depqbf, 3));
  assert (qdpll_get_scope_type (depqbf, 1) == QDPLL_QTYPE_EXISTS);
  assert (qdpll_get_scope_type (depqbf, 2) == QDPLL_QTYPE_FORALL);
  assert (qdpll_get_scope_type (depqbf, 3) == QDPLL_QTYPE_EXISTS);
  assert (qdpll_get_max_declared_var_id (depqbf) == 3);
  assert (qdpll_get_max_scope_nesting (depqbf) == 3);

#if 1
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
  qdpll_gc(depqbf);

  /* Variables 1 and 2 have been deleted by 'qdpll_gc', including their
     quantifier blocks because these blocks became empty. */
  assert (!qdpll_is_var_declared (depqbf, 1));
  assert (!qdpll_is_var_declared (depqbf, 2));
  /* Variable 3 still occurs in a clause and hence 'qdpll_gc' does not clean
     it up. */
  assert (qdpll_is_var_declared (depqbf, 3));
  /* The current prefix consists of the existential block containing variable
     3 only. This block is now at nesting level 1 because the other blocks
     have been deleted by 'qdpll_gc'. */
  assert (qdpll_get_max_scope_nesting (depqbf) == 1);
  assert (qdpll_get_nesting_of_var (depqbf, 3) == 1);
  assert (qdpll_get_max_declared_var_id (depqbf) == 3);

  /* We have to restore the original prefix and insert variables 1 and 2 and
     their respective quantifier blocks. */ 
  /* Add new existential block at
     nesting level 1 and new variable with ID 1 to this block. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_EXISTS, 1);
  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, 0);
  assert (qdpll_is_var_declared (depqbf, 1));

  assert (qdpll_get_nesting_of_var (depqbf, 1) == 1);
  /* The block of variable 3 now appears at nesting level 2 because we added a
     new existential block at nesting level 1.*/
  assert (qdpll_get_nesting_of_var (depqbf, 3) == 2);

  /* Add new universal block at nesting level 2 and new variable with ID 2 to
     this block. */
  qdpll_new_scope_at_nesting (depqbf, QDPLL_QTYPE_FORALL, 2);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);
  assert (qdpll_is_var_declared (depqbf, 2));

  assert (qdpll_get_nesting_of_var (depqbf, 1) == 1);
  assert (qdpll_get_nesting_of_var (depqbf, 2) == 2);
  /* The block of variable 3 now appears at nesting level 3 because we added a
     new existential and universal block at nesting levels 1 and 2.*/
  assert (qdpll_get_nesting_of_var (depqbf, 3) == 3);
  assert (qdpll_get_scope_type (depqbf, 1) == QDPLL_QTYPE_EXISTS);
  assert (qdpll_get_scope_type (depqbf, 2) == QDPLL_QTYPE_FORALL);
  assert (qdpll_get_scope_type (depqbf, 3) == QDPLL_QTYPE_EXISTS);

  /* Now the original prefix is restored and we can proceed with adding
     further clauses containing variables 1 and 2. */
#endif

  qdpll_add (depqbf, 1);
  qdpll_add (depqbf, -2);
  qdpll_add (depqbf, 0);

  qdpll_add (depqbf, -1);
  qdpll_add (depqbf, 2);
  qdpll_add (depqbf, 0);

  qdpll_print (depqbf, stdout);

  res = qdpll_sat (depqbf);
  assert (res == QDPLL_RESULT_UNSAT);
  printf ("result is: %d\n", res);

  qdpll_delete (depqbf);
}
