/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        
 Copyright 2013, 2014, 2015, 2016, 2017 Florian Lonsing,
   Vienna University of Technology, Vienna, Austria.
 Copyright 2010, 2011, 2012 Florian Lonsing,
   Johannes Kepler University, Linz, Austria.
 Copyright 2012 Aina Niemetz,
   Johannes Kepler University, Linz, Austria.

 DepQBF is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 DepQBF is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with DepQBF.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include "qdpll_dynamic_bloqqer.h"
#include "qdpll_internals.h"
#include "qdpll_pcnf.h"
#include "qdpll_config.h"
#include "./bloqqer35/bloqqer.h"

/* Get process time. Can be used for performance statistics. 
   TODO: code also appears in 'qdpll.c', should be put in separate module. */
static double
time_stamp ()
{
  double result = 0;
  struct rusage usage;

  if (!getrusage (RUSAGE_SELF, &usage))
    {
      result += usage.ru_utime.tv_sec + 1e-6 * usage.ru_utime.tv_usec;
      result += usage.ru_stime.tv_sec + 1e-6 * usage.ru_stime.tv_usec;
    }

  return result;
}

static void 
import_prefix_under_current_assignment (QDPLL *qdpll)
{
  Scope *s;
  int exist_block = 1; 
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      /* We go over the list of quantifier blocks (scopes) from left to
         right. */
      if (QDPLL_SCOPE_EXISTS (s))
        {
  	  exist_block = 1; 
        }
      else
        {
          assert (QDPLL_SCOPE_FORALL (s));
	  exist_block = -1; 
        }
      /* Import variables of the current block 's'. */
      VarID *vp, *ve;
      for (vp = s->vars.start, ve = s->vars.top; vp < ve; vp++)
        {
          VarID vid = *vp;
          assert (vid);
          Var *var = VARID2VARPTR (qdpll->pcnf.vars, vid);
          if (!QDPLL_VAR_ASSIGNED (var))
            {
		bloqqer_decl_var (vid*exist_block);
            }
        }
    }
}

/* Returns non-zero if the clause 'c' is satisfied under the current
   assignment in the QBF solver. */
static int
is_clause_satisfied (QDPLL *qdpll, Constraint *c)
{
  assert (!c->is_cube);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
        return 1;
    }
  return 0;
}

static void
import_cnf_under_current_assignment (QDPLL *qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      /* Go over list of original clauses. */
      assert (!c->is_cube);
      assert (!c->learnt);
      /* Ignore clauses which are blocked or satisfied under the current
         assignment in the QBF solver. */
      if (!c->qbcp_qbce_blocked && !is_clause_satisfied (qdpll, c))
        {
          /* Import clause 'c' in Bloqqer. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              /* Ignore literals of variables which are currently
                 assigned. These literals do not satisfy the clause (otherwise we
                 would not have entered this loop). */
              if (!QDPLL_VAR_ASSIGNED (var)) {
                bloqqer_add (lit);  
              } else
                {
                  assert ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)) || 
                          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)));
                }
            }
	    bloqqer_add (0);
        }
    }
}

static void
import_qbf_under_current_assignment (QDPLL *qdpll)
{
  import_prefix_under_current_assignment (qdpll);
  import_cnf_under_current_assignment (qdpll);
}

static BloqqerResult 
run_bloqqer ()
{
  int res = bloqqer_preprocess ();
  if (res == 10) return BLOQQER_RESULT_SAT;
  if (res == 20) return BLOQQER_RESULT_UNSAT;
  return BLOQQER_RESULT_UNKNOWN;
}

static void 
dynamic_bloqqer_reset ()
{
  bloqqer_reset ();
}

/* ---------- START: public functions ---------- */

BloqqerResult 
dynamic_bloqqer_test (QDPLL *qdpll)
{
  /* Return immediately if calls of Bloqqer have been disabled dynamically by
     number of calls and average calling time. */
  if (qdpll->state.dyn_bloqqer_disabled)
    return BLOQQER_RESULT_UNKNOWN;

  /* Disable Bloqqer calls if limit on number of clauses in original CNF exceeded. */
  if (qdpll->options.dyn_bloqqer_disable_cnf_threshold && 
      qdpll->pcnf.clauses.cnt >= qdpll->options.dyn_bloqqer_disable_cnf_threshold)
    {
      assert (!qdpll->state.dyn_bloqqer_disabled);
      qdpll->state.dyn_bloqqer_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling Bloqqer calls: CNF size is %d, %d threshold\n", 
                 qdpll->pcnf.clauses.cnt, qdpll->options.dyn_bloqqer_disable_cnf_threshold);
      return BLOQQER_RESULT_UNKNOWN;
    }

  qdpll->state.dyn_bloqqer_calls++;
  double start_time = time_stamp (); 

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "Running dynamic Bloqqer test.\n");

  dynamic_bloqqer_reset ();
  fflush(stdout);

  bloqqer_init(qdpll_get_max_declared_var_id (qdpll), qdpll->pcnf.clauses.cnt);
  import_qbf_under_current_assignment (qdpll);
  BloqqerResult result = run_bloqqer ();
  qdpll->state.dyn_bloqqer_time += (time_stamp () - start_time); 
#if COMPUTE_STATS
  if (result == BLOQQER_RESULT_SAT)
    {
      qdpll->stats.dyn_bloqqer_result_sat++;
      qdpll->stats.dyn_bloqqer_success_dlevels += qdpll->state.decision_level;
      qdpll->stats.dyn_bloqqer_cur_result_unknown_streak = 0;
    }
  else if (result == BLOQQER_RESULT_UNSAT)
    {
      qdpll->stats.dyn_bloqqer_result_unsat++;
      qdpll->stats.dyn_bloqqer_success_dlevels += qdpll->state.decision_level;
      qdpll->stats.dyn_bloqqer_cur_result_unknown_streak = 0;
    }
  else
    {
      assert (result == BLOQQER_RESULT_UNKNOWN);
      qdpll->stats.dyn_bloqqer_cur_result_unknown_streak++;
      if (qdpll->stats.dyn_bloqqer_cur_result_unknown_streak > 
          qdpll->stats.dyn_bloqqer_max_result_unknown_streak)
        qdpll->stats.dyn_bloqqer_max_result_unknown_streak = 
          qdpll->stats.dyn_bloqqer_cur_result_unknown_streak;
    }
#endif

  if (qdpll->options.dyn_bloqqer_disable_calls_threshold > 0 && 
      qdpll->state.dyn_bloqqer_calls >= qdpll->options.dyn_bloqqer_disable_calls_threshold && 
      (qdpll->state.dyn_bloqqer_time / qdpll->state.dyn_bloqqer_calls) >= 
      qdpll->options.dyn_bloqqer_disable_time_threshold)
    {
      assert (!qdpll->state.dyn_bloqqer_disabled);
      qdpll->state.dyn_bloqqer_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling Bloqqer calls: average time is %f, %d calls\n", 
                 qdpll->state.dyn_bloqqer_time / qdpll->state.dyn_bloqqer_calls, qdpll->state.dyn_bloqqer_calls);
    }

  return result;
}

/* ---------- END: public functions ---------- */
