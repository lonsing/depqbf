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
#include "qdpll_dynamic_nenofex.h"
#include "qdpll_internals.h"
#include "qdpll_pcnf.h"
#include "qdpll_config.h"
#include "./nenofex/nenofex.h"

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

/* Returns nonzero iff scope 's' contains only assigned variables. */
static int 
is_scope_effectively_empty (QDPLL *qdpll, Scope *s)
{
  VarID *vp, *ve;
  for (vp = s->vars.start, ve = s->vars.top; vp < ve; vp++)
    {
      VarID vid = *vp;
      assert (vid);
      Var *var = VARID2VARPTR (qdpll->pcnf.vars, vid);
      if (!QDPLL_VAR_ASSIGNED (var))
        return 0;
    }
  return 1;
}

/* Collect unassigned variables in scope 's' on stack. */
static void 
import_prefix_collect_vars (QDPLL *qdpll, Scope *s, VoidPtrStack *stack)
{
  assert (stack);
  VarID *vp, *ve;
  for (vp = s->vars.start, ve = s->vars.top; vp < ve; vp++)
    {
      VarID vid = *vp;
      assert (vid);
      Var *var = VARID2VARPTR (qdpll->pcnf.vars, vid);
      if (!QDPLL_VAR_ASSIGNED (var))
        QDPLL_PUSH_STACK (qdpll->mm, *stack, (void *) ((long unsigned int) vid));
    }
}

static void 
import_prefix_under_current_assignment (QDPLL *qdpll)
{
  VoidPtrStack svars;
  QDPLL_INIT_STACK (svars);
  Scope *prev_nonempty, *cur_nonempty;
  /* Initialize scope pointers to first non-empty scope, if any. */
  for (cur_nonempty = qdpll->pcnf.scopes.first; 
       cur_nonempty && is_scope_effectively_empty (qdpll, cur_nonempty); 
       cur_nonempty = cur_nonempty->link.next);

  prev_nonempty = cur_nonempty;

  while (cur_nonempty)
    {
      assert (prev_nonempty);
      assert (!is_scope_effectively_empty (qdpll, cur_nonempty));
      assert (!is_scope_effectively_empty (qdpll, prev_nonempty));
      if (prev_nonempty->type != cur_nonempty->type)
        {
          /* Import previous scope in Nenofex (may contain variables from
             merged scopes). */
          assert (QDPLL_COUNT_STACK (svars) > 0);
          nenofex_add_orig_scope (qdpll->nenofex_oracle, 
                                  svars.start,
                                  QDPLL_COUNT_STACK (svars), 
                                  QDPLL_SCOPE_EXISTS (prev_nonempty) ? 
                                  SCOPE_TYPE_EXISTENTIAL : SCOPE_TYPE_UNIVERSAL);
          QDPLL_RESET_STACK (svars);
        }
      /* Collect variables in CURRENT scope. */
      import_prefix_collect_vars (qdpll, cur_nonempty, &svars);
      prev_nonempty = cur_nonempty;
      /* Move current scope to next non-empty scope. */
      for (cur_nonempty = cur_nonempty->link.next; 
           cur_nonempty && is_scope_effectively_empty (qdpll, cur_nonempty); 
           cur_nonempty = cur_nonempty->link.next);
    }
  if (prev_nonempty)
    {
      /* Import last scope in Nenofex. */
      assert (QDPLL_COUNT_STACK (svars) > 0);
      nenofex_add_orig_scope (qdpll->nenofex_oracle, 
                              svars.start,
                              QDPLL_COUNT_STACK (svars), 
                              QDPLL_SCOPE_EXISTS (prev_nonempty) ? 
                              SCOPE_TYPE_EXISTENTIAL : SCOPE_TYPE_UNIVERSAL);
    }
  QDPLL_DELETE_STACK (qdpll->mm, svars);
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
  VoidPtrStack lits;
  QDPLL_INIT_STACK (lits);
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

          /* TODO OPTIMIZATION: check for satisfied clauses in THIS loop,
             i.e. while collecting clause literals. This way, we avoid the
             additional traversals of clause literals in
             'is_clause_satisfied'. */

          QDPLL_RESET_STACK (lits);
          /* Import clause 'c' in Nenofex. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              /* Ignore literals of variables which are currently
                 assigned. These literals do not satisfy the clause (otherwise we
                 would not have entered this loop). */
              if (!QDPLL_VAR_ASSIGNED (var)) 
                QDPLL_PUSH_STACK (qdpll->mm, lits, (void *) ((long int) lit));
              else
                assert ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)) || 
                        (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)));
            }
	  nenofex_add_orig_clause (qdpll->nenofex_oracle, lits.start, QDPLL_COUNT_STACK (lits));
        }
    }
  QDPLL_DELETE_STACK (qdpll->mm, lits);
}

static void
import_qbf_under_current_assignment (QDPLL *qdpll)
{
  import_prefix_under_current_assignment (qdpll);
  import_cnf_under_current_assignment (qdpll);
}

static NenofexResult 
run_nenofex (QDPLL *qdpll)
{
  NenofexResult res = nenofex_solve (qdpll->nenofex_oracle);
  if (res == 10) return NENOFEX_RESULT_SAT;
  if (res == 20) return NENOFEX_RESULT_UNSAT;
  return NENOFEX_RESULT_UNKNOWN;
}

static void 
dynamic_nenofex_reset_and_init (QDPLL *qdpll)
{
  /* Delete current Nenofex object and create new one because Nenofex
     does not have a reset functions. */
  assert (qdpll->nenofex_oracle);
  nenofex_delete (qdpll->nenofex_oracle);
  qdpll->nenofex_oracle = nenofex_create ();
  char **sp, **se;
  for (sp = qdpll->nenofex_option_strings.start, 
         se = qdpll->nenofex_option_strings.top; sp < se; sp++)
    nenofex_configure (qdpll->nenofex_oracle, *sp);
}

/* ---------- START: public functions ---------- */

NenofexResult 
dynamic_nenofex_test (QDPLL *qdpll)
{
  NenofexResult result = NENOFEX_RESULT_UNKNOWN;
  /* Return immediately if calls of Nenofex have been disabled dynamically by
     number of calls and average calling time. */
  if (qdpll->state.dyn_nenofex_disabled)
    return NENOFEX_RESULT_UNKNOWN;

  /* Disable Nenofex calls if limit on number of clauses in original CNF exceeded. */
  if (qdpll->options.dyn_nenofex_disable_cnf_threshold && 
      qdpll->pcnf.clauses.cnt >= qdpll->options.dyn_nenofex_disable_cnf_threshold)
    {
      assert (!qdpll->state.dyn_nenofex_disabled);
      qdpll->state.dyn_nenofex_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling Nenofex calls: CNF size is %d, %d threshold\n", 
                 qdpll->pcnf.clauses.cnt, qdpll->options.dyn_nenofex_disable_cnf_threshold);
      return NENOFEX_RESULT_UNKNOWN;
    }

  qdpll->state.dyn_nenofex_calls++;
  double start_time = time_stamp (); 

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "Running dynamic Nenofex test.\n");

  dynamic_nenofex_reset_and_init (qdpll);
  fflush(stdout);

  nenofex_set_up_preamble (qdpll->nenofex_oracle, 
			   qdpll_get_max_declared_var_id (qdpll), 
			   qdpll->pcnf.clauses.cnt);

  import_qbf_under_current_assignment (qdpll);
  result = run_nenofex (qdpll);
  qdpll->state.dyn_nenofex_time += (time_stamp () - start_time); 
#if COMPUTE_STATS
  if (result == NENOFEX_RESULT_SAT)
    {
      qdpll->stats.dyn_nenofex_result_sat++;
      qdpll->stats.dyn_nenofex_success_dlevels += qdpll->state.decision_level;
      qdpll->stats.dyn_nenofex_cur_result_unknown_streak = 0;
    }
  else if (result == NENOFEX_RESULT_UNSAT)
    {
      qdpll->stats.dyn_nenofex_result_unsat++;
      qdpll->stats.dyn_nenofex_success_dlevels += qdpll->state.decision_level;
      qdpll->stats.dyn_nenofex_cur_result_unknown_streak = 0;
    }
  else
    {
      assert (result == NENOFEX_RESULT_UNKNOWN);
      qdpll->stats.dyn_nenofex_cur_result_unknown_streak++;
      if (qdpll->stats.dyn_nenofex_cur_result_unknown_streak > 
          qdpll->stats.dyn_nenofex_max_result_unknown_streak)
        qdpll->stats.dyn_nenofex_max_result_unknown_streak = 
          qdpll->stats.dyn_nenofex_cur_result_unknown_streak;
    }
#endif

  if (qdpll->options.dyn_nenofex_disable_calls_threshold > 0 && 
      qdpll->state.dyn_nenofex_calls >= qdpll->options.dyn_nenofex_disable_calls_threshold && 
      (qdpll->state.dyn_nenofex_time / qdpll->state.dyn_nenofex_calls) >= 
      qdpll->options.dyn_nenofex_disable_time_threshold)
    {
      assert (!qdpll->state.dyn_nenofex_disabled);
      qdpll->state.dyn_nenofex_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling Nenofex calls: average time is %f, %d calls\n", 
                 qdpll->state.dyn_nenofex_time / qdpll->state.dyn_nenofex_calls, qdpll->state.dyn_nenofex_calls);
    }

  return result;
}

/* ---------- END: public functions ---------- */
