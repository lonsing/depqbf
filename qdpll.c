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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <ctype.h>
#include <sys/resource.h>
#include "qdpll.h"
#include "qdpll_mem.h"
#include "qdpll_pcnf.h"
#include "qdpll_exit.h"
#include "qdpll_stack.h"
#include "qdpll_internals.h"
#include "qdpll_dep_man_generic.h"
#include "qdpll_dep_man_qdag.h"
#include "qdpll_config.h"
#include "qdpll_dynamic_nenofex.h"
#include "./picosat/picosat.h"

#define QDPLL_ABORT_QDPLL(cond,msg)					\
  do {									\
    if (cond)								\
      {									\
        fprintf (stderr, "[QDPLL] %s at line %d: %s\n", __func__,	\
                 __LINE__, msg);                                        \
        fflush (stderr);                                                \
        abort();                                                        \
      }									\
  } while (0)


/* Generic link-unlink macros */
#define LINK_LAST(anchor,element,link)		\
  do {						\
    assert (!(element)->link.prev);		\
    assert (!(element)->link.next);		\
    if ((anchor).last)				\
      {						\
        assert (!(anchor).last->link.next);	\
        assert ((anchor).first);                \
        assert (!(anchor).first->link.prev);	\
        (anchor).last->link.next = (element);	\
      }						\
    else                                        \
      {						\
        assert (!(anchor).first);		\
        (anchor).first = (element);		\
      }						\
    (element)->link.prev = (anchor).last;	\
    (anchor).last = (element);			\
    (anchor).cnt++;				\
  } while (0)

#define LINK_FIRST(anchor,element,link)		\
  do {						\
    assert (!(element)->link.prev);		\
    assert (!(element)->link.next);		\
    (element)->link.next = (anchor).first;	\
    if ((anchor).first)				\
      {						\
        assert ((anchor).last);			\
        (anchor).first->link.prev = (element);	\
      }						\
    else					\
      {						\
        assert (!(anchor).last);		\
        (anchor).last = (element);		\
      }						\
    (anchor).first = (element);			\
    (anchor).cnt++;				\
  } while (0)

#define UNLINK(anchor,element,link)				\
  do {								\
    assert ((anchor).cnt);					\
    if ((element)->link.prev)					\
      {								\
        assert ((anchor).first);                                \
        assert ((anchor).last);					\
        assert ((element)->link.prev->link.next == (element));	\
        (element)->link.prev->link.next = (element)->link.next; \
      }								\
    else                                                        \
      {								\
        assert ((anchor).first == (element));			\
        (anchor).first = (element)->link.next;			\
      }								\
    if ((element)->link.next)					\
      {								\
        assert ((anchor).first);                                \
        assert ((anchor).last);					\
        assert ((element)->link.next->link.prev == (element));	\
        (element)->link.next->link.prev = (element)->link.prev; \
      }								\
    else                                                        \
      {								\
        assert ((anchor).last == (element));			\
        (anchor).last = (element)->link.prev;			\
      }								\
    (element)->link.prev = (element)->link.next = 0;		\
    (anchor).cnt--;						\
  } while (0)


static int is_clause_empty (QDPLL * qdpll, Constraint * clause);

static int is_clause_satisfied (QDPLL * qdpll, Constraint * clause);

static int
has_variable_active_occs_in_clauses (QDPLL * qdpll, Var * var,
                                     BLitsOccStack * occ_clauses,
                                     int check_prop);

static void
push_assigned_variable (QDPLL * qdpll, Var * var, QDPLLAssignment assignment,
                        QDPLLVarMode mode);


/* -------------------- START: ASSERTION-ONLY CODE -------------------- */

static void
print_all_deps (QDPLL * qdpll)
{
  fprintf (stdout, "all deps:\n");
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          fprintf (stdout, "%d: ", p->id);
          qdpll_print_deps (qdpll, p->id);
          fprintf (stdout, "\n");
        }
    }
  fprintf (stdout, "end deps\n");
}

static void print_constraint (QDPLL * qdpll, Constraint * c);

static void
print_lit_notify_lists (QDPLL * qdpll, BLitsOccStack * notify_list)
{
  BLitsOcc *p, *e;
  for (p = notify_list->start, e = notify_list->top; p < e; p++)
    {
      print_constraint (qdpll, BLIT_STRIP_PTR (p->constraint));
      fprintf (stderr, "\n");
    }
}

static void
print_lit_notify_lists_info (QDPLL * qdpll)
{
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          fprintf (stderr, "Var %d, pos:\n", p->id);
          print_lit_notify_lists (qdpll, &(p->pos_notify_lit_watchers));
          fprintf (stderr, "Var %d, neg:\n", p->id);
          print_lit_notify_lists (qdpll, &(p->neg_notify_lit_watchers));
        }
    }
}


static void
print_vars_state (QDPLL * qdpll)
{
  unsigned int cnt_all, cnt_used;
  cnt_all = cnt_used = 0;
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      cnt_all++;
      if (p->id)
        {
          cnt_used++;
          int val;
          if (QDPLL_VAR_ASSIGNED_TRUE (p))
            val = 1;
          else if (QDPLL_VAR_ASSIGNED_FALSE (p))
            val = -1;
          else
            val = 0;
          fprintf (stderr, "Var %d: value=%d\n", p->id, val);
        }
    }
  assert (cnt_all == qdpll->pcnf.size_vars);
  assert (cnt_used == qdpll->pcnf.used_vars);
}


static int
check_depends (QDPLL * qdpll, VarID id1, VarID id2)
{
  return qdpll->dm->depends (qdpll->dm, id1, id2);
}

static void
print_var_pqueue (QDPLL * qdpll)
{
  fprintf (stderr, "var_pqueue:");
  VarID *p, *e;
  for (p = qdpll->var_pqueue, e = p + qdpll->cnt_var_pqueue; p < e; p++)
    fprintf (stderr, " %d", *p);
  fprintf (stderr, "\n");
}

static int
find_in_assigned_vars (QDPLL * qdpll, VarID id)
{
  VarID *p;
  for (p = qdpll->assigned_vars; p < qdpll->assigned_vars_top; p++)
    if (*p == id)
      return 1;

  return 0;
}


static unsigned int
count_in_notify_clause_watcher_list (LitIDStack * notify_list, LitID id)
{
  unsigned int cnt = 0;
  LitID *p, *e;
  for (p = notify_list->start, e = notify_list->top; p < e; p++)
    {
      assert (*p != 0);
      if (*p == id)
        cnt++;
    }

  return cnt;
}


static unsigned int
offset_in_notify_clause_watcher_list (LitIDStack * notify_list, LitID id)
{
  LitID *p, *e;
  for (p = notify_list->start, e = notify_list->top; p < e; p++)
    {
      assert (*p != 0);
      if (*p == id)
        return p - notify_list->start;
    }

  return -1;
}


static unsigned int
offset_in_clause (Constraint * clause, LitID id)
{
  assert (!clause->is_cube);
  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      assert (*p != 0);
      if (*p == id)
        return p - clause->lits;
    }

  return -1;
}


static unsigned int
count_in_notify_literal_watcher_list (BLitsOccStack * notify_list,
                                      Constraint * c)
{
  assert (!BLIT_MARKED_PTR (c));
  unsigned int cnt = 0;
  BLitsOcc *p, *e;
  for (p = notify_list->start, e = notify_list->top; p < e; p++)
    {
      Constraint *cp = BLIT_STRIP_PTR (p->constraint);
      if (cp == c)
        cnt++;
    }

  return cnt;
}


static void
print_assigned_vars (QDPLL * qdpll)
{
  Var *vars = qdpll->pcnf.vars, *v;

  VarID *p, *e;
  for (p = qdpll->assigned_vars, e = qdpll->assigned_vars_top; p < e; p++)
    {
      assert (*p > 0);
      v = VARID2VARPTR (vars, *p);
      fprintf (stderr,
               "id=%d, type=%c(%d), dlevel=%d, value=%d, mode=%d, prop=%d\n",
               v->id, QDPLL_SCOPE_FORALL (v->scope) ? 'A' : 'E',
               v->scope->nesting, v->decision_level, v->assignment, v->mode,
               v->mark_propagated);
    }
}


static void
print_lits (QDPLL * qdpll, LitID * lits, unsigned int num,
            unsigned int num_more)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = lits, e = p + num; p < e; p++)
    {
      LitID lit = *p;
      assert (*p);
      Var *var = LIT2VARPTR (vars, lit);
      fprintf (stderr, "%c(%d)%d",
               QDPLL_SCOPE_FORALL (var->scope) ? 'A' : 'E',
               var->scope->nesting, *p);
      if (QDPLL_VAR_ASSIGNED (var))
        {
          char mode_char = 'X';
          if (var->mode == QDPLL_VARMODE_UNIT)
            mode_char = 'U';
          else if (var->mode == QDPLL_VARMODE_PURE)
            mode_char = 'P';
          else if (var->mode == QDPLL_VARMODE_LBRANCH)
            mode_char = 'L';
          else if (var->mode == QDPLL_VARMODE_RBRANCH)
            mode_char = 'R';
	  else if (var->mode == QDPLL_VARMODE_ASSUMED)
	    mode_char = 'A';
          else
            assert (0);
          fprintf (stderr, "(%c%c)@%d",
                   QDPLL_VAR_ASSIGNED_TRUE (var) ? 'T' : 'F', mode_char,
                   var->decision_level);
        }
      fprintf (stderr, " ");
    }

  /* Print additional literals which were forall-reduced. This is only
     relevant for original clauses. Do not print info on quantifier,
     scope, assignment,... like above because scopes might have been
     released during cleanup. */
  for (p = e, e = lits + num_more; p < e; p++)
    {
      /* Can happen that '*p == 0' if input clause had multiple
         literals that were deleted. */
      if (*p)
        {
          fprintf (stderr, "%d", *p);
          fprintf (stderr, " ");
        }
    }

  fprintf (stderr, "\n");
}


static void
print_constraint (QDPLL * qdpll, Constraint * c)
{
  print_lits (qdpll, c->lits, c->num_lits, 0);
}

static int
constraint_has_lit (Constraint * c, LitID lit)
{
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      if (*p == lit)
        return 1;
    }

  return 0;
}


#ifndef NDEBUG

static void
assert_full_prefix_integrity_scopes (QDPLL * qdpll, Scope *s, Scope *n)
{
  assert (s->is_internal);
  assert (s->nesting != QDPLL_DEFAULT_SCOPE_NESTING
          || QDPLL_SCOPE_EXISTS (s));
  assert (s->nesting == QDPLL_DEFAULT_SCOPE_NESTING
          || QDPLL_COUNT_STACK (s->vars) != 0);
  if (n)
    {
      assert (s->nesting == n->nesting - 1);
      assert (s->type != n->type);
    }
  VarIDStack *scope_vars = &s->vars;
  VarID *p, *e, v;
  for (p = scope_vars->start, e = scope_vars->top; p < e; p++)
    {
      v = *p;
      assert (v < qdpll->pcnf.size_vars);
      Var *var = qdpll->pcnf.vars + v;
      /* If '!var->id' then 'var' was a no-occ internal variable which was cleaned up. */
      assert (var->id || s == qdpll->pcnf.scopes.first);
      if (!var->id)
        continue;
      assert (var->scope == s);
      assert (var->id == v);
      assert (!QDPLL_VAR_ASSIGNED (var) || var->mode == QDPLL_VARMODE_UNIT
              || var->mode == QDPLL_VARMODE_PURE || var->mode == QDPLL_VARMODE_ASSUMED);
      assert (!QDPLL_VAR_MARKED (var));
      assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
      /* Internal vars are usually expected to have occurrences, however, if
         the user does 'push' but then does not add any clauses then the internal
         variable allocated by that 'push' will be garbage-collected. */
      assert (var->is_internal || QDPLL_VAR_HAS_OCCS (var));

      BLitsOcc *bp, *be;
      for (bp = var->neg_occ_clauses.start, be = var->neg_occ_clauses.top;
           bp < be; bp++)
        assert (constraint_has_lit (BLIT_STRIP_PTR (bp->constraint), -v));
      for (bp = var->pos_occ_clauses.start, be = var->pos_occ_clauses.top;
           bp < be; bp++)
        assert (constraint_has_lit (BLIT_STRIP_PTR (bp->constraint), v));
    }
}


static void
assert_full_prefix_integrity_user_scopes (QDPLL * qdpll)
{
  assert (QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs) == 
          qdpll->pcnf.user_scopes.cnt);
  /* User scope nestings start at 1. */
  assert (qdpll->pcnf.user_scopes.cnt == (qdpll->pcnf.user_scopes.last ? 
                                          qdpll->pcnf.user_scopes.last->nesting : 0));
  Scope *usn, *us = qdpll->pcnf.user_scopes.first;
  Scope **se, **sp;
  for (sp = qdpll->pcnf.user_scope_ptrs.start,  
         se = qdpll->pcnf.user_scope_ptrs.top; sp < se; sp++)
    {
      assert (us);
      assert (us->link.prev || us->nesting == QDPLL_DEFAULT_SCOPE_NESTING + 1);
      assert (!us->is_internal);
      assert (us == *sp);
      usn = us->link.next;
      assert (!usn || usn->nesting == us->nesting + 1);
      VarID *p, *e;
      for (p = us->vars.start, e = us->vars.top; p < e; p++)
        {
          Var *var = VARID2VARPTR(qdpll->pcnf.vars, *p);
          /* Bug Fix: handle user variables which have been reset because they had no occs. */
          /* Another bug fix: one and the same variable ID might have pushed
             multiple times on the us->vars stack, e.g. by
             'qdpll_add_var_to_scope', but we will detect that only after the
             user scopes have been full imported. */
          assert (!var->id || !qdpll->state.no_scheduled_import_user_scopes || 
                  var->offset_in_user_scope_vars == (unsigned int)(p - us->vars.start));
        }
      us = usn;
    }
  assert (!us);
}


static int
assert_full_prefix_integrity_find_var (VarID id, VarID *start, VarID *end)
{
  assert (start <= end);
  VarID *p, *e;
  for (p = start, e = end; p < e; p++)
    if (*p == id)
      return 1;
  return 0;
}


static void
assert_full_prefix_integrity (QDPLL * qdpll)
{
  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  assert (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.first));
  /* Internal scope nestings start at 0. */
  assert (qdpll->pcnf.scopes.cnt == qdpll->pcnf.scopes.last->nesting + 1);

  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
      assert_full_prefix_integrity_scopes (qdpll, s, n);
    }

  assert_full_prefix_integrity_user_scopes (qdpll);

  /* Count used variables (user-vars and internal ones). */
  unsigned int cnt_used = 0;
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (!p->id)
        continue;
      cnt_used++;
      /* A variable is internal iff it is stored in the internal part of the
         variable table. */
      assert (!p->is_internal || p >= qdpll->pcnf.vars + qdpll->pcnf.size_user_vars);
      assert (p < qdpll->pcnf.vars + qdpll->pcnf.size_user_vars || p->is_internal);
      if (p->is_internal)
        {
          assert (!p->is_cur_inactive_group_selector || p->is_cur_used_internal_var);
          assert (p->clause_group_id > 0);
          assert (p->scope);
          assert (!p->user_scope);
          /* A declared (i.e. non-zero ID) internal var must appear on either
             stack 'qdpll->state.cur_used_internal_vars' or stack
             'qdpll->state.popped_off_internal_vars'. */
          assert (p->id);
          assert (!p->is_cur_used_internal_var || 
                  assert_full_prefix_integrity_find_var (p->id, qdpll->state.cur_used_internal_vars.start, 
                                                         qdpll->state.cur_used_internal_vars.top));
          assert (p->is_cur_used_internal_var ||
                  assert_full_prefix_integrity_find_var (p->id, qdpll->state.popped_off_internal_vars.start, 
                                                         qdpll->state.popped_off_internal_vars.top));
        }
      else
        assert (p->clause_group_id == 0);
    }
  assert (cnt_used == qdpll->pcnf.used_vars);
}


static int
occs_have_constraint (LitID lit, BLitsOccStack * occ_list, Constraint * c)
{
  assert (!BLIT_MARKED_PTR (c));
  BLitsOcc *bp, *be;
  for (bp = occ_list->start, be = occ_list->top; bp < be; bp++)
    {
      if (BLIT_STRIP_PTR (bp->constraint) == c)
        return 1;
    }
  return 0;
}


static unsigned int
count_occs (LitID lit, BLitsOccStack * occs)
{
  unsigned int res = 0;
  BLitsOcc *bp, *be;
  for (bp = occs->start, be = occs->top; bp < be; bp++)
    res++;
  return res;
}


static LitID
find_selector_literal (QDPLL *qdpll, Constraint *c);

static unsigned int
count_selector_literals (QDPLL *qdpll, Constraint *c);

static void
assert_full_cnf_integrity_for_clauses (QDPLL * qdpll,
                                       ConstraintList * clause_list)
{
  Constraint *c, *n;
  for (c = clause_list->first; c; c = n)
    {
      n = c->link.next;
      if (qdpll->state.cnt_created_clause_groups > 0 || 
          QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0)
        {
          /* In incremental mode: original clauses have exactly one selector
             literal (unless they are permanently added). Learned clauses also
             if we use the optimized handling of selector literals based on
             chronological ordering of frame indices. */
          assert (clause_list != &qdpll->pcnf.clauses || count_selector_literals (qdpll, c) <= 1);
          assert (clause_list != &qdpll->pcnf.learnt_clauses || 
                  (qdpll->state.clause_group_api_called || count_selector_literals (qdpll, c) <= 1));
        }
      assert (!c->is_cube);
      LitID *p1, *p2, *e, lit1, lit2;
      for (p1 = c->lits, e = p1 + c->num_lits; p1 < e; p1++)
        {
          lit1 = *p1;
          assert (lit1);
          Var *v1 = LIT2VARPTR (qdpll->pcnf.vars, lit1);
          assert (QDPLL_VAR_HAS_OCCS(v1));
          assert (QDPLL_COUNT_STACK (v1->neg_occ_clauses) ==
                  count_occs (-v1->id, &v1->neg_occ_clauses));
          assert (QDPLL_COUNT_STACK (v1->pos_occ_clauses) ==
                  count_occs (v1->id, &v1->pos_occ_clauses));

          /* Check only if we use full occ-lists for pure literals. */
          if (QDPLL_LIT_NEG (lit1))
            assert (occs_have_constraint (lit1, &v1->neg_occ_clauses, c));
          else
            assert (occs_have_constraint (lit1, &v1->pos_occ_clauses, c));

          for (p2 = p1 + 1; p2 < e; p2++)
            {
              lit2 = *p2;
              assert (lit2 != lit1);
              assert (lit2 != -lit1);
              Var *v2 = LIT2VARPTR (qdpll->pcnf.vars, lit2);
              assert (v1->scope->nesting <= v2->scope->nesting);
            }
        }
    }
}


static unsigned int
count_constraints (ConstraintList * list)
{
  unsigned int res = 0;
  Constraint *c;
  for (c = list->first; c; c = c->link.next)
    res++;
  return res;
}


static void
assert_full_cnf_integrity (QDPLL * qdpll)
{
  assert (qdpll->pcnf.clauses.cnt ==
          count_constraints (&(qdpll->pcnf.clauses)));
  assert_full_cnf_integrity_for_clauses (qdpll, &(qdpll->pcnf.clauses));
  if (qdpll->options.no_spure_literals &&
      !qdpll->options.no_pure_literals)
    assert_full_cnf_integrity_for_clauses (qdpll,
                                           &(qdpll->pcnf.learnt_clauses));
}


static void
assert_full_formula_integrity (QDPLL * qdpll)
{
  assert_full_prefix_integrity (qdpll);
  assert_full_cnf_integrity (qdpll);
}


static void
assert_notify_lists_integrity_by_watcher (QDPLL * qdpll, LitID signed_id,
                                          Constraint * watched_constraint)
{
  if (watched_constraint->qbcp_qbce_blocked)
    return;
  assert (watched_constraint->is_watched);
  LitID *p, *e;
  for (p = watched_constraint->lits, e = p + watched_constraint->num_lits;
       p < e; p++)
    {
      assert (*p != 0);
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, *p);

      if (LIT2VARID (*p) == LIT2VARID (signed_id))
        continue;

      if (*p < 0)
        {
          if (!watched_constraint->is_cube)
            assert (count_in_notify_clause_watcher_list
                    (&(var->neg_notify_clause_watchers), signed_id) == 1);
          else
            assert (count_in_notify_clause_watcher_list
                    (&(var->pos_notify_clause_watchers), signed_id) == 1);

        }
      else
        {
          if (!watched_constraint->is_cube)
            assert (count_in_notify_clause_watcher_list
                    (&(var->pos_notify_clause_watchers), signed_id) == 1);
          else
            assert (count_in_notify_clause_watcher_list
                    (&(var->neg_notify_clause_watchers), signed_id) == 1);
        }
    }
}


static void
assert_incremental_selector_vars (QDPLL *qdpll)
{
  VarID *p, *e;
  for (p = qdpll->state.popped_off_internal_vars.start, 
         e = qdpll->state.popped_off_internal_vars.top; p < e; p++)
    {
      /* Unused internal vars must be set to TRUE so that the clauses are NOT
         active in the formula. */
      VarID id = *p;
      assert (id);
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      assert (!var->is_cur_used_internal_var);
      assert (!var->is_cur_inactive_group_selector);
      /* Stack may contain former internal variables which might have been
         cleaned up because they did not have occurrences. */
      assert (!var->id || QDPLL_VAR_ASSIGNED_TRUE (var));
    }
  for (p = qdpll->state.cur_used_internal_vars.start, 
         e = qdpll->state.cur_used_internal_vars.top; p < e; p++)
    {
      /* Used internal vars which are selectors of activated (deactivated)
         groups must be set to FALSE (TRUE) so that the clauses are active in
         the formula. */
      VarID id = *p;
      if (id)
        {
          Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
          assert (var->is_cur_used_internal_var);
          /* Stack may contain former internal variables which might have been
             cleaned up because they did not have occurrences. */
          if (var->id)
            {
              assert (var->is_cur_inactive_group_selector || QDPLL_VAR_ASSIGNED_FALSE (var));
              assert (!var->is_cur_inactive_group_selector || QDPLL_VAR_ASSIGNED_TRUE (var));
            }
        }
    }
}

static int
has_variable_active_occs_in_cubes (QDPLL * qdpll, Var * var,
                                   BLitsOccStack * occ_cubes);

/* Traverse all variables and check if:
   - all pure variables have been found and pushed on assigned stack
   - all clause watchers are set correctly
   Check should be done EACH TIME BEFORE AND AFTER a variable has been (un)assigned.
*/
static void
assert_all_pure_literals_and_clause_watchers_integrity (QDPLL * qdpll)
{
  Var *vars = qdpll->pcnf.vars;

  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      VarIDStack *scope_vars = &s->vars;
      VarID *p, *e;
      for (p = scope_vars->start, e = scope_vars->top; p < e; p++)
        {
          assert (*p > 0 && *p < qdpll->pcnf.size_vars);
          Var *var = VARID2VARPTR (vars, *p);

          assert (!QDPLL_VAR_MARKED_PROPAGATED (var)
                  || QDPLL_VAR_ASSIGNED (var));
          assert (QDPLL_VAR_ASSIGNED (var)
                  || !QDPLL_VAR_MARKED_PROPAGATED (var));

          if (qdpll->options.no_pure_literals)
            continue;

          int has_active_neg_occs_in_clauses =
            has_variable_active_occs_in_clauses (qdpll, var,
                                                 &(var->neg_occ_clauses), 0);
          int has_active_pos_occs_in_clauses =
            has_variable_active_occs_in_clauses (qdpll, var,
                                                 &(var->pos_occ_clauses), 0);
          int has_active_neg_occs_in_cubes =
            has_variable_active_occs_in_cubes (qdpll, var,
                                               &(var->neg_occ_cubes));
          int has_active_pos_occs_in_cubes =
            has_variable_active_occs_in_cubes (qdpll, var,
                                               &(var->pos_occ_cubes));

          if (has_active_neg_occs_in_clauses
              && !has_active_pos_occs_in_clauses
              && !has_active_pos_occs_in_cubes)
            {                   /* Pure: only negative occurrences left. */
              /* Variable must have been pushed, but not necessarily propagated already. */
              assert (find_in_assigned_vars (qdpll, var->id));
              assert (QDPLL_VAR_ASSIGNED (var));
              assert (!QDPLL_VAR_EXISTS (var)
                      || QDPLL_VAR_ASSIGNED_FALSE (var));
              assert (!QDPLL_VAR_FORALL (var)
                      || QDPLL_VAR_ASSIGNED_TRUE (var));

              /* Exactly one watcher must be satisfied. */
              assert (!QDPLL_VAR_HAS_NEG_OCCS (var) ||
                      !is_clause_satisfied (qdpll,
                                            BLIT_STRIP_PTR (var->
                                                            neg_occ_clauses.
                                                            start[0].
                                                            constraint)));
              assert (!QDPLL_VAR_HAS_POS_OCCS (var)
                      || is_clause_satisfied (qdpll,
                                              BLIT_STRIP_PTR (var->
                                                              pos_occ_clauses.
                                                              start[0].
                                                              constraint)));

            }
          else if (!has_active_neg_occs_in_clauses
                   && !has_active_neg_occs_in_cubes
                   && has_active_pos_occs_in_clauses)
            {                   /* Pure: only pos occurrences left. */
              /* Variable must have been pushed, but not necessarily propagated already. */
              assert (find_in_assigned_vars (qdpll, var->id));
              assert (QDPLL_VAR_ASSIGNED (var));
              assert (!QDPLL_VAR_EXISTS (var)
                      || QDPLL_VAR_ASSIGNED_TRUE (var));
              assert (!QDPLL_VAR_FORALL (var)
                      || QDPLL_VAR_ASSIGNED_FALSE (var));
              /* Exactly one watcher must be satisfied. */
              assert (!QDPLL_VAR_HAS_POS_OCCS (var) ||
                      !is_clause_satisfied (qdpll,
                                            BLIT_STRIP_PTR (var->
                                                            pos_occ_clauses.
                                                            start[0].
                                                            constraint)));
              assert (!QDPLL_VAR_HAS_NEG_OCCS (var)
                      || is_clause_satisfied (qdpll,
                                              BLIT_STRIP_PTR (var->
                                                              neg_occ_clauses.
                                                              start[0].
                                                              constraint)));
            }
          else if (!has_active_neg_occs_in_clauses
                   && !has_active_pos_occs_in_clauses
                   && !has_active_pos_occs_in_cubes
                   && !has_active_neg_occs_in_cubes)
            {                   /* Eliminated: no occurrences left. */
              assert (!QDPLL_VAR_HAS_POS_OCCS (var)
                      || (!QDPLL_VAR_MARKED_PROPAGATED (var)
                          || QDPLL_VAR_ASSIGNED_FALSE (var))
                      || is_clause_satisfied (qdpll,
                                              BLIT_STRIP_PTR (var->
                                                              pos_occ_clauses.
                                                              start[0].
                                                              constraint)));
              assert (!QDPLL_VAR_HAS_NEG_OCCS (var)
                      || (!QDPLL_VAR_MARKED_PROPAGATED (var)
                          || QDPLL_VAR_ASSIGNED_TRUE (var))
                      || is_clause_satisfied (qdpll,
                                              BLIT_STRIP_PTR (var->
                                                              neg_occ_clauses.
                                                              start[0].
                                                              constraint)));
            }
          else
            {                   /* Neither pure nor eliminated: both types of occurrences left. */
              assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
              assert (!QDPLL_VAR_HAS_POS_OCCS (var) ||
                      !is_clause_satisfied (qdpll,
                                            BLIT_STRIP_PTR (var->
                                                            pos_occ_clauses.
                                                            start[0].
                                                            constraint))
                      || has_active_pos_occs_in_cubes);
              assert (!QDPLL_VAR_HAS_NEG_OCCS (var)
                      || !is_clause_satisfied (qdpll,
                                               BLIT_STRIP_PTR (var->
                                                               neg_occ_clauses.
                                                               start[0].
                                                               constraint))
                      || has_active_neg_occs_in_cubes);
            }

          /* Check notify lists wrt. watched clauses. */
          if (QDPLL_VAR_HAS_NEG_OCCS (var)
              && !(QDPLL_VAR_ASSIGNED (var) && var->decision_level == 0))
            {
              if (!var->mark_is_neg_watching_cube)
                assert_notify_lists_integrity_by_watcher (qdpll, -var->id,
                                                          BLIT_STRIP_PTR
                                                          (var->
                                                           neg_occ_clauses.
                                                           start[0].
                                                           constraint));
              else
                assert_notify_lists_integrity_by_watcher (qdpll, -var->id,
                                                          BLIT_STRIP_PTR
                                                          (var->neg_occ_cubes.
                                                           start[0].
                                                           constraint));
            }

          if (QDPLL_VAR_HAS_POS_OCCS (var)
              && !(QDPLL_VAR_ASSIGNED (var) && var->decision_level == 0))
            {
              if (!var->mark_is_pos_watching_cube)
                assert_notify_lists_integrity_by_watcher (qdpll, var->id,
                                                          BLIT_STRIP_PTR
                                                          (var->pos_occ_clauses.
                                                           start[0].
                                                           constraint));
              else
                assert_notify_lists_integrity_by_watcher (qdpll, var->id,
                                                          BLIT_STRIP_PTR
                                                          (var->pos_occ_cubes.
                                                           start[0].
                                                           constraint));
            }
        }
    }
}


static int
is_constraint_decided (QDPLL * qdpll, Constraint * c)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      assert (var->id);
      if (!c->is_cube)
        {
          if ((QDPLL_VAR_ASSIGNED_TRUE (var) && QDPLL_LIT_POS (lit)) ||
              (QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_NEG (lit)))
            return 1;
        }
      else
        {
          if ((QDPLL_VAR_ASSIGNED_TRUE (var) && QDPLL_LIT_NEG (lit)) ||
              (QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_POS (lit)))
            return 1;
        }
    }
  return 0;
}


static int has_constraint_spurious_pure_lit (QDPLL * qdpll, Constraint * c);

/* Satisfied/empty clauses/cubes do not maintain lit-watcher integrity. */
static int
assert_constraint_ignore_lit_watchers (QDPLL * qdpll, Constraint * c)
{
  const int is_cube = c->is_cube;
  Var *vars = qdpll->pcnf.vars;
  /* Search for disabling literals. */
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      if (c->is_cube)
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 1;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 1;
            }
        }
      else
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 1;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 1;
            }
        }
    }

  return 0;
}


static void
  assert_all_unit_literals_and_literal_watchers_integrity_for_clauses
  (QDPLL * qdpll, ConstraintList * clause_list)
{
  Var *vars = qdpll->pcnf.vars;
  Constraint *c;
  for (c = clause_list->first; c; c = c->link.next)
    {
      assert (!c->deleted);

      const int is_cube = c->is_cube;

      if (c->num_lits < 2)
        continue;

      /* Skip blocked clauses. They are ignored anyway during unit literal
         propagation and can never be used as antecedents of unit
         implications. */
      if (c->qbcp_qbce_blocked)
        continue;

      assert ((c->rwatcher_pos == c->lwatcher_pos
               && c->rwatcher_pos == QDPLL_INVALID_WATCHER_POS)
              || (c->lwatcher_pos < c->rwatcher_pos
                  && c->lwatcher_pos != QDPLL_INVALID_WATCHER_POS
                  && c->rwatcher_pos != QDPLL_INVALID_WATCHER_POS));

      if (c->lwatcher_pos == QDPLL_INVALID_WATCHER_POS ||
          c->rwatcher_pos == QDPLL_INVALID_WATCHER_POS)
        {
          assert (c->rwatcher_pos == c->lwatcher_pos);
          assert_constraint_ignore_lit_watchers (qdpll, c);
          continue;
        }

      assert (c->num_lits < 2 || c->lwatcher_pos < c->rwatcher_pos);
      assert (c->rwatcher_pos < c->num_lits);
      assert (c->lwatcher_pos < c->num_lits);

      unsigned int lwpos = c->lwatcher_pos;
      unsigned int rwpos = c->rwatcher_pos;

      LitID *lits = c->lits;
      LitID rwlit = *(lits + rwpos);
      LitID lwlit = *(lits + lwpos);
      assert (rwlit != 0);
      assert (lwlit != 0);
      assert (c->num_lits < 2 || rwlit != lwlit);
      assert (-rwlit != lwlit);

      Var *rwvar = LIT2VARPTR (vars, rwlit);
      Var *lwvar = LIT2VARPTR (vars, lwlit);
      assert (is_cube || QDPLL_VAR_EXISTS (rwvar));
      assert (!is_cube || QDPLL_VAR_FORALL (rwvar));

      int ignore = 0;
      if (lwvar->decision_level != QDPLL_INVALID_DECISION_LEVEL ||
          rwvar->decision_level != QDPLL_INVALID_DECISION_LEVEL)
        {
          ignore = 1;
          /* Conjecture: this assertion-function is called only if BCP
             saturated. Then, if a watcher still points to assigned
             literal, then the constraint must be irrelevant under the
             current assignment. */
          assert_constraint_ignore_lit_watchers (qdpll, c);
        }

      if (1 || qdpll->dm->is_init (qdpll->dm))
        {
          if (is_cube)
            {
              assert ((QDPLL_VAR_FORALL (lwvar) && QDPLL_VAR_FORALL (rwvar))
                      || (QDPLL_VAR_EXISTS (lwvar) && QDPLL_VAR_FORALL (rwvar)
                          && qdpll->dm->depends (qdpll->dm, lwvar->id,
                                                 rwvar->id)));
            }
          else
            {
              assert ((QDPLL_VAR_EXISTS (lwvar) && QDPLL_VAR_EXISTS (rwvar))
                      || (QDPLL_VAR_FORALL (lwvar) && QDPLL_VAR_EXISTS (rwvar)
                          && qdpll->dm->depends (qdpll->dm, lwvar->id,
                                                 rwvar->id)));
            }
        }

      assert (!QDPLL_VAR_ASSIGNED (rwvar) || is_constraint_decided (qdpll, c)
              || has_constraint_spurious_pure_lit (qdpll, c));
      assert (!QDPLL_VAR_ASSIGNED (lwvar) || is_constraint_decided (qdpll, c)
              || has_constraint_spurious_pure_lit (qdpll, c));

      BLitsOccStack *notify_list;
      if (QDPLL_LIT_NEG (rwlit))
        {
          if (!is_cube)
            notify_list = &(rwvar->pos_notify_lit_watchers);
          else
            notify_list = &(rwvar->neg_notify_lit_watchers);

          assert (count_in_notify_literal_watcher_list (notify_list, c) == 1);
          assert (QDPLL_COUNT_STACK (*notify_list) == 0 ||
                  c->offset_in_notify_list[1] <
                  QDPLL_COUNT_STACK (*notify_list));
          assert (QDPLL_COUNT_STACK (*notify_list) == 0
                  || c ==
                  BLIT_STRIP_PTR (notify_list->
                                  start[c->offset_in_notify_list[1]].
                                  constraint));
        }
      else
        {
          if (!is_cube)
            notify_list = &(rwvar->neg_notify_lit_watchers);
          else
            notify_list = &(rwvar->pos_notify_lit_watchers);

          assert (count_in_notify_literal_watcher_list (notify_list, c) == 1);
          assert (QDPLL_COUNT_STACK (*notify_list) == 0 ||
                  c->offset_in_notify_list[1] <
                  QDPLL_COUNT_STACK (*notify_list));
          assert (QDPLL_COUNT_STACK (*notify_list) == 0
                  || c ==
                  BLIT_STRIP_PTR (notify_list->
                                  start[c->offset_in_notify_list[1]].
                                  constraint));
        }

      if (QDPLL_LIT_NEG (lwlit))
        {
          if (!is_cube)
            notify_list = &(lwvar->pos_notify_lit_watchers);
          else
            notify_list = &(lwvar->neg_notify_lit_watchers);

          assert (count_in_notify_literal_watcher_list (notify_list, c) == 1);
          assert (QDPLL_COUNT_STACK (*notify_list) == 0 ||
                  c->offset_in_notify_list[0] <
                  QDPLL_COUNT_STACK (*notify_list));
          assert (QDPLL_COUNT_STACK (*notify_list) == 0
                  || c ==
                  BLIT_STRIP_PTR (notify_list->
                                  start[c->offset_in_notify_list[0]].
                                  constraint));
        }
      else
        {
          if (!is_cube)
            notify_list = &(lwvar->neg_notify_lit_watchers);
          else
            notify_list = &(lwvar->pos_notify_lit_watchers);

          assert (count_in_notify_literal_watcher_list (notify_list, c) == 1);
          assert (QDPLL_COUNT_STACK (*notify_list) == 0 ||
                  c->offset_in_notify_list[0] <
                  QDPLL_COUNT_STACK (*notify_list));
          assert (QDPLL_COUNT_STACK (*notify_list) == 0
                  || c ==
                  BLIT_STRIP_PTR (notify_list->
                                  start[c->offset_in_notify_list[0]].
                                  constraint));
        }

      LitID *ip, *ie;
      for (ip = c->lits, ie = c->lits + c->num_lits; ip < ie; ip++)
        {
          if ((unsigned int) (ip - c->lits) != lwpos
              && (unsigned int) (ip - c->lits) != rwpos)
            {
              Var *other = LIT2VARPTR (vars, *ip);
              /* Adapt assertions to long-distance resolution: the current
                 literal of variable 'other' is not watched, but the
                 complementary occurrence in that clause might be watched if that
                 clause is tautological. */
              if (other->id == LIT2VARPTR(vars, c->lits[lwpos])->id || 
                  other->id == LIT2VARPTR(vars, c->lits[rwpos])->id)
                {
                  assert (qdpll->options.long_dist_res);
                  assert (*ip == -c->lits[lwpos] || *ip == -c->lits[rwpos]);
                  continue;
                }
              assert (count_in_notify_literal_watcher_list
                      (&(other->pos_notify_lit_watchers), c) == 0);
              assert (count_in_notify_literal_watcher_list
                      (&(other->neg_notify_lit_watchers), c) == 0);
            }
        }
    }
}


static void
assert_all_unit_literals_and_literal_watchers_integrity (QDPLL * qdpll)
{
  assert_all_unit_literals_and_literal_watchers_integrity_for_clauses (qdpll,
                                                                       &
                                                                       (qdpll->
                                                                        pcnf.
                                                                        clauses));
  assert_all_unit_literals_and_literal_watchers_integrity_for_clauses (qdpll,
                                                                       &
                                                                       (qdpll->
                                                                        pcnf.
                                                                        learnt_clauses));
  assert_all_unit_literals_and_literal_watchers_integrity_for_clauses (qdpll,
                                                                       &
                                                                       (qdpll->
                                                                        pcnf.
                                                                        learnt_cubes));
}


static void
assert_candidates_on_pqueue (QDPLL * qdpll)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      /* All variables which are candidates must be either (already)
         assigned or must occur on priority queue. */
      if (p->id)
        assert (!dm->is_candidate (dm, p->id) || QDPLL_VAR_ASSIGNED (p)
                || p->priority_pos != QDPLL_INVALID_PQUEUE_POS);
    }
}


static void
assert_learn_vars_unmarked (QDPLL * qdpll)
{
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      assert (!p->mark_learn0);
      assert (!p->mark_learn1);
      /* For cleaning up conflict clause, must also check that respective marks are cleared. */
      assert (!QDPLL_VAR_POS_MARKED (p));
      assert (!QDPLL_VAR_NEG_MARKED (p));
      assert (!QDPLL_VAR_MARKED (p));
    }
}


/* This is for checking asserting clauses only. */
static int
assert_is_clause_satisfied_by_univ_lit (QDPLL * qdpll, LitID implied,
                                        Constraint * clause)
{
  assert (!clause->is_cube);
  int found_implied = 0;
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      if (lit != implied)
        {
          Var *var = LIT2VARPTR (vars, lit);
          if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
              (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
            {
              if (!QDPLL_SCOPE_FORALL (var->scope))
                return 0;
              if (!found_implied)
                return 0;
              /* Clause must be satisfied by universal pure literal. */
              if (!(var->mode == QDPLL_VARMODE_PURE))
                return 0;
            }
        }
      else
        found_implied = 1;
    }
  return 1;
}


static void
assert_lits_sorted (QDPLL * qdpll, LitID * lit_start, LitID * lit_end)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *prev, *e;
  for (prev = p = lit_start, e = lit_end; p < e; p++)
    {
      if (!*p)
        continue;
      Var *pvar = LIT2VARPTR (vars, *p);
      Var *prev_var = LIT2VARPTR (vars, *prev);
      Nesting pvar_nesting, prev_var_nesting;
      /* Compare by user-scope nestings but must handle internal and free
         variables properly. */
      assert (pvar->user_scope || pvar->scope);
      pvar_nesting = pvar->user_scope ? 
        pvar->user_scope->nesting : pvar->scope->nesting;
      assert (prev_var->user_scope || prev_var->scope);
      prev_var_nesting = prev_var->user_scope ? 
        prev_var->user_scope->nesting : prev_var->scope->nesting;
      /* Fix: input formula might have adjacent user scopes of same type:
         internally, variables from these scopes are merged into a single scope,
         but will be ordered by their user scope ordering. However, they appear
         in the same internal scope then. */
      assert (prev_var_nesting <= pvar_nesting || 
              (pvar->user_scope && prev_var->user_scope && 
               pvar->user_scope->type == prev_var->user_scope->type && 
               pvar->scope && prev_var->scope && 
               pvar->scope == prev_var->scope));
      /* Internal variables must appear to the left of non-internals. */
      assert (prev_var->is_internal || !pvar->is_internal);
      prev = p;
    }
}


static void
assert_lits_unassigned (QDPLL * qdpll, LitID * lit_start, LitID * lit_end)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = lit_start, e = lit_end; p < e; p++)
    {
      assert (*p);
      Var *pvar = LIT2VARPTR (vars, *p);
      assert (!QDPLL_VAR_ASSIGNED (pvar));
      assert (pvar->decision_level == QDPLL_INVALID_DECISION_LEVEL);
    }
}


static void
assert_pushed_pure_lits (QDPLL * qdpll)
{
  Var *vars = qdpll->pcnf.vars;
  VarID *p, *e;
  for (p = qdpll->assigned_vars, e = qdpll->assigned_vars_top; p < e; p++)
    {
      Var *var = VARID2VARPTR (vars, *p);
      if (var->mode == QDPLL_VARMODE_PURE)
        {
          int has_neg_occ_clauses =
            has_variable_active_occs_in_clauses (qdpll, var,
                                                 &(var->neg_occ_clauses), 0);
          int has_pos_occ_clauses =
            has_variable_active_occs_in_clauses (qdpll, var,
                                                 &(var->pos_occ_clauses), 0);
          int has_pos_occ_cubes =
            has_variable_active_occs_in_cubes (qdpll, var,
                                               &(var->pos_occ_cubes));
          int has_neg_occ_cubes =
            has_variable_active_occs_in_cubes (qdpll, var,
                                               &(var->neg_occ_cubes));
          assert (!(has_neg_occ_clauses && has_pos_occ_clauses));
          assert (!(has_neg_occ_cubes && has_pos_occ_cubes));
          assert (!(has_neg_occ_clauses && has_pos_occ_cubes));
          assert (!(has_pos_occ_clauses && has_neg_occ_cubes));
          if (QDPLL_SCOPE_FORALL (var->scope))
            {
              if (var->assignment == QDPLL_ASSIGNMENT_FALSE)
                {
                  assert (!has_neg_occ_clauses && !has_neg_occ_cubes);
                }
              else
                {
                  assert (var->assignment == QDPLL_ASSIGNMENT_TRUE);
                  assert (!has_pos_occ_clauses && !has_pos_occ_cubes);
                }
            }
          else
            {
              assert (QDPLL_SCOPE_EXISTS (var->scope));
              if (var->assignment == QDPLL_ASSIGNMENT_FALSE)
                {
                  assert (!has_pos_occ_clauses && !has_pos_occ_cubes);
                }
              else
                {
                  assert (var->assignment == QDPLL_ASSIGNMENT_TRUE);
                  assert (!has_neg_occ_clauses && !has_neg_occ_cubes);
                }
            }
        }
    }
}


static unsigned int
get_highest_type_lit_dec_level (QDPLL * qdpll, LitID * lit_start,
                                LitID * lit_end,
                                const QDPLLQuantifierType type);
static Var *get_type_var_at_dec_level (QDPLL * qdpll, LitID * lit_start,
                                       LitID * lit_end, unsigned int level,
                                       const QDPLLQuantifierType type);
static unsigned int count_type_lit_at_dec_level (QDPLL * qdpll,
                                                 LitID * lit_start,
                                                 LitID * lit_end,
                                                 unsigned int level,
                                                 const QDPLLQuantifierType
                                                 type);
static void
assert_stop_crit_data (QDPLL * qdpll, LitIDStack * lit_stack,
                       const QDPLLQuantifierType type)
{
  assert (QDPLL_COUNT_STACK (*lit_stack) > 0);
  unsigned int max_type_level =
    get_highest_type_lit_dec_level (qdpll, lit_stack->start, lit_stack->top,
                                    type);
  assert (max_type_level == qdpll->hi_type_dl);
  Var *type_var =
    get_type_var_at_dec_level (qdpll, lit_stack->start, lit_stack->top,
                               max_type_level, type);
  assert (type_var->decision_level == qdpll->hi_dl_type_var->decision_level);
  assert (count_type_lit_at_dec_level
          (qdpll, lit_stack->start, lit_stack->top, max_type_level,
           type) == qdpll->cnt_hi_dl_type_lits);
}


static void
assert_is_lit_irreducible_aux (QDPLL * qdpll, LitID lit, LitID * start,
                               LitID * end)
{
  assert (start <= end);
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *vars = qdpll->pcnf.vars;
  Var *lit_var = LIT2VARPTR (vars, lit);
  LitID *p, *e;
  for (p = start, e = end; p < e; p++)
    {
      Var *var = LIT2VARPTR (vars, *p);
      if (!(QDPLL_VAR_ASSIGNED (var) && var->decision_level == 0)
          && dm->depends (dm, lit_var->id, var->id))
        break;
    }
  assert (p < e);
  QDPLL_ABORT_QDPLL (p >= e, "reducible lit!");
}

#endif

static void
assert_peek_taut_lit_irreducible_aux (QDPLL * qdpll, Var * taut_var,
                                      LitID * start, LitID * end)
{
  assert (!qdpll->options.long_dist_res);
  assert (start <= end);
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *vars = qdpll->pcnf.vars;
  int taut_lit_found = 0;
  LitID *p, *e;
  for (p = start, e = end; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      if (var == taut_var)
        taut_lit_found = 1;
      if (!(QDPLL_VAR_ASSIGNED (var) && var->decision_level == 0)
          && dm->depends (dm, taut_var->id, var->id))
        break;
    }
  assert (taut_lit_found);
  /* Unexpected behaviour: lit-list fully traversed without finding
     dependency. */
  assert (p < e);
  QDPLL_ABORT_QDPLL (!taut_lit_found || p >= e, "taut by reducible lits!");
}


static void
assert_peek_taut_lit_irreducible (QDPLL * qdpll, LitIDStack * lit_stack,
                                  Var * pivot, Var * taut_var)
{
  assert (!qdpll->options.long_dist_res);
  assert_peek_taut_lit_irreducible_aux (qdpll, taut_var, lit_stack->start,
                                        lit_stack->top);
  Constraint *antecedent = pivot->antecedent;
  assert (antecedent);
  assert_peek_taut_lit_irreducible_aux (qdpll, taut_var, antecedent->lits,
                                        antecedent->lits +
                                        antecedent->num_lits);
}


static void
assert_internal_vars_integrity (QDPLL *qdpll)
{
#ifndef NDEBUG
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          /* Assertion: a variable is internal iff it does NOT occur in the
             user-part of the variable table. */
          assert (p->is_internal || (p < qdpll->pcnf.vars + qdpll->pcnf.size_user_vars));
          assert (!(p < qdpll->pcnf.vars + qdpll->pcnf.size_user_vars) || !p->is_internal);
        }
    }
#endif
}

/* -------------------- END: ASSERTION-ONLY CODE -------------------- */


/* -------------------- START: TRACING-ONLY CODE -------------------- */

static void
encode_num (int num, int is_literal)
{
  unsigned char ch;
  unsigned int x = num;

  if (is_literal)
    x = num < 0 ? (-x << 1) | 1 : x << 1;

  while (x & ~0x7f)
    {
      ch = (x & 0x7f) | 0x80;
      putc (ch, stdout);
      x >>= 7;
    }
  ch = x;
  putc (ch, stdout);
}

static void
print_qrp_constraint (ConstraintID id, LitID * lits, unsigned int num_lits,
                      ConstraintID ant1, ConstraintID ant2)
{
  LitID *p;

  fprintf (stdout, "%u ", id);
  for (p = lits; p < lits + num_lits; p++)
    if (*p)                     /* skip deleted */
      fprintf (stdout, "%d ", *p);
  fprintf (stdout, "0 ");
  if (ant1)
    fprintf (stdout, "%u ", ant1);
  if (ant2)
    fprintf (stdout, "%u ", ant2);
  fprintf (stdout, "0\n");
}

static void
print_bqrp_constraint (ConstraintID id, LitID * lits, unsigned int num_lits,
                       ConstraintID ant1, ConstraintID ant2)
{
  LitID *p;

  encode_num (id, 0);
  for (p = lits; p < lits + num_lits; p++)
    if (*p)                     /* skip deleted */
      encode_num (*p, 1);
  encode_num (0, 0);
  if (ant1)
    encode_num (ant1, 0);
  if (ant2)
    encode_num (ant2, 0);
  encode_num (0, 0);
}


static void
print_qrp_full_cover_set (QDPLL * qdpll,
                          ConstraintID id,
                          LitID * inner_lits, unsigned int num_inner_lits,
                          LitID * lits, unsigned int num_lits)
{
  LitID *p;
  fprintf (stdout, "%u ", id);
  for (p = inner_lits; p < inner_lits + num_inner_lits; p++)
    {
      fprintf (stdout, "%d ", *p);
      /* existential lits of innermost scope -> reset mark */
      (LIT2VARPTR (qdpll->pcnf.vars, *p))->mark_qrp = 0;
    }
  for (p = lits; p < lits + num_lits; p++)
    fprintf (stdout, "%d ", *p);
  fprintf (stdout, "0 0\n");
}


static void
print_bqrp_full_cover_set (QDPLL * qdpll,
                           ConstraintID id,
                           LitID * inner_lits, unsigned int num_inner_lits,
                           LitID * lits, unsigned int num_lits)
{
  LitID *p;
  encode_num (id, 0);
  for (p = inner_lits; p < inner_lits + num_inner_lits; p++)
    {
      encode_num (*p, 1);
      /* existential lits of innermost scope -> reset mark */
      (LIT2VARPTR (qdpll->pcnf.vars, *p))->mark_qrp = 0;
    }
  for (p = lits; p < lits + num_lits; p++)
    encode_num (*p, 1);
  encode_num (0, 0);
  encode_num (0, 0);
}


static void
print_qrp_scope (Scope * scope)
{
  VarID *p;

  if (QDPLL_SCOPE_EXISTS (scope))
    fprintf (stdout, "e");
  else
    fprintf (stdout, "a");

  for (p = scope->vars.start; p < scope->vars.top; p++)
    fprintf (stdout, " %u", *p);
  fprintf (stdout, " 0\n");
}


static void
print_bqrp_scope (Scope * scope)
{
  VarID *p;

  encode_num (0, 0);
  if (QDPLL_SCOPE_EXISTS (scope))
    fprintf (stdout, "e");
  else
    fprintf (stdout, "a");

  for (p = scope->vars.start; p < scope->vars.top; p++)
    encode_num (*p, 0);
  encode_num (0, 0);
}

/* --------------------- END: TRACING-ONLY CODE --------------------- */



/* Get process time. Can be used for performance statistics. */
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


/* Compute 'literal block distance' of current constraint: partition
   literals into classes accroding to their decision level. Must treat
   unassigned literals separately. */
static unsigned int
compute_constraint_lbd (QDPLL * qdpll, Constraint * c)
{
  const unsigned int dec_level = qdpll->state.decision_level;
  assert (dec_level != QDPLL_INVALID_DECISION_LEVEL);
  char level_classes[dec_level + 2];
  memset (level_classes, 0, (dec_level + 2) * sizeof (char));
  unsigned int result = 0;
  Var *vars = qdpll->pcnf.vars;

  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      unsigned int pos =
        QDPLL_VAR_ASSIGNED (var) ? var->decision_level : dec_level + 1;
      assert (pos < dec_level + 2);
      level_classes[pos] = 1;
    }

  char *cp, *ce;
  for (cp = level_classes, ce = cp + dec_level + 2; cp < ce; cp++)
    if (*cp)
      result++;

  assert (result > 0);
  return result;
}


/* -------------------- START: VARIABLE PRIORITY-QUEUE -------------------- */

static void
var_pqueue_adjust (QDPLL * qdpll, unsigned int size)
{
  unsigned int old_size;

  if ((old_size = qdpll->size_var_pqueue) < size)
    {
      QDPLLMemMan *mm = qdpll->mm;
      qdpll->var_pqueue = qdpll_realloc (mm, qdpll->var_pqueue,
                                         old_size * sizeof (VarID),
                                         size * sizeof (VarID));
      qdpll->size_var_pqueue = size;
    }
}


static unsigned int
var_pqueue_get_left_child_pos (unsigned int cur_pos)
{
  assert (cur_pos != QDPLL_INVALID_PQUEUE_POS);
  return 2 * cur_pos + 1;
}


static unsigned int
var_pqueue_get_right_child_pos (unsigned int cur_pos)
{
  assert (cur_pos != QDPLL_INVALID_PQUEUE_POS);
  return 2 * (cur_pos + 1);
}


static unsigned int
var_pqueue_get_parent_pos (unsigned int cur_pos)
{
  assert (cur_pos != QDPLL_INVALID_PQUEUE_POS);
  unsigned int result;
  result = (cur_pos - 1) / 2;
  assert (cur_pos == var_pqueue_get_right_child_pos (result) ||
          cur_pos == var_pqueue_get_left_child_pos (result));
  return result;
}


static int
var_pqueue_compare (QDPLL * qdpll, unsigned int pos_a, unsigned int pos_b)
{
  assert (pos_a != QDPLL_INVALID_PQUEUE_POS);
  assert (pos_b != QDPLL_INVALID_PQUEUE_POS);
  assert (pos_a < qdpll->cnt_var_pqueue);
  assert (pos_b < qdpll->cnt_var_pqueue);

  unsigned int *var_pqueue = qdpll->var_pqueue;
  Var *vars = qdpll->pcnf.vars;
  assert (*(var_pqueue + pos_a) > 0);
  assert (*(var_pqueue + pos_b) > 0);
  Var *var_a = VARID2VARPTR (vars, *(var_pqueue + pos_a));
  Var *var_b = VARID2VARPTR (vars, *(var_pqueue + pos_b));

  double var_a_priority = var_a->priority;
  double var_b_priority = var_b->priority;

  if (var_a_priority < var_b_priority)
    return -1;
  else if (var_a_priority == var_b_priority)
    {
      assert (var_a->id != var_b->id);
      if (var_a->id < var_b->id)
        return -1;
      else
        return 1;
    }
  else
    return 1;
}


static void
var_pqueue_swap (QDPLL * qdpll, unsigned int pos_a, unsigned int pos_b)
{
  assert (pos_a != pos_b);
  assert (pos_a != QDPLL_INVALID_PQUEUE_POS);
  assert (pos_b != QDPLL_INVALID_PQUEUE_POS);
  assert (pos_a < qdpll->cnt_var_pqueue);
  assert (pos_b < qdpll->cnt_var_pqueue);

  VarID *var_pqueue = qdpll->var_pqueue;
  unsigned int tmp, *ptr_a, *ptr_b;

  ptr_a = var_pqueue + pos_a;
  tmp = *ptr_a;
  ptr_b = var_pqueue + pos_b;

  Var *vars = qdpll->pcnf.vars;
  assert (*ptr_a > 0);
  assert (*ptr_b > 0);
  Var *var_a = VARID2VARPTR (vars, *ptr_a);
  Var *var_b = VARID2VARPTR (vars, *ptr_b);

  assert (var_a->priority_pos == pos_a);
  assert (var_b->priority_pos == pos_b);

  *ptr_a = *ptr_b;
  var_b->priority_pos = pos_a;

  *ptr_b = tmp;
  var_a->priority_pos = pos_b;
}


static void
var_pqueue_up_heap (QDPLL * qdpll, unsigned int cur_pos)
{
  assert (cur_pos != QDPLL_INVALID_PQUEUE_POS);
  assert (cur_pos < qdpll->cnt_var_pqueue);

  while (cur_pos > 0)
    {
      unsigned int parent_pos = var_pqueue_get_parent_pos (cur_pos);

      if (var_pqueue_compare (qdpll, cur_pos, parent_pos) <= 0)
        break;

      var_pqueue_swap (qdpll, cur_pos, parent_pos);
      cur_pos = parent_pos;
    }
}


static void
var_pqueue_down_heap (QDPLL * qdpll, unsigned int cur_pos)
{
  assert (cur_pos != QDPLL_INVALID_PQUEUE_POS);
  assert (cur_pos < qdpll->cnt_var_pqueue);

  unsigned int child_pos, left_child_pos, right_child_pos;
  unsigned int count = qdpll->cnt_var_pqueue;

  for (;;)
    {
      left_child_pos = var_pqueue_get_left_child_pos (cur_pos);

      if (left_child_pos >= count)
        break;

      right_child_pos = var_pqueue_get_right_child_pos (cur_pos);

      if (right_child_pos < count &&
          var_pqueue_compare (qdpll, left_child_pos, right_child_pos) < 0)
        child_pos = right_child_pos;
      else
        child_pos = left_child_pos;

      if (var_pqueue_compare (qdpll, cur_pos, child_pos) < 0)
        {
          var_pqueue_swap (qdpll, cur_pos, child_pos);
          cur_pos = child_pos;
        }
      else
        break;
    }
}


static void
assert_var_pqueue_condition (QDPLL * qdpll)
{
  unsigned int *var_pqueue = qdpll->var_pqueue;
  unsigned int pos, no_children, left_child_pos, right_child_pos;
  Var *vars = qdpll->pcnf.vars;
  no_children = qdpll->cnt_var_pqueue / 2;

  for (pos = 0; pos < qdpll->cnt_var_pqueue; pos++)
    {
      unsigned int *cur, *left, *right;
      Var *cur_var, *left_var, *right_var;

      cur = var_pqueue + pos;
      assert (*cur > 0);
      cur_var = VARID2VARPTR (vars, *cur);
      assert (cur_var->priority_pos == pos);

      left_child_pos = var_pqueue_get_left_child_pos (pos);
      right_child_pos = var_pqueue_get_right_child_pos (pos);

      if (pos < no_children)
        {
          assert (left_child_pos < qdpll->cnt_var_pqueue);

          left = var_pqueue + left_child_pos;
          assert (*left > 0);
          left_var = VARID2VARPTR (vars, *left);
          assert (left_var->priority_pos == left_child_pos);

          if (right_child_pos < qdpll->cnt_var_pqueue)
            {
              right = var_pqueue + right_child_pos;
              assert (*right > 0);
              right_var = VARID2VARPTR (vars, *right);
              assert (right_var->priority_pos == right_child_pos);
            }

          assert (cur_var->priority >= left_var->priority);
          assert (right_child_pos >= qdpll->cnt_var_pqueue ||
                  cur_var->priority >= right_var->priority);
        }
      else                      /* has no children */
        {
          assert (right_child_pos >= qdpll->cnt_var_pqueue);
          assert (left_child_pos >= qdpll->cnt_var_pqueue);
        }
    }
}


static void
var_pqueue_increase_key (QDPLL * qdpll, VarID id)
{
  unsigned int cur_pos = VARID2VARPTR (qdpll->pcnf.vars, id)->priority_pos;
  var_pqueue_up_heap (qdpll, cur_pos);
#ifndef NDEBUG
#if QDPLL_PQ_ASSERT_HEAP_CONDITION_INCREASE_KEY
  assert_var_pqueue_condition (qdpll);
#endif
#endif
}


static void
var_pqueue_insert (QDPLL * qdpll, VarID id, double priority)
{
  assert (id > 0);
  unsigned int pos, cnt = qdpll->cnt_var_pqueue, size =
    qdpll->size_var_pqueue;
  pos = cnt;

  if (cnt == size)
    var_pqueue_adjust (qdpll, size ? 2 * size : 1);

  qdpll->var_pqueue[pos] = id;
  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);
  var->priority = priority;
  assert (var->priority_pos == QDPLL_INVALID_PQUEUE_POS);
  var->priority_pos = pos;
  cnt++;
  qdpll->cnt_var_pqueue = cnt;

  var_pqueue_up_heap (qdpll, pos);

#ifndef NDEBUG
#if QDPLL_PQ_ASSERT_HEAP_CONDITION_INSERT
  assert_var_pqueue_condition (qdpll);
#endif
#endif
}


/* Remove first element in constant time, e.g. for clearing queue.
   NOTE: destroys heap condition! */
static VarID
var_pqueue_remove_first (QDPLL * qdpll)
{
  Var *vars = qdpll->pcnf.vars;
  VarID *var_pqueue = qdpll->var_pqueue;
  VarID last, result = 0;
  unsigned int cnt = qdpll->cnt_var_pqueue;

  if (cnt == 0)
    return result;

  result = var_pqueue[0];
  assert (result > 0);
  Var *last_var, *result_var = VARID2VARPTR (vars, result);
  assert (result_var->priority_pos == 0);

  cnt--;
  last = var_pqueue[cnt];
  last_var = VARID2VARPTR (vars, last);
  var_pqueue[0] = last;
  assert (last_var->priority_pos == cnt);
  last_var->priority_pos = 0;
  result_var->priority_pos = QDPLL_INVALID_PQUEUE_POS;

  qdpll->cnt_var_pqueue = cnt;

  return result;
}


static VarID
var_pqueue_remove_min (QDPLL * qdpll)
{
  VarID result = 0;

  if (qdpll->cnt_var_pqueue == 0)
    return result;

  result = var_pqueue_remove_first (qdpll);

  if (qdpll->cnt_var_pqueue > 0)
    var_pqueue_down_heap (qdpll, 0);

#ifndef NDEBUG
#if QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN
  assert_var_pqueue_condition (qdpll);
#endif
#endif

  return result;
}


static VarID
var_pqueue_access_min (QDPLL * qdpll)
{
  VarID *var_pqueue = qdpll->var_pqueue;
  unsigned int cnt = qdpll->cnt_var_pqueue;

  if (cnt == 0)
    return 0;
  else
    {
      assert (var_pqueue[0] > 0);
      return var_pqueue[0];
    }
}


/* Removes elem at index 'remove_pos' and maintains heap condition. */
static VarID
var_pqueue_remove_elem (QDPLL * qdpll, unsigned int remove_pos)
{
  assert (remove_pos != QDPLL_INVALID_PQUEUE_POS);
  assert (remove_pos < qdpll->cnt_var_pqueue);

#ifndef NDEBUG
#if QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM
  assert_var_pqueue_condition (qdpll);
#endif
#endif

  VarID last_id, remove_id;
  unsigned int cnt = qdpll->cnt_var_pqueue;
  Var *last_var, *remove_var, *vars = qdpll->pcnf.vars;
  VarID *var_pqueue = qdpll->var_pqueue;
  VarID *remove_ptr = var_pqueue + remove_pos;

  remove_id = *remove_ptr;
  assert (remove_id > 0);
  remove_var = VARID2VARPTR (vars, remove_id);
  assert (remove_var->priority_pos == remove_pos);
  remove_var->priority_pos = QDPLL_INVALID_PQUEUE_POS;

  cnt--;
  last_id = var_pqueue[cnt];
  assert (last_id > 0);
  qdpll->cnt_var_pqueue = cnt;

  if (remove_pos != cnt)
    {
      *remove_ptr = last_id;
      last_var = VARID2VARPTR (vars, last_id);
      assert (last_var->priority_pos == cnt);
      last_var->priority_pos = remove_pos;
      var_pqueue_up_heap (qdpll, remove_pos);
      var_pqueue_down_heap (qdpll, remove_pos);
    }

#ifndef NDEBUG
#if QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM
  assert_var_pqueue_condition (qdpll);
#endif
#endif

  return remove_id;
}

/* -------------------- END: VARIABLE PRIORITY-QUEUE -------------------- */


static size_t
size_assigned_vars (QDPLL * qdpll)
{
  return qdpll->assigned_vars_end - qdpll->assigned_vars;
}


static size_t
count_assigned_vars (QDPLL * qdpll)
{
  return qdpll->assigned_vars_top - qdpll->assigned_vars;
}


static void
enlarge_assigned_vars (QDPLL * qdpll)
{
  size_t old_size = size_assigned_vars (qdpll);
  size_t old_count = count_assigned_vars (qdpll);
  assert (old_size == old_count);
  size_t old_bcp_index = qdpll->bcp_ptr - qdpll->assigned_vars;
  size_t old_old_bcp_index = qdpll->old_bcp_ptr - qdpll->assigned_vars;
  size_t new_size = old_size ? 2 * old_size : 1;
  qdpll->assigned_vars =
    (VarID *) qdpll_realloc (qdpll->mm, qdpll->assigned_vars,
                             old_size * sizeof (VarID),
                             new_size * sizeof (VarID));
  qdpll->assigned_vars_end = qdpll->assigned_vars + new_size;
  qdpll->assigned_vars_top = qdpll->assigned_vars + old_count;
  qdpll->bcp_ptr = qdpll->assigned_vars + old_bcp_index;
  qdpll->old_bcp_ptr = qdpll->assigned_vars + old_old_bcp_index;
}


static void
push_assigned_vars (QDPLL * qdpll, VarID id)
{
  if (qdpll->assigned_vars_top == qdpll->assigned_vars_end)
    enlarge_assigned_vars (qdpll);
  assert (qdpll->assigned_vars_top < qdpll->assigned_vars_end);
  assert (qdpll->assigned_vars <= qdpll->assigned_vars_top);

  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);
  assert (var->trail_pos == QDPLL_INVALID_TRAIL_POS);
  var->trail_pos = qdpll->assigned_vars_top - qdpll->assigned_vars;

  *(qdpll->assigned_vars_top++) = id;
}


/* -------------------- START: INEFFICIENT STATE CHECK -------------------- */

/* Be careful to handle conflicts detected by enqueued but not yet propagated assignments. */
static int
is_clause_empty (QDPLL * qdpll, Constraint * clause)
{
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;

  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      if (!QDPLL_VAR_ASSIGNED (var))
        {
          if (QDPLL_VAR_EXISTS (var))
            return 0;
        }
      else
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 0;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 0;
            }
        }
    }

  return 1;
}

static void
remove_clause_from_notify_list (QDPLL * qdpll, const int is_cube,
                                int lit_is_rwlit, LitID lit,
                                Constraint * clause);

static void
add_clause_to_notify_list (QDPLL * qdpll, const int is_cube, int lit_is_rwlit,
                           LitID lit, Var * var, BLitsOcc blit);

static void
update_blocking_literal (QDPLL * qdpll, Var * vars, BLitsOcc * blit_ptr,
                         Constraint * c, LitID disabling_lit,
                         Var * disabling_var, const int is_cube);

static LitID
is_clause_satisfied (QDPLL * qdpll, Constraint * clause)
{
  assert (clause);
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;

#if COMPUTE_STATS
  qdpll->stats.total_is_clause_sat_calls++;
#endif

  int init_watchers = 0;

  if (clause->num_lits > 1
      && clause->lwatcher_pos != QDPLL_INVALID_WATCHER_POS
      && clause->rwatcher_pos != QDPLL_INVALID_WATCHER_POS)
    {
      init_watchers = 1;
      assert (clause->lwatcher_pos < clause->num_lits);
      assert (clause->rwatcher_pos < clause->num_lits);
      /* Check if a watcher satisfies the clause already. */
      LitID wlit = *(clause->lits + clause->lwatcher_pos);
      Var *wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar))
            {
              assert (wvar->pos_notify_lit_watchers.start +
                      clause->offset_in_notify_list[0] <
                      wvar->pos_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->pos_notify_lit_watchers.start +
                                       clause->offset_in_notify_list[0],
                                       clause, wlit, wvar, 0);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return wlit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar))
            {
              assert (wvar->neg_notify_lit_watchers.start +
                      clause->offset_in_notify_list[0] <
                      wvar->neg_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->neg_notify_lit_watchers.start +
                                       clause->offset_in_notify_list[0],
                                       clause, wlit, wvar, 0);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return wlit;
            }
        }
      wlit = *(clause->lits + clause->rwatcher_pos);
      wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar))
            {
              assert (wvar->pos_notify_lit_watchers.start +
                      clause->offset_in_notify_list[1] <
                      wvar->pos_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->pos_notify_lit_watchers.start +
                                       clause->offset_in_notify_list[1],
                                       clause, wlit, wvar, 0);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return wlit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar))
            {
              assert (wvar->neg_notify_lit_watchers.start +
                      clause->offset_in_notify_list[1] <
                      wvar->neg_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->neg_notify_lit_watchers.start +
                                       clause->offset_in_notify_list[1],
                                       clause, wlit, wvar, 0);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return wlit;
            }
        }
    }

  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      if (QDPLL_LIT_NEG (lit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (var))
            {
              return lit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          if (QDPLL_VAR_ASSIGNED_TRUE (var))
            {
              return lit;
            }
        }
    }

  return 0;
}


/* Check if clause is satisfied by a propagated assignment. We use
   separate code here since the 'is_clause_satisfied' funtion is a
   hot-spot. */
static int
is_clause_satisfied_by_prop_var (QDPLL * qdpll, Constraint * clause)
{
  assert (clause);
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;

#if COMPUTE_STATS
  qdpll->stats.total_is_clause_sat_calls++;
#endif

  int init_watchers = 0;

  if (clause->num_lits > 1
      && clause->lwatcher_pos != QDPLL_INVALID_WATCHER_POS
      && clause->rwatcher_pos != QDPLL_INVALID_WATCHER_POS)
    {
      init_watchers = 1;
      assert (clause->lwatcher_pos < clause->num_lits);
      assert (clause->rwatcher_pos < clause->num_lits);
      /* Check if a watcher satisfies the clause already. */
      LitID wlit = *(clause->lits + clause->lwatcher_pos);
      Var *wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar)
              && QDPLL_VAR_MARKED_PROPAGATED (wvar))
            {
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return 1;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar)
              && QDPLL_VAR_MARKED_PROPAGATED (wvar))
            {
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return 1;
            }
        }
      wlit = *(clause->lits + clause->rwatcher_pos);
      wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar)
              && QDPLL_VAR_MARKED_PROPAGATED (wvar))
            {
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return 1;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar)
              && QDPLL_VAR_MARKED_PROPAGATED (wvar))
            {
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return 1;
            }
        }
    }

  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      if (QDPLL_LIT_NEG (lit))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (var)
              && QDPLL_VAR_MARKED_PROPAGATED (var))
            {
              return 1;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          if (QDPLL_VAR_ASSIGNED_TRUE (var)
              && QDPLL_VAR_MARKED_PROPAGATED (var))
            {
              return 1;
            }
        }
    }

  return 0;
}


/* Dual to 'is_clause_empty' */
static int
is_cube_satisfied (QDPLL * qdpll, Constraint * cube)
{
  assert (cube->is_cube);
  Var *vars = qdpll->pcnf.vars;

  LitID *p, *e;
  for (p = cube->lits, e = p + cube->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      /* Must check if all cube literals are both assigned and
         propagated. */

      if (!QDPLL_VAR_ASSIGNED (var))
        {
          if (QDPLL_VAR_FORALL (var))
            return 0;
        }
      else
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 0;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 0;
            }
        }
    }

  return 1;
}


/* Dual to 'is_clause_satisfied' */
static LitID
is_cube_empty (QDPLL * qdpll, Constraint * cube)
{
  assert (cube->is_cube);
  Var *vars = qdpll->pcnf.vars;

#if COMPUTE_STATS
  qdpll->stats.total_is_clause_sat_calls++;
#endif

  /* Check if a watcher satisfies the clause already. */
  LitID wlit;
  Var *wvar;

  if (cube->lwatcher_pos < cube->num_lits)
    {
      wlit = *(cube->lits + cube->lwatcher_pos);
      wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar))
            {
              assert (wvar->neg_notify_lit_watchers.start +
                      cube->offset_in_notify_list[0] <
                      wvar->neg_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->neg_notify_lit_watchers.start +
                                       cube->offset_in_notify_list[0],
                                       cube, wlit, wvar, 1);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return wlit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar))
            {
              assert (wvar->pos_notify_lit_watchers.start +
                      cube->offset_in_notify_list[0] <
                      wvar->pos_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->pos_notify_lit_watchers.start +
                                       cube->offset_in_notify_list[0],
                                       cube, wlit, wvar, 1);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_lw++;
#endif
              return wlit;
            }
        }
    }

  if (cube->rwatcher_pos < cube->num_lits)
    {
      wlit = *(cube->lits + cube->rwatcher_pos);
      wvar = LIT2VARPTR (vars, wlit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (wlit))
        {
          if (QDPLL_VAR_ASSIGNED_TRUE (wvar))
            {
              assert (wvar->neg_notify_lit_watchers.start +
                      cube->offset_in_notify_list[1] <
                      wvar->neg_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->neg_notify_lit_watchers.start +
                                       cube->offset_in_notify_list[1],
                                       cube, wlit, wvar, 1);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return wlit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (wlit));
          if (QDPLL_VAR_ASSIGNED_FALSE (wvar))
            {
              assert (wvar->pos_notify_lit_watchers.start +
                      cube->offset_in_notify_list[1] <
                      wvar->pos_notify_lit_watchers.top);
              /* Update blocking literal in left-watcher's notify list. */
              update_blocking_literal (qdpll, vars,
                                       wvar->pos_notify_lit_watchers.start +
                                       cube->offset_in_notify_list[1],
                                       cube, wlit, wvar, 1);
#if COMPUTE_STATS
              qdpll->stats.total_is_clause_sat_by_rw++;
#endif
              return wlit;
            }
        }
    }

  LitID *p, *e;
  for (p = cube->lits, e = p + cube->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

#if COMPUTE_STATS
      qdpll->stats.total_is_clause_sat_lit_visits++;
#endif

      if (QDPLL_LIT_NEG (lit))
        {
          if (QDPLL_VAR_ASSIGNED_TRUE (var))
            {
              return lit;
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          if (QDPLL_VAR_ASSIGNED_FALSE (var))
            {
              return lit;
            }
        }
    }

  return 0;
}


/* Returns unit universal literal or 0 if cube is not unit. */
static LitID
is_cube_unit (QDPLL * qdpll, Constraint * cube)
{
  assert (cube->is_cube);
  Var *vars = qdpll->pcnf.vars;
  /* Check literals from largest to smallest scope. */
  LitID *p, *e;
  for (e = cube->lits, p = e + cube->num_lits - 1; e <= p; p--)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      if (QDPLL_VAR_ASSIGNED (var))
        {
          /* Must check if cube literals are both assigned and
             propagated. */

          /* Detect false literals. */
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 0;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 0;
            }
        }
      else
        {
          assert (!QDPLL_VAR_ASSIGNED (var));
          /* Find largest unassigned universal literal... */
          if (QDPLL_SCOPE_FORALL (var->scope))
            {
              /* ...and check smaller literals. */
              LitID *p2;
              for (p2 = p - 1; e <= p2; p2--)
                {
                  LitID lit2 = *p2;
                  Var *var2 = LIT2VARPTR (vars, lit2);
                  if (QDPLL_VAR_ASSIGNED (var2))
                    {
                      /* Must check if all cube literals are both assigned and
                         propagated. */

                      /* Detect false literals. */
                      if (QDPLL_LIT_NEG (lit2))
                        {
                          if (QDPLL_VAR_ASSIGNED_TRUE (var2))
                            return 0;
                        }
                      else
                        {
                          assert (QDPLL_LIT_POS (lit2));
                          if (QDPLL_VAR_ASSIGNED_FALSE (var2))
                            return 0;
                        }
                    }
                  else
                    {
                      /* Found a second unassigned literal. */
                      assert (!QDPLL_VAR_ASSIGNED (var2));
                      return 0;
                    }
                }
              /* Did neither find a smaller unassigned literal nor a
                 false literal in the cube. */
              return lit;
            }
        }
    }
  return 0;
}


static int has_formula_empty_clause (QDPLL * qdpll);

static int has_constraint_spurious_pure_lit (QDPLL * qdpll, Constraint * c);


/* Check if formula has a satisfied cube. */
static int
has_formula_satisfied_cube (QDPLL * qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.learnt_cubes.first; c; c = c->link.next)
    {
      if (is_cube_satisfied (qdpll, c))
        {
          if (qdpll->options.no_spure_literals
              || !has_constraint_spurious_pure_lit (qdpll, c))
            return 1;
        }
    }
  return 0;
}


/* Check if formula has an empty clause. */
static int
has_formula_empty_clause (QDPLL * qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      if (c->qbcp_qbce_blocked)
        continue;
      if (is_clause_empty (qdpll, c))
        return 1;
    }
  for (c = qdpll->pcnf.learnt_clauses.first; c; c = c->link.next)
    {
      /* We never check if learned clauses are blocked. */
      assert (!c->qbcp_qbce_blocked);
      if (is_clause_empty (qdpll, c))
        {
          if (qdpll->options.no_spure_literals
              || !has_constraint_spurious_pure_lit (qdpll, c))
            return 1;
        }
    }
  return 0;
}


/* Check if all cubes in formula are empty. */
static int
all_cubes_empty (QDPLL * qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.learnt_cubes.first; c; c = c->link.next)
    {
      if (!is_cube_empty (qdpll, c))
        return 0;
    }
  return 1;
}


/* Check if all clauses in formula are satisfied. */
static int
all_clauses_satisfied (QDPLL * qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      if (c->qbcp_qbce_blocked)
        continue;
      if (!is_clause_satisfied (qdpll, c))
        return 0;
    }
  for (c = qdpll->pcnf.learnt_clauses.first; c; c = c->link.next)
    {
      if ((!qdpll->options.qbce_preprocessing && !qdpll->options.qbce_inprocessing &&  
           qdpll->options.no_qbce_dynamic) || qdpll->options.qbce_inprocessing)
        {
          if (!is_clause_satisfied (qdpll, c)
              && (qdpll->options.no_spure_literals
                  || !has_constraint_spurious_pure_lit (qdpll, c)))
            return 0;
        }
      else
        {
          if (is_clause_empty (qdpll, c) && 
              (qdpll->options.no_spure_literals
               || !has_constraint_spurious_pure_lit (qdpll, c)))
            return 0;
        }
    }
  return 1;
}


/* Checks if empty clause in formula. */
static int
is_formula_false (QDPLL * qdpll)
{
  int has_empty_clause = has_formula_empty_clause (qdpll);

  if (qdpll->result_constraint && qdpll->result_constraint->is_cube)
    {
      assert (is_cube_satisfied (qdpll, qdpll->result_constraint));
      /* Fix the assertion-problem described above. */
      return 0;
    }

  if (has_empty_clause
      && (1 || qdpll->options.no_sdcl || all_cubes_empty (qdpll)))
    {
      return 1;
    }
  return 0;
}


/* Checks if all clauses are satisfied. */
static int
is_formula_true (QDPLL * qdpll)
{
  if (!qdpll->options.no_sdcl)
    {
      if (has_formula_satisfied_cube (qdpll))
        {
          return 1;
        }
    }
  if (all_clauses_satisfied (qdpll))
    return 1;
  return 0;
}


static QDPLLSolverState
determine_solver_state (QDPLL * qdpll)
{
  if (is_formula_false (qdpll))
    return QDPLL_SOLVER_STATE_UNSAT;
  else if (is_formula_true (qdpll))
    return QDPLL_SOLVER_STATE_SAT;
  else
    return QDPLL_SOLVER_STATE_UNDEF;
}


/* -------------------- END: INEFFICIENT STATE CHECK -------------------- */


/* -------------------- START: CLAUSE WATCHING -------------------- */


/* Delete signed 'id' from notify-list in constant time. Variable
   'owner' owns the lists 'notify_list' and
   'offset_in_watched_clause'. */
static void
remove_id_from_notify_list (Var * vars, Var * owner, LitIDStack * notify_list,
                            VarIDStack * offset_in_watched_clause,
                            VarID del_pos, LitID signed_id)
{
  assert (signed_id != 0);
  assert (count_in_notify_clause_watcher_list (notify_list, signed_id) == 1);
  assert (QDPLL_COUNT_STACK (*notify_list) ==
          QDPLL_COUNT_STACK (*offset_in_watched_clause));
  assert (del_pos < QDPLL_COUNT_STACK (*notify_list));

  /* Delete notify-list entry by overwriting with last element.
     Must also copy entry in offset-in-watcher list. */

  LitID last = QDPLL_POP_STACK (*notify_list);
  VarID last_offset = QDPLL_POP_STACK (*offset_in_watched_clause);

  if (QDPLL_COUNT_STACK (*notify_list) == 0)
    {
      /* Stacks are empty now. */
      assert (del_pos == 0);
      assert (QDPLL_COUNT_STACK (*offset_in_watched_clause) == 0);
      assert (count_in_notify_clause_watcher_list (notify_list, signed_id) ==
              0);
      return;
    }

  notify_list->start[del_pos] = last;
  offset_in_watched_clause->start[del_pos] = last_offset;

  /* Finally, since the offset of 'last' in the notify-list changed,
     we must also update its stored offset in 'offset_in_notify_list'. */
  Var *last_var = LIT2VARPTR (vars, last);
  VarIDStack *other_offset_in_notify_list = last < 0 ?
    &(last_var->neg_offset_in_notify_list) : &(last_var->
                                               pos_offset_in_notify_list);

  other_offset_in_notify_list->start[last_offset] = del_pos;

  assert (count_in_notify_clause_watcher_list (notify_list, signed_id) == 0);
}


static LitID
is_constraint_empty_watcher (QDPLL * qdpll, Constraint * c)
{
  LitID disable_witness;
  if (!c->is_cube)
    disable_witness = is_clause_satisfied (qdpll, c);
  else
    disable_witness = is_cube_empty (qdpll, c);

  return disable_witness;
}


/* Remove signed 'id' from notify-lists of variables in old watched clause.
   Watched clause is watched by variable 'id' and is satisfied now.
*/
static void
remove_watching_var_from_notify_lists (QDPLL * qdpll, LitID signed_id,
                                       Constraint * watched_clause)
{
  assert (watched_clause->is_watched);
  watched_clause->is_watched--;
  assert (watched_clause->is_cube
          || !is_clause_empty (qdpll, watched_clause));
  assert (!watched_clause->is_cube
          || !is_cube_satisfied (qdpll, watched_clause));
  assert (watched_clause->qbcp_qbce_blocked || 
          is_constraint_empty_watcher (qdpll, watched_clause));
  assert (signed_id != 0);
  Var *vars = qdpll->pcnf.vars;
  VarID id = signed_id < 0 ? -signed_id : signed_id;

  LitID *p, *e;
  VarIDStack *offset_in_notify_list = signed_id < 0 ?
    &(VARID2VARPTR (vars, id)->neg_offset_in_notify_list) :
    &(VARID2VARPTR (vars, id)->pos_offset_in_notify_list);
  assert (QDPLL_COUNT_STACK (*offset_in_notify_list) ==
          watched_clause->num_lits);
  VarID *del_pos_ptr = offset_in_notify_list->start;
  for (p = watched_clause->lits, e = p + watched_clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      assert (lit != 0);
      assert (lit != -signed_id);
      Var *v = LIT2VARPTR (vars, lit);

      VarIDStack *offset_in_watched_clause;
      LitIDStack *notify_list;
      if (QDPLL_LIT_NEG (lit))
        {
          if (!watched_clause->is_cube)
            {
              offset_in_watched_clause = &(v->neg_offset_in_watched_clause);
              notify_list = &(v->neg_notify_clause_watchers);
            }
          else
            {
              offset_in_watched_clause = &(v->pos_offset_in_watched_clause);
              notify_list = &(v->pos_notify_clause_watchers);
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          if (!watched_clause->is_cube)
            {
              offset_in_watched_clause = &(v->pos_offset_in_watched_clause);
              notify_list = &(v->pos_notify_clause_watchers);
            }
          else
            {
              offset_in_watched_clause = &(v->neg_offset_in_watched_clause);
              notify_list = &(v->neg_notify_clause_watchers);
            }
        }

      if (v->id != id)
        {
          assert (notify_list->start[*del_pos_ptr] == signed_id);
          remove_id_from_notify_list (vars, v, notify_list,
                                      offset_in_watched_clause,
                                      *del_pos_ptr, signed_id);
        }
      del_pos_ptr++;
    }
  /* Must clear the offset list, since this is needed for the new watcher then. */
  QDPLL_RESET_STACK (*offset_in_notify_list);
}


/* Add signed 'id' to notify-lists of variables in new watched clause.
   Sign of ID indicates which watcher to update for var 'id' after notification.
   Watched clause is now watched by variable 'id'.
*/
static void
add_watching_var_to_notify_lists (QDPLL * qdpll, LitID signed_id,
                                  Constraint * watched_clause)
{
  watched_clause->is_watched++;
  assert (watched_clause->is_watched <= watched_clause->num_lits);
  assert (signed_id != 0);
  assert (constraint_has_lit (watched_clause, signed_id));
  assert (!watched_clause->qbcp_qbce_blocked);
  Var *vars = qdpll->pcnf.vars;
  VarID id = QDPLL_LIT_NEG (signed_id) ? -signed_id : signed_id;
  QDPLLMemMan *mm = qdpll->mm;

  VarID offset = 0;
  VarIDStack *offset_in_notify_list = QDPLL_LIT_NEG (signed_id) ?
    &(VARID2VARPTR (vars, id)->neg_offset_in_notify_list) :
    &(VARID2VARPTR (vars, id)->pos_offset_in_notify_list);
  assert (QDPLL_COUNT_STACK (*offset_in_notify_list) == 0);

  LitID *p, *e;
  for (p = watched_clause->lits, e = p + watched_clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      assert (lit != 0);
      assert (lit != -signed_id);
      Var *v = LIT2VARPTR (vars, lit);

      if (v->id != id)
        {
          VarIDStack *offset_in_watched_clause;
          LitIDStack *notify_list;
          if (QDPLL_LIT_NEG (lit))
            {
              if (!watched_clause->is_cube)
                {
                  offset_in_watched_clause =
                    &(v->neg_offset_in_watched_clause);
                  notify_list = &(v->neg_notify_clause_watchers);
                }
              else
                {
                  offset_in_watched_clause =
                    &(v->pos_offset_in_watched_clause);
                  notify_list = &(v->pos_notify_clause_watchers);
                }
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (!watched_clause->is_cube)
                {
                  offset_in_watched_clause =
                    &(v->pos_offset_in_watched_clause);
                  notify_list = &(v->pos_notify_clause_watchers);
                }
              else
                {
                  offset_in_watched_clause =
                    &(v->neg_offset_in_watched_clause);
                  notify_list = &(v->neg_notify_clause_watchers);
                }
            }

          assert (count_in_notify_clause_watcher_list
                  (notify_list, signed_id) == 0);
          /* Store offsets. */
          QDPLL_PUSH_STACK (mm, *offset_in_notify_list,
                            QDPLL_COUNT_STACK (*notify_list));
          QDPLL_PUSH_STACK (mm, *offset_in_watched_clause, offset);
          QDPLL_PUSH_STACK (mm, *notify_list, signed_id);
          assert (count_in_notify_clause_watcher_list
                  (notify_list, signed_id) == 1);
        }
      else                      /* Push dummy entry. */
        QDPLL_PUSH_STACK (mm, *offset_in_notify_list, 0);
      offset++;
    }
  assert (QDPLL_COUNT_STACK (*offset_in_notify_list) ==
          watched_clause->num_lits);
}


static void
set_new_watcher (QDPLL * qdpll, LitID signed_id, BLitsOccStack * occ_list,
                 BLitsOcc * new_watcher)
{
  assert (signed_id != 0);
  /* Watched clause always occurs first on list. */
  BLitsOcc tmp = *new_watcher;
  *new_watcher = occ_list->start[0];
  occ_list->start[0] = tmp;

  /* Add watching variable's ID to notify-lists of variable in watched clause. */
  add_watching_var_to_notify_lists (qdpll, signed_id,
                                    BLIT_STRIP_PTR (tmp.constraint));
}


static Constraint *check_disabling_blocking_lit (QDPLL * qdpll,
                                                 BLitsOcc blit_occ,
                                                 const int
                                                 called_on_pure_lits);

/* Traverse the occurrence stack beginning from start position
   and search a new, unsatisfied clause to watch. 
   The new watcher is then copied to the first position (invariant).
   Returns new watcher if found, else null.
   NOTE: we use 'init' flag to use this function both for watcher
   update and watcher initialization.  
   NOTE: 'occ_list' is the list where we search for a new watcher,
   'old_watcher_list' contains the old (now empty) watcher, which can
   be equal to 'occ_list'. */
static Constraint *
find_and_set_new_watcher (QDPLL * qdpll, LitID lit, BLitsOccStack * occ_list,
                          BLitsOccStack * old_watcher_list, const int init)
{
#if COMPUTE_STATS
  qdpll->stats.total_clause_watcher_find_calls++;
#endif

  Var *vars = qdpll->pcnf.vars;
  BLitsOcc *bp, *be;
  bp = occ_list->start;
  be = occ_list->top;
  /* Start search at second element. */
  if (!init && occ_list == old_watcher_list)
    bp++;
  for (; bp < be; bp++)
    {
      Constraint *c = check_disabling_blocking_lit (qdpll, *bp, 1);
      if (!c)
        continue;
      if (c->qbcp_qbce_blocked)
        continue;

#if COMPUTE_STATS
      qdpll->stats.total_clause_watcher_find_clause_visits++;
      if (c->learnt)
        qdpll->stats.total_clause_watcher_find_learnt_clause_visits++;
#endif

      LitID disabling_lit;
      if (!(disabling_lit = is_constraint_empty_watcher (qdpll, c)))
        {
          /* We have found a new watcher. */
          if (!init)
            remove_watching_var_from_notify_lists (qdpll, lit,
                                                   BLIT_STRIP_PTR
                                                   (old_watcher_list->
                                                    start[0].constraint));
          set_new_watcher (qdpll, lit, occ_list, bp);
          return c;
        }
      else
        update_blocking_literal (qdpll, vars, bp,
                                 c, disabling_lit, LIT2VARPTR (vars,
                                                               disabling_lit),
                                 c->is_cube);
    }

  return 0;
}

/* Toggle marks of variables to indicate occurrences in watched clause; 
   value == 0 means resetting of marks to 0, value == 1 means setting marks to 1. */
static void
update_empty_formula_watcher_toggle_var_marks (QDPLL *qdpll, 
                                               BLitsOcc *watched_blit, 
                                               const unsigned int value)
{
  assert (value == 0 || value == 1);
  if (!watched_blit)
    return;
  Constraint *watched_clause = watched_blit->constraint;
  LitID *p, *e;
  for (p = watched_clause->lits, e = p + watched_clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      assert (!var->empty_formula_watcher_neg_occ || 
              !var->empty_formula_watcher_pos_occ);
      if (QDPLL_LIT_NEG (lit))
        {
          assert (value || var->empty_formula_watcher_neg_occ);
          assert (!value || !var->empty_formula_watcher_neg_occ);
          var->empty_formula_watcher_neg_occ = value;
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          assert (value || var->empty_formula_watcher_pos_occ);
          assert (!value || !var->empty_formula_watcher_pos_occ);
          var->empty_formula_watcher_pos_occ = value;
        }
    }
}

/* For assertion checking only: returns non-zero iff the constraint 'c' has
   ALL of its literals assigned as assumptions. */
static int
assert_all_assigned_assumption_lits_clause (QDPLL *qdpll, Constraint *c)
{
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      if (!QDPLL_VAR_ASSIGNED (var) || var->mode != QDPLL_VARMODE_ASSUMED)
        return 0;
    }
  return 1;
}

/* Returns zero iff the formula is currently empty. */
static BLitsOcc *
update_empty_formula_watcher (QDPLL *qdpll)
{
  BLitsOcc *cur_watcher_p = qdpll->empty_formula_watcher;
  assert (!cur_watcher_p || cur_watcher_p->constraint->qbcp_qbce_blocked || 
          !is_clause_empty (qdpll, cur_watcher_p->constraint));
#if COMPUTE_STATS
  qdpll->stats.empty_formula_watcher_total_update_calls++;
#endif
  if (!qdpll->state.empty_formula_watcher_scheduled_update)
    {
      /* If no update is scheduled, then the current watched clause is still
         unsatisfied and non-blocked under the current assignment. */
      assert (cur_watcher_p || qdpll->pcnf.clauses.cnt == 0);
      assert (!cur_watcher_p || !cur_watcher_p->constraint->qbcp_qbce_blocked);
      assert (!cur_watcher_p || !is_clause_satisfied (qdpll, cur_watcher_p->constraint));
      return cur_watcher_p;
    }
#if COMPUTE_STATS
  qdpll->stats.empty_formula_watcher_effective_update_calls++;
#endif

  qdpll->state.empty_formula_watcher_scheduled_update = 0;

  if (!cur_watcher_p)
    cur_watcher_p = qdpll->empty_formula_watching_blit_occs.start;

  assert (qdpll->pcnf.clauses.cnt == 
          (unsigned int) QDPLL_COUNT_STACK (qdpll->empty_formula_watching_blit_occs));
  assert (cur_watcher_p <= qdpll->empty_formula_watching_blit_occs.top);
  assert (qdpll->empty_formula_watching_blit_occs.start <= cur_watcher_p);

  BLitsOcc *e = qdpll->empty_formula_watching_blit_occs.top;
  for (; cur_watcher_p < e; cur_watcher_p++)
    {
#if COMPUTE_STATS
      if (cur_watcher_p->blit)
        qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses++;
#endif
      /* This branch should save calls of 'is_clause_satisfied'. */
      /* Must handle empty input clauses. */
      assert (cur_watcher_p->blit || cur_watcher_p->constraint->num_lits == 0);
      Constraint *cur_watcher = cur_watcher_p->blit ?
        check_disabling_blocking_lit (qdpll, *cur_watcher_p, 0) : cur_watcher_p->constraint;
          /* Check if clause is satisfied by cached literal. */
          if (!cur_watcher)
            {
#if COMPUTE_STATS
              qdpll->stats.empty_formula_watcher_is_clause_sat_cache_hits++;
#endif
              continue;
            }
          else
            {
              /* We must detect conflicts first. We may encounter
                 syntactically empty input clauses if this function is called
                 from 'set_up_watchers'. In incremental solving, empty input
                 clauses have one selector literal. Conflict will be found
                 during literal watcher initialization then. 
                 Further, we may have conflict due to user-given
                 assumptions. In this case, we watch that clause although
                 conflict will be found later. */
              assert (cur_watcher->num_lits == 0 || 
                      (cur_watcher->num_lits == 1 && 
                       (LIT2VARPTR(qdpll->pcnf.vars, cur_watcher->lits[0])->is_internal)) ||  
                      cur_watcher->qbcp_qbce_blocked || 
                      !is_clause_empty (qdpll, cur_watcher) || 
                      assert_all_assigned_assumption_lits_clause (qdpll, cur_watcher));
              if (cur_watcher->qbcp_qbce_blocked)
                {
#if COMPUTE_STATS
                  qdpll->stats.empty_formula_watcher_is_clause_sat_found_blocked++;
#endif
                  continue;
                }
              LitID satisfying_lit;
              if ((satisfying_lit = is_constraint_empty_watcher (qdpll, cur_watcher)))
                {
#if COMPUTE_STATS
                  qdpll->stats.empty_formula_watcher_is_clause_sat_found_sat++;
#endif
                  update_blocking_literal (qdpll, qdpll->pcnf.vars, cur_watcher_p,
                                 cur_watcher, satisfying_lit, LIT2VARPTR (qdpll->pcnf.vars,
                                                               satisfying_lit),
                         cur_watcher->is_cube);
                  continue;
                }
              else
                {
                  /* Clause is neither satisfied nor blocked. */
                  break;
                }
            }
    }

  /* Reset marks of variables appearing in old watched clause. */
  update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 0);
  qdpll->empty_formula_watcher = cur_watcher_p < e ? cur_watcher_p : 0;
  /* Set marks of variables appearing in new watched clause. */
  update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 1);
  return qdpll->empty_formula_watcher;
}

static int
notify_clause_watching_variables_aux (QDPLL * qdpll, LitID signed_id, Var *v)
{
  BLitsOccStack *occs, *next_occs;
  QDPLLAssignment pure_value;
  if (QDPLL_LIT_NEG (signed_id))
    {
      pure_value = QDPLL_SCOPE_EXISTS (v->scope) ?
        QDPLL_ASSIGNMENT_TRUE : QDPLL_ASSIGNMENT_FALSE;
      /* Must find new neg-occ watcher. */
      if (v->mark_is_neg_watching_cube)
        {
          /* First search neg-occ cubes, then neg-occ clauses. */
          assert (is_cube_empty
                  (qdpll,
                   BLIT_STRIP_PTR (v->neg_occ_cubes.start[0].
                                   constraint)));
          occs = &(v->neg_occ_cubes);
          next_occs = &(v->neg_occ_clauses);
        }
      else
        {
          /* First search neg-occ clauses, then neg-occ cubes. */
          assert (BLIT_STRIP_PTR (v->neg_occ_clauses.start[0].
                                   constraint)->qbcp_qbce_blocked || 
                  is_clause_satisfied
                  (qdpll,
                   BLIT_STRIP_PTR (v->neg_occ_clauses.start[0].
                                   constraint)));
          occs = &(v->neg_occ_clauses);
          next_occs = &(v->neg_occ_cubes);
        }
    }
  else
    {
      assert (QDPLL_LIT_POS (signed_id));
      pure_value = QDPLL_SCOPE_EXISTS (v->scope) ?
        QDPLL_ASSIGNMENT_FALSE : QDPLL_ASSIGNMENT_TRUE;
      /* Must find new pos-occ watcher. */
      if (v->mark_is_pos_watching_cube)
        {
          /* First search pos-occ cubes, then pos-occ clauses. */
          assert (is_cube_empty
                  (qdpll,
                   BLIT_STRIP_PTR (v->pos_occ_cubes.start[0].
                                   constraint)));
          occs = &(v->pos_occ_cubes);
          next_occs = &(v->pos_occ_clauses);
        }
      else
        {
          /* First search pos-occ clauses, then pos-occ cubes. */
          assert (BLIT_STRIP_PTR (v->pos_occ_clauses.start[0].
                                   constraint)->qbcp_qbce_blocked || 
                  is_clause_satisfied
                  (qdpll,
                   BLIT_STRIP_PTR (v->pos_occ_clauses.start[0].
                                   constraint)));
          occs = &(v->pos_occ_clauses);
          next_occs = &(v->pos_occ_cubes);
        }
    }

  Constraint *new_in_occs = 0, *new_in_next_occs = 0;
  if (!(new_in_occs =
        find_and_set_new_watcher (qdpll, signed_id, occs, occs, 0)) &&
      !(new_in_next_occs =
        find_and_set_new_watcher (qdpll, signed_id, next_occs, occs, 0)))
    {
      assert (!new_in_occs && !new_in_next_occs);
      /* Variable has no active occurrences left -> is pure. */
      push_assigned_variable (qdpll, v, pure_value, QDPLL_VARMODE_PURE);
    }
  else
    {
      assert (new_in_occs || new_in_next_occs);
      /* Invert flag to indicate that we found a new
         watcher in the other occ-list. */
      if (!new_in_occs)
        {
          assert (new_in_next_occs);
          if (QDPLL_LIT_NEG (signed_id))
            v->mark_is_neg_watching_cube = !v->mark_is_neg_watching_cube;
          else
            v->mark_is_pos_watching_cube = !v->mark_is_pos_watching_cube;
        }
      return 1;
    }
  return 0;
}

/* Notify clause-watching variables to find new watcher after assignment. */
static void
notify_clause_watching_variables (QDPLL * qdpll, LitIDStack * notify_list)
{
  Var *vars = qdpll->pcnf.vars, *v;
  LitID *p, *e;
  for (p = notify_list->start, e = notify_list->top; p < e; p++)
    {
      assert (*p != 0);
      LitID signed_id = *p;
      v = LIT2VARPTR (vars, signed_id);

      if (QDPLL_VAR_ASSIGNED (v))
        continue;

#ifndef NDEBUG
  LitID *old_top = notify_list->top;
#endif
      if (notify_clause_watching_variables_aux (qdpll, signed_id, v))
        {
          /* New watcher was set. */
#ifndef NDEBUG
          assert (old_top == notify_list->top + 1);
#endif
          /* Entry has been removed from list being traversed. */
          e--;
          p--;
          /* Must check 'new' element which was copied there. */
        }
    }
}


/* Find clause watchers for each variable.
   This is only for initialization before solver starts. */
static void
init_clause_watchers (QDPLL * qdpll)
{
  assert (qdpll->state.decision_level == 0);
  Var *vars = qdpll->pcnf.vars;

  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      VarID *p, *e;
      for (p = s->vars.start, e = s->vars.top; p < e; p++)
        {
          assert (*p > 0 && *p < qdpll->pcnf.size_vars);
          Var *v = VARID2VARPTR (vars, *p);
          assert (!v->mark_is_neg_watching_cube);
          assert (!v->mark_is_pos_watching_cube);

          if (QDPLL_VAR_ASSIGNED (v))
            {
              assert (v->decision_level == 0);
              continue;
            }

          Constraint *watcher;

          if ((watcher =
               find_and_set_new_watcher (qdpll, -v->id, &(v->neg_occ_clauses),
                                         &(v->neg_occ_clauses), 1)) ||
              ((qdpll->options.no_spure_literals) &&
               (watcher =
                find_and_set_new_watcher (qdpll, -v->id, &(v->neg_occ_cubes),
                                          &(v->neg_occ_cubes), 1))))
            {
              if (watcher->is_cube)
                v->mark_is_neg_watching_cube = 1;
            }
          else
            {                   /* Pure literal detected: variable has no negative occurrences. */
              assert (!QDPLL_VAR_ASSIGNED (v));
              if (QDPLL_VAR_EXISTS (v))
                {
                  push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_TRUE,
                                          QDPLL_VARMODE_PURE);
                }
              else
                {
                  push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_FALSE,
                                          QDPLL_VARMODE_PURE);
                }
              /* 'continue' here because: other watcher can not be set
                 since now all clauses implicitly satisfied. And we must
                 not enqueue two assignments. */
              continue;
            }

          if ((watcher =
               find_and_set_new_watcher (qdpll, v->id, &(v->pos_occ_clauses),
                                         &(v->pos_occ_clauses), 1)) ||
              ((qdpll->options.no_spure_literals) &&
               (watcher =
                find_and_set_new_watcher (qdpll, v->id, &(v->pos_occ_cubes),
                                          &(v->pos_occ_cubes), 1))))
            {
              if (watcher->is_cube)
                v->mark_is_pos_watching_cube = 1;
            }
          else
            {                   /* Pure literal detected: variable has no positive occurrences. */
              assert (!QDPLL_VAR_ASSIGNED (v));
              if (QDPLL_VAR_EXISTS (v))
                {
                  push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_FALSE,
                                          QDPLL_VARMODE_PURE);
                }
              else
                {
                  push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_TRUE,
                                          QDPLL_VARMODE_PURE);
                }
            }
        }
    }
}

/* -------------------- END: CLAUSE WATCHING -------------------- */


/* -------------------- START: LITERAL WATCHING -------------------- */

/* 'blit_ptr' points to a blocking-lit-object of constraint 'c'. */
static void
update_blocking_literal (QDPLL * qdpll, Var * vars, BLitsOcc * blit_ptr,
                         Constraint * c, LitID disabling_lit,
                         Var * disabling_var, const int is_cube)
{
  assert (((QDPLL_LIT_NEG (disabling_lit) &&
            ((!is_cube && QDPLL_VAR_ASSIGNED_FALSE (disabling_var)) ||
             (is_cube && QDPLL_VAR_ASSIGNED_TRUE (disabling_var)))) ||
           (QDPLL_LIT_POS (disabling_lit) &&
            ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (disabling_var)) ||
             (is_cube && QDPLL_VAR_ASSIGNED_FALSE (disabling_var))))));
  assert (LIT2VARPTR (vars, disabling_lit) == disabling_var);
#if COMPUTE_STATS
  qdpll->stats.blits_update_calls++;
#endif
  assert (!BLIT_MARKED_PTR (c));
  assert (c == BLIT_STRIP_PTR (blit_ptr->constraint));
  assert (blit_ptr->blit);
  assert (blit_ptr->constraint);
  LitID cur_blit = blit_ptr->blit;
  Var *cur_bvar = LIT2VARPTR (vars, cur_blit);
  int cur_non_disabling = ((QDPLL_LIT_NEG (cur_blit) &&
                            ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (cur_bvar))
                             || (is_cube
                                 && QDPLL_VAR_ASSIGNED_FALSE (cur_bvar))))
                           || (QDPLL_LIT_POS (cur_blit)
                               &&
                               ((!is_cube
                                 && QDPLL_VAR_ASSIGNED_FALSE (cur_bvar))
                                || (is_cube
                                    && QDPLL_VAR_ASSIGNED_TRUE (cur_bvar)))));
  /* Set blocking literal only if cur. blocking literal is unassigned,
     assigned but non-disabling or assigned disabling but at higher
     level -> want to keep "good" blocking literals. */
  if (!QDPLL_VAR_ASSIGNED (cur_bvar) || cur_non_disabling ||
      cur_bvar->decision_level > disabling_var->decision_level)
    {
#if COMPUTE_STATS
      qdpll->stats.blits_update_done++;
#endif
      blit_ptr->blit = disabling_lit;
    }
}


/* Traverse clause's literals between 'right' and 'left' and search unassigned 
   literal of specified type. If a true literal is found, then value 'QDPLL_WATCHER_SAT' is returned.
*/
static unsigned int
find_watcher_pos (QDPLL * qdpll, const int is_cube, Var * vars,
                  Constraint * c, LitID * right, LitID * left,
                  const QDPLLQuantifierType qtype, BLitsOcc * blit_ptr)
{
  assert (!BLIT_MARKED_PTR (c));
#if COMPUTE_STATS
  qdpll->stats.total_lit_watcher_find_calls++;
#endif
  Var *oldw = 0;
  QDPLLQuantifierType oldw_type = QDPLL_QTYPE_UNDEF;
  if (qtype == QDPLL_QTYPE_UNDEF)
    {
      /* Only when searching new left watcher. */
      oldw = LIT2VARPTR (qdpll->pcnf.vars, *(right + 1));
      oldw_type = oldw->scope->type;
      assert (!is_cube || oldw_type == QDPLL_QTYPE_FORALL);
      assert (is_cube || oldw_type == QDPLL_QTYPE_EXISTS);
    }

  for (; right >= left; right--)
    {
      assert (right >= c->lits);

#if COMPUTE_STATS
      qdpll->stats.total_lit_watcher_find_lit_visits++;
#endif

      LitID lit = *right;
      assert (lit != 0);
      Var *var = LIT2VARPTR (vars, lit);
      if (!QDPLL_VAR_ASSIGNED (var))
        {
          /* Literal unassigned. */
          if (qtype == QDPLL_QTYPE_UNDEF || qtype == var->scope->type)
            {
#if COMPUTE_STATS
              qdpll->stats.total_lwatched++;
#endif
              if (qtype == QDPLL_QTYPE_UNDEF
                  && oldw_type != var->scope->type
                  && qdpll->dm->is_init (qdpll->dm))
                {
#if COMPUTE_STATS
                  qdpll->stats.total_lwatched_tested++;
#endif
                  if (!qdpll->dm->depends (qdpll->dm, var->id, oldw->id))
                    {
#if COMPUTE_STATS
                      qdpll->stats.non_dep_lwatched_skipped++;
#endif
                      continue;
                    }
                }
              return right - c->lits;
            }
        }
      else
        {
          /* Check if assigned literal satisfies clause / falsifies cube. */
          if (QDPLL_LIT_NEG (lit))
            {
              if ((!is_cube && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
                  (is_cube && QDPLL_VAR_ASSIGNED_TRUE (var)))
                {
                  update_blocking_literal (qdpll, vars, blit_ptr, c, lit, var,
                                           is_cube);
                  return QDPLL_WATCHER_SAT;
                }
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (var)) ||
                  (is_cube && QDPLL_VAR_ASSIGNED_FALSE (var)))
                {
                  update_blocking_literal (qdpll, vars, blit_ptr, c, lit, var,
                                           is_cube);
                  return QDPLL_WATCHER_SAT;
                }
            }
        }
    }

  return QDPLL_INVALID_WATCHER_POS;
}


/* Delete the 'clause' from the literal's notify-list. Parameter
   'lit_is_rwlit' indicates if 'lit' is the literal of the right or left
   watcher. This avoids retrieving the watcher list again from the clause. */
static void
remove_clause_from_notify_list (QDPLL * qdpll, const int is_cube,
                                int lit_is_rwlit, LitID lit,
                                Constraint * clause)
{
  assert (!BLIT_MARKED_PTR (clause));
  Var *vars = qdpll->pcnf.vars;
  Var *var = LIT2VARPTR (vars, lit);
  BLitsOccStack *notify_list;
  if (QDPLL_LIT_NEG (lit))
    {
      if (!is_cube)
        notify_list = &(var->pos_notify_lit_watchers);
      else
        notify_list = &(var->neg_notify_lit_watchers);
    }
  else
    {
      assert (QDPLL_LIT_POS (lit));
      if (!is_cube)
        notify_list = &(var->neg_notify_lit_watchers);
      else
        notify_list = &(var->pos_notify_lit_watchers);
    }
  assert (count_in_notify_literal_watcher_list (notify_list, clause) == 1);

  unsigned int offset = clause->offset_in_notify_list[lit_is_rwlit];
  BLitsOcc last_occ = QDPLL_POP_STACK (*notify_list);
  Constraint *last_occ_constr = last_occ.constraint;
  int marked = BLIT_MARKED_PTR (last_occ_constr);
  last_occ_constr = BLIT_STRIP_PTR (last_occ_constr);
  assert (marked || !last_occ_constr->is_cube);
  assert (!marked || last_occ_constr->is_cube);

  if (last_occ_constr == clause)
    return;

  const int same_types = (clause->is_cube == last_occ_constr->is_cube);
  /* Overwrite the current position with the last entry. */
  assert (BLIT_STRIP_PTR (notify_list->start[offset].constraint) == clause);
  notify_list->start[offset] = last_occ;
  assert (notify_list->start[offset].blit == last_occ.blit);
  assert (notify_list->start[offset].constraint == last_occ.constraint);
  /* Must update position information in the copied entry. */
  unsigned int *other_offsetp = last_occ_constr->offset_in_notify_list;
  LitID other_wlit = *(last_occ_constr->lits + last_occ_constr->lwatcher_pos);
  /* Literal 'lit' must be watched in 'last_entry' as well. */
  if ((same_types && other_wlit != lit)
      || ((!same_types && other_wlit != -lit)))
    {
      other_wlit = *(last_occ_constr->lits + last_occ_constr->rwatcher_pos);
      other_offsetp++;
    }
  assert (!same_types || other_wlit == lit);
  assert (same_types || other_wlit == -lit);
  *other_offsetp = offset;

  assert (count_in_notify_literal_watcher_list (notify_list, clause) == 0);
}


static void
add_clause_to_notify_list (QDPLL * qdpll, const int is_cube, int lit_is_rwlit,
                           LitID lit, Var * var, BLitsOcc blit)
{
  Constraint *clause = BLIT_STRIP_PTR (blit.constraint);
  QDPLLMemMan *mm = qdpll->mm;
  /* Add clause to notification list wrt. sign of literal. */
  BLitsOccStack *other_notify_list;
  if (QDPLL_LIT_NEG (lit))
    {
      if (!is_cube)
        other_notify_list = &(var->pos_notify_lit_watchers);
      else
        other_notify_list = &(var->neg_notify_lit_watchers);
    }
  else
    {
      assert (QDPLL_LIT_POS (lit));
      if (!is_cube)
        other_notify_list = &(var->neg_notify_lit_watchers);
      else
        other_notify_list = &(var->pos_notify_lit_watchers);
    }
  assert (count_in_notify_literal_watcher_list (other_notify_list, clause) ==
          0);
  /* Store clauses's position in notify-list. */
  clause->offset_in_notify_list[lit_is_rwlit] =
    QDPLL_COUNT_STACK (*other_notify_list);
  QDPLL_PUSH_STACK (mm, *other_notify_list, blit);
  assert (count_in_notify_literal_watcher_list (other_notify_list, clause) ==
          1);
}


/* Function is called to check satisfied cubes/learnt clauses and
   learnt unit constraints for spurious pure literals. */
static int
has_constraint_spurious_pure_lit (QDPLL * qdpll, Constraint * c)
{
  /* Spurious pure literals can only occur in learnt constraints
     because we use original clauses for detection. */
  if (!c->learnt && !c->is_cube)
    {
      return 0;
    }
  assert (!qdpll->options.no_spure_literals);
  Var *vars = qdpll->pcnf.vars;
  const int is_cube = c->is_cube;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      if (var->mode == QDPLL_VARMODE_PURE)
        {
          assert (QDPLL_VAR_ASSIGNED (var));
          if (!is_cube && QDPLL_SCOPE_EXISTS (var->scope))
            {
              /* A false existential pure literal in a learnt clause
                 is always spurious. Normally, pure existential literals
                 always satisfy clauses. */
              if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)) ||
                  (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)))
                return 1;
            }
          else if (is_cube && QDPLL_SCOPE_FORALL (var->scope))
            {
              /* A true universal pure literal in a learnt cube
                 is always spurious. Normally, pure universal literals
                 always falsify cubes. */
              if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
                  (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
                return 1;
            }
        }
    }
  return 0;
}

static void learnt_constraint_mtf (QDPLL * qdpll, Constraint * c);

static Constraint *
handle_detected_unit_constraint (QDPLL * qdpll, LitID lit, Var * var,
                                 Constraint * constraint)
{
  assert (!QDPLL_VAR_ASSIGNED (var));
  assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
  assert (!constraint->qbcp_qbce_blocked);

  if (!qdpll->options.no_spure_literals)
    {
      if (has_constraint_spurious_pure_lit (qdpll, constraint))
        {
#if COMPUTE_STATS
          if (constraint->is_cube)
            qdpll->stats.total_splits_ignored_unit_cubes++;
          else
            qdpll->stats.total_splits_ignored_unit_clauses++;
#endif
          return constraint;
        }
    }

  assert (!var->antecedent);
  var->antecedent = constraint;
  assert (!constraint->is_reason);
  constraint->is_reason = 1;

  if (constraint->learnt)
    {
      if (!qdpll->options.no_unit_mtf)
        learnt_constraint_mtf (qdpll, constraint);
#if COMPUTE_STATS
      assert (!constraint->derived_by_trivial_truth_or_falsity || 
              !constraint->derived_by_dynamic_nenofex);
      if (constraint->is_cube)
        {
          qdpll->stats.total_unit_lcubes++;
          if (constraint->is_taut)
            qdpll->stats.total_unit_taut_lcubes++;
          if (constraint->derived_by_trivial_truth_or_falsity)
            qdpll->stats.trivial_truth_unit_cubes++;
          else if (constraint->derived_by_dynamic_nenofex)
            qdpll->stats.dyn_nenofex_unit_cubes++;
        }
      else
        {
          qdpll->stats.total_unit_lclauses++;
          if (constraint->is_taut)
            qdpll->stats.total_unit_taut_lclauses++;
          if (constraint->derived_by_trivial_truth_or_falsity)
            qdpll->stats.trivial_falsity_unit_clauses++;
          else if (constraint->derived_by_dynamic_nenofex)
            qdpll->stats.dyn_nenofex_unit_clauses++;
        }
#endif
    }

  /* Push unit. */
  push_assigned_variable (qdpll, var,
                          QDPLL_LIT_POS (lit) ?
                          QDPLL_ASSIGNMENT_TRUE :
                          QDPLL_ASSIGNMENT_FALSE, QDPLL_VARMODE_UNIT);

  return constraint;
}


/* Called after watcher became false. Try to set up watcher invariant by 
   finding new pair of watched literals. Returns null if conflict occurred, 
   otherwise sentinel for entry deletion. Detected unit literals will be pushed immediately.
*/
static Constraint *
update_literal_watchers (QDPLL * qdpll, Var * propagated_var,
                         BLitsOcc * blit_ptr)
{
  BLitsOcc blit = *blit_ptr;
  Constraint *clause = BLIT_STRIP_PTR (blit.constraint);
  assert (!clause->qbcp_qbce_blocked);

#if COMPUTE_STATS
  qdpll->stats.total_lit_watcher_update_calls++;
#endif

  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  const int is_cube = clause->is_cube;
  /* When disabling unit literals or using lazy assignments, we need
     to watch original unit clauses for UNSAT-checking. */
  assert (clause->num_lits > 1);

  assert (QDPLL_VAR_ASSIGNED (propagated_var));
  assert (QDPLL_VAR_MARKED_PROPAGATED (propagated_var));
  assert (clause->num_lits == 1
          || clause->lwatcher_pos < clause->rwatcher_pos);
  assert (clause->rwatcher_pos < clause->num_lits);
  assert (clause->lwatcher_pos < clause->num_lits);

  unsigned int oldlwpos = clause->lwatcher_pos;
  unsigned int newlwpos, newrwpos;

  LitID *lits = clause->lits;
  LitID lwlit = *(lits + oldlwpos);
  Var *lwvar = LIT2VARPTR (vars, lwlit);

  /* Check if a watcher satisfies clause already. */

  if (QDPLL_LIT_NEG (lwlit))
    {
      if ((!is_cube && QDPLL_VAR_ASSIGNED_FALSE (lwvar)) ||
          (is_cube && QDPLL_VAR_ASSIGNED_TRUE (lwvar)))
        {
          /* True watcher must not equal blocking lit, otherwise we
             should have detected that before. */
          assert (lwlit != blit.blit);
          update_blocking_literal (qdpll, vars, blit_ptr, clause, lwlit,
                                   lwvar, is_cube);
#if COMPUTE_STATS
          qdpll->stats.total_lit_watcher_update_sat_by_lw++;
#endif
          return clause;
        }
    }
  else
    {
      assert (QDPLL_LIT_POS (lwlit));
      if ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (lwvar)) ||
          (is_cube && QDPLL_VAR_ASSIGNED_FALSE (lwvar)))
        {
          /* True watcher must not equal blocking lit, otherwise we
             should have detected that before. */
          assert (lwlit != blit.blit);
          update_blocking_literal (qdpll, vars, blit_ptr, clause, lwlit,
                                   lwvar, is_cube);
#if COMPUTE_STATS
          qdpll->stats.total_lit_watcher_update_sat_by_lw++;
#endif
          return clause;
        }
    }

  unsigned int oldrwpos = clause->rwatcher_pos;
  LitID rwlit = *(lits + oldrwpos);
  Var *rwvar = LIT2VARPTR (vars, rwlit);

  if (QDPLL_LIT_NEG (rwlit))
    {
      if ((!is_cube && QDPLL_VAR_ASSIGNED_FALSE (rwvar)) ||
          (is_cube && QDPLL_VAR_ASSIGNED_TRUE (rwvar)))
        {
          /* True watcher must not equal blocking lit, otherwise we
             should have detected that before. */
          assert (rwlit != blit.blit);
          update_blocking_literal (qdpll, vars, blit_ptr, clause, rwlit,
                                   rwvar, is_cube);
#if COMPUTE_STATS
          qdpll->stats.total_lit_watcher_update_sat_by_rw++;
#endif
          return clause;
        }
    }
  else
    {
      assert (QDPLL_LIT_POS (rwlit));
      if ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (rwvar)) ||
          (is_cube && QDPLL_VAR_ASSIGNED_FALSE (rwvar)))
        {
          /* True watcher must not equal blocking lit, otherwise we
             should have detected that before. */
          assert (rwlit != blit.blit);
          update_blocking_literal (qdpll, vars, blit_ptr, clause, rwlit,
                                   rwvar, is_cube);
#if COMPUTE_STATS
          qdpll->stats.total_lit_watcher_update_sat_by_rw++;
#endif
          return clause;
        }
    }

  assert (is_cube || QDPLL_VAR_EXISTS (rwvar));
  assert (!is_cube || QDPLL_VAR_FORALL (rwvar));
  assert (QDPLL_VAR_ASSIGNED (lwvar) || QDPLL_VAR_ASSIGNED (rwvar));
  assert (rwlit != 0);
  assert (lwlit != 0);
  assert (clause->num_lits == 1 || rwlit != lwlit);
  assert (clause->num_lits == 1 || -rwlit != lwlit);

  if (!QDPLL_VAR_ASSIGNED (rwvar))
    {
      /* Left watcher assigned. Here, conflicts/solutions can NOT occur. */
      assert (lwvar == propagated_var);
      assert (is_cube || QDPLL_LIT_POS (lwlit)
              || QDPLL_VAR_ASSIGNED_TRUE (lwvar));
      assert (is_cube || QDPLL_LIT_NEG (lwlit)
              || QDPLL_VAR_ASSIGNED_FALSE (lwvar));
      assert (!is_cube || QDPLL_LIT_POS (lwlit)
              || QDPLL_VAR_ASSIGNED_FALSE (lwvar));
      assert (!is_cube || QDPLL_LIT_NEG (lwlit)
              || QDPLL_VAR_ASSIGNED_TRUE (lwvar));

      if ((newlwpos =
           find_watcher_pos (qdpll, is_cube, vars, clause,
                             lits + oldrwpos - 1, lits, QDPLL_QTYPE_UNDEF,
                             blit_ptr)) != QDPLL_INVALID_WATCHER_POS)
        {
          if (newlwpos != QDPLL_WATCHER_SAT)
            {                   /* New watcher found -> update notify lists. */
              remove_clause_from_notify_list (qdpll, is_cube, 0, lwlit,
                                              clause);
              lwlit = *(lits + newlwpos);
              assert (lwlit);
              lwvar = LIT2VARPTR (vars, lwlit);
              add_clause_to_notify_list (qdpll, is_cube, 0, lwlit, lwvar,
                                         blit);
              clause->lwatcher_pos = newlwpos;
              return clause + 1;
            }
          else                  /* Clause is satisfied. */
            {
              return clause;
            }
        }
      else
        {
          /* Did not find new left watcher. Next, try to find new right watcher. */
          newrwpos =
            find_watcher_pos (qdpll, is_cube, vars, clause,
                              lits + clause->num_lits - 1, lits,
                              is_cube ? QDPLL_QTYPE_FORALL :
                              QDPLL_QTYPE_EXISTS, blit_ptr);
          assert (newrwpos != QDPLL_INVALID_WATCHER_POS);
          assert (oldrwpos <= newrwpos);
          if (newrwpos != QDPLL_WATCHER_SAT)
            {
              if (newrwpos != oldrwpos)
                {
                  assert (oldrwpos < newrwpos);
                  newlwpos =
                    find_watcher_pos (qdpll, is_cube, vars, clause,
                                      lits + newrwpos - 1, lits + oldrwpos,
                                      QDPLL_QTYPE_UNDEF, blit_ptr);
                  assert (newlwpos != QDPLL_INVALID_WATCHER_POS);
                  assert (oldrwpos <= newlwpos);
                  if (newlwpos != QDPLL_WATCHER_SAT)
                    {
                      if (newlwpos != oldrwpos)
                        {
                          /* Must remove entry for old watcher and add two new entries. */
                          assert (oldrwpos < newlwpos);

                          remove_clause_from_notify_list (qdpll, is_cube, 1,
                                                          rwlit, clause);

                          rwlit = *(lits + newrwpos);
                          assert (rwlit);
                          rwvar = LIT2VARPTR (vars, rwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 1, rwlit,
                                                     rwvar, blit);

                          remove_clause_from_notify_list (qdpll, is_cube, 0,
                                                          lwlit, clause);
                          lwlit = *(lits + newlwpos);
                          assert (lwlit);
                          lwvar = LIT2VARPTR (vars, lwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 0, lwlit,
                                                     lwvar, blit);
                        }
                      else
                        {
                          /* Must add entry for new right watcher. */
                          remove_clause_from_notify_list (qdpll, is_cube, 0,
                                                          lwlit, clause);
                          clause->offset_in_notify_list[0] =
                            clause->offset_in_notify_list[1];
                          rwlit = *(lits + newrwpos);
                          assert (rwlit);
                          rwvar = LIT2VARPTR (vars, rwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 1, rwlit,
                                                     rwvar, blit);
                        }

                      clause->lwatcher_pos = newlwpos;
                      clause->rwatcher_pos = newrwpos;

                      return clause + 1;
                    }
                  else
                    {
                      /* Clause is satisfied. */
                      return clause;
                    }
                }
              else
                {
                  /* Clause is unit. No unassigned literal to the left of old rwatcher. */
                  return handle_detected_unit_constraint (qdpll,
                                                          !is_cube ? rwlit :
                                                          -rwlit, rwvar,
                                                          clause);
                }
            }
          else
            {
              /* Clause is satisfied. */
              return clause;
            }
        }
    }
  else
    {
      /* Right watcher assigned. Here, both unit literals and conflicts can occur. */
      assert (is_cube || QDPLL_LIT_POS (rwlit)
              || QDPLL_VAR_ASSIGNED_TRUE (rwvar));
      assert (is_cube || QDPLL_LIT_NEG (rwlit)
              || QDPLL_VAR_ASSIGNED_FALSE (rwvar));
      assert (!is_cube || QDPLL_LIT_POS (rwlit)
              || QDPLL_VAR_ASSIGNED_FALSE (rwvar));
      assert (!is_cube || QDPLL_LIT_NEG (rwlit)
              || QDPLL_VAR_ASSIGNED_TRUE (rwvar));
      assert (QDPLL_VAR_ASSIGNED (lwvar) || rwvar == propagated_var);

      if ((newrwpos =
           find_watcher_pos (qdpll, is_cube, vars, clause,
                             lits + clause->num_lits - 1, lits,
                             is_cube ? QDPLL_QTYPE_FORALL :
                             QDPLL_QTYPE_EXISTS,
                             blit_ptr)) != QDPLL_INVALID_WATCHER_POS)
        {                       /* Clause can not be conflicting, since existential literal found. */
          if (newrwpos != QDPLL_WATCHER_SAT)
            {
              /* NOTE: at this point, if left watcher not false, then need not find new left watcher. */
              if ((newlwpos =
                   find_watcher_pos (qdpll, is_cube, vars, clause,
                                     lits + newrwpos - 1, lits,
                                     QDPLL_QTYPE_UNDEF,
                                     blit_ptr)) != QDPLL_INVALID_WATCHER_POS)
                {
                  if (newlwpos != QDPLL_WATCHER_SAT)
                    {           /* New watcher found -> update notify lists. */
                      assert (newlwpos < newrwpos);

                      if (newlwpos != oldlwpos)
                        {       /* Must remove one old entry and add two new ones. */
                          remove_clause_from_notify_list (qdpll, is_cube, 0,
                                                          lwlit, clause);
                          remove_clause_from_notify_list (qdpll, is_cube, 1,
                                                          rwlit, clause);

                          rwlit = *(lits + newrwpos);
                          assert (rwlit);
                          rwvar = LIT2VARPTR (vars, rwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 1, rwlit,
                                                     rwvar, blit);

                          lwlit = *(lits + newlwpos);
                          assert (lwlit);
                          lwvar = LIT2VARPTR (vars, lwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 0, lwlit,
                                                     lwvar, blit);
                        }
                      else
                        {       /* Add new entry for new right watcher. */
                          assert (clause->lwatcher_pos == newlwpos);
                          remove_clause_from_notify_list (qdpll, is_cube, 1,
                                                          rwlit, clause);
                          rwlit = *(lits + newrwpos);
                          assert (rwlit);
                          rwvar = LIT2VARPTR (vars, rwlit);
                          add_clause_to_notify_list (qdpll, is_cube, 1, rwlit,
                                                     rwvar, blit);
                        }

                      clause->rwatcher_pos = newrwpos;
                      clause->lwatcher_pos = newlwpos;

                      return clause + 1;
                    }
                  else          /* Clause is satisfied. */
                    {
                      return clause;
                    }
                }
              else
                {
                  /* Clause is unit or sat. when watching true
                     lits. No unassigned literal to the left of new
                     rwatcher. */

                  rwlit = *(lits + newrwpos);
                  assert (rwlit != 0);
                  rwvar = LIT2VARPTR (vars, rwlit);

                  return handle_detected_unit_constraint (qdpll,
                                                          !is_cube ? rwlit
                                                          : -rwlit, rwvar,
                                                          clause);
                }
            }
          else                  /* Clause is satisfied. */
            {
              return clause;
            }
        }
      else                      /* Clause is conflicting: no free existential literal found. */
        {
          return 0;
        }
    }
}


static void
init_literal_watcher (QDPLL * qdpll, Constraint * c, unsigned int left_offset,
                      unsigned int right_offset)
{
  assert (c->num_lits > 1);
  assert (left_offset < c->num_lits);
  assert (right_offset < c->num_lits);
  assert (left_offset < right_offset);
  assert (c->num_lits != 1 || left_offset == right_offset);
  assert (c->num_lits == 1 || left_offset != right_offset);

  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LitID lit, *litp;
  VarID var_id;
  unsigned int num_lits = c->num_lits;
  const int is_cube = c->is_cube;
  Var *var;

  /* Set right watcher. */
  litp = c->lits + right_offset;
  assert (litp >= c->lits);
  assert (litp < c->lits + num_lits);
  lit = *litp;
  assert (lit != 0);
  var_id = LIT2VARID (lit);
  var = VARID2VARPTR (vars, var_id);
  assert (is_cube || QDPLL_VAR_EXISTS (var));
  assert (!is_cube || QDPLL_VAR_FORALL (var));

  c->rwatcher_pos = right_offset;

  /* Add clause to notification list wrt. sign of literal. */
  BLitsOccStack *notify_list;
  if (QDPLL_LIT_NEG (lit))
    {
      if (!is_cube)
        notify_list = &(var->pos_notify_lit_watchers);
      else
        notify_list = &(var->neg_notify_lit_watchers);
    }
  else
    {
      assert (QDPLL_LIT_POS (lit));
      if (!is_cube)
        notify_list = &(var->neg_notify_lit_watchers);
      else
        notify_list = &(var->pos_notify_lit_watchers);
    }
  assert (count_in_notify_literal_watcher_list (notify_list, c) == 0);
  /* For initialization, simply use watched literal as blocking literal. */
  BLitsOcc occ = { lit, is_cube ? BLIT_MARK_PTR (c) : c };
  /* Store clauses's position in notify-list. */
  c->offset_in_notify_list[1] = QDPLL_COUNT_STACK (*notify_list);
  QDPLL_PUSH_STACK (mm, *notify_list, occ);
  assert (count_in_notify_literal_watcher_list (notify_list, c) == 1);

  /* Set left watcher. */
  litp = c->lits + left_offset;

  assert (litp >= c->lits);
  assert (litp < c->lits + num_lits);
  lit = *litp;
  assert (lit != 0);
  var_id = LIT2VARID (lit);
  var = VARID2VARPTR (vars, var_id);

  c->lwatcher_pos = left_offset;

  /* Add clause to notification list wrt. sign of literal. */
  if (QDPLL_LIT_NEG (lit))
    {
      if (!is_cube)
        notify_list = &(var->pos_notify_lit_watchers);
      else
        notify_list = &(var->neg_notify_lit_watchers);
    }
  else
    {
      assert (QDPLL_LIT_POS (lit));
      if (!is_cube)
        notify_list = &(var->neg_notify_lit_watchers);
      else
        notify_list = &(var->pos_notify_lit_watchers);
    }
  assert (num_lits == 1
          || count_in_notify_literal_watcher_list (notify_list, c) == 0);
  occ.blit = lit;
  assert (!is_cube || occ.constraint == BLIT_MARK_PTR (c));
  assert (is_cube || occ.constraint == c);
  /* Store clauses's position in notify-list. */
  c->offset_in_notify_list[0] = QDPLL_COUNT_STACK (*notify_list);
  QDPLL_PUSH_STACK (mm, *notify_list, occ);
  assert (num_lits == 1
          || count_in_notify_literal_watcher_list (notify_list, c) == 1);
}

/* Find watched lit only wrt. deps but not wrt. assignment. */
static unsigned int
find_init_watcher_pos (QDPLL * qdpll, const int is_cube, Var * vars,
                       LitID * lits, LitID * right, LitID * left,
                       const QDPLLQuantifierType qtype)
{
  assert (qdpll->dm->is_init (qdpll->dm));
#if COMPUTE_STATS
  qdpll->stats.total_lit_watcher_find_calls++;
#endif
  Var *oldw = 0;
  QDPLLQuantifierType oldw_type = QDPLL_QTYPE_UNDEF;
  if (qtype == QDPLL_QTYPE_UNDEF)
    {
      /* Only when searching new left watcher. */
      oldw = LIT2VARPTR (qdpll->pcnf.vars, *(right + 1));
      oldw_type = oldw->scope->type;
      assert (!is_cube || oldw_type == QDPLL_QTYPE_FORALL);
      assert (is_cube || oldw_type == QDPLL_QTYPE_EXISTS);
    }

  for (; right >= left; right--)
    {
      assert (right >= lits);

#if COMPUTE_STATS
      qdpll->stats.total_lit_watcher_find_lit_visits++;
#endif

      LitID lit = *right;
      assert (lit != 0);
      Var *var = LIT2VARPTR (vars, lit);
      assert (QDPLL_VAR_HAS_OCCS (var));
      if (!QDPLL_VAR_ASSIGNED (var))
        {
          /* Literal unassigned. */
          if (qtype == QDPLL_QTYPE_UNDEF || qtype == var->scope->type)
            {
#if COMPUTE_STATS
              qdpll->stats.total_lwatched++;
#endif
              if (qtype == QDPLL_QTYPE_UNDEF && oldw_type != var->scope->type)
                {
#if COMPUTE_STATS
                  qdpll->stats.total_lwatched_tested++;
#endif
                  if (!qdpll->dm->depends (qdpll->dm, var->id, oldw->id))
                    {
#if COMPUTE_STATS
                      qdpll->stats.non_dep_lwatched_skipped++;
#endif
                      continue;
                    }
                }
              return right - lits;
            }
        }
      else
        {
          /* Check if assigned literal satisfies clause / falsifies cube. */
          if (QDPLL_LIT_NEG (lit))
            {
              if ((!is_cube && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
                  (is_cube && QDPLL_VAR_ASSIGNED_TRUE (var)))
                return QDPLL_WATCHER_SAT;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if ((!is_cube && QDPLL_VAR_ASSIGNED_TRUE (var)) ||
                  (is_cube && QDPLL_VAR_ASSIGNED_FALSE (var)))
                return QDPLL_WATCHER_SAT;
            }
        }
    }

  return QDPLL_INVALID_WATCHER_POS;
}



static QDPLLSolverState
init_literal_watchers_for_constraint (QDPLL * qdpll, Constraint * c)
{
  assert (qdpll->state.decision_level == 0);
  assert (c->lwatcher_pos == QDPLL_INVALID_WATCHER_POS);
  assert (c->rwatcher_pos == QDPLL_INVALID_WATCHER_POS);
  assert (!c->qbcp_qbce_blocked);
  Var *vars = qdpll->pcnf.vars;
  const int is_cube = c->is_cube;

  unsigned int right_offset, left_offset;
  right_offset =
    find_init_watcher_pos (qdpll, is_cube, vars, c->lits,
                           c->lits + c->num_lits - 1, c->lits,
                           is_cube ? QDPLL_QTYPE_FORALL : QDPLL_QTYPE_EXISTS);

  if (right_offset == QDPLL_INVALID_WATCHER_POS)
    {
      /* Important to check for spurious pure literals. */
      if (qdpll->options.no_spure_literals ||
          !has_constraint_spurious_pure_lit (qdpll, c))
        return is_cube ? QDPLL_SOLVER_STATE_SAT : QDPLL_SOLVER_STATE_UNSAT;
      else
        assert (c->is_cube || c->learnt); 
    }
  else if (right_offset != QDPLL_WATCHER_SAT)
    {
      left_offset =
        find_init_watcher_pos (qdpll, is_cube, vars, c->lits,
                               c->lits + right_offset - 1, c->lits,
                               QDPLL_QTYPE_UNDEF);
      if (left_offset == QDPLL_INVALID_WATCHER_POS)
        {
          /* Constraint is unit. Spurious pure lits are handled. */
          LitID rwlit = c->lits[right_offset];
          Var *rwvar = LIT2VARPTR (vars, rwlit);
          handle_detected_unit_constraint (qdpll, !is_cube ?
                                           rwlit : -rwlit, rwvar, c);
        }
      else if (left_offset != QDPLL_WATCHER_SAT)
        init_literal_watcher (qdpll, c, left_offset, right_offset);
    }
  /* If constraint disabled at top level, then do not set any watcher. */

  return QDPLL_SOLVER_STATE_UNDEF;
}


static QDPLLSolverState
init_literal_watchers_aux (QDPLL * qdpll, ConstraintList * clist)
{
  QDPLLSolverState result;
  Constraint *c, *next;
  for (c = clist->first; c; c = next)
    {
      /* Bug Fix: constraint-mtf for detected units modifies list! */
      next = c->link.next;
      if (c->qbcp_qbce_blocked)
        continue;
      if ((result =
           init_literal_watchers_for_constraint (qdpll,
                                                 c)) !=
          QDPLL_SOLVER_STATE_UNDEF)
        {
          assert (!qdpll->result_constraint);
          qdpll->result_constraint = c;
          return result;
        }
    }
  return QDPLL_SOLVER_STATE_UNDEF;
}


/* Initialize literal watchers to two rightmost literals in clause. */
static QDPLLSolverState
init_literal_watchers (QDPLL * qdpll)
{
  assert (!qdpll->result_constraint);
  assert (qdpll->state.decision_level == 0);
  QDPLLSolverState result;

  if ((result = init_literal_watchers_aux
       (qdpll, &(qdpll->pcnf.clauses))) != QDPLL_SOLVER_STATE_UNDEF)
    return result;

  if ((result = init_literal_watchers_aux
       (qdpll, &(qdpll->pcnf.learnt_clauses))) != QDPLL_SOLVER_STATE_UNDEF)
    return result;

  result = init_literal_watchers_aux (qdpll, &(qdpll->pcnf.learnt_cubes));

  return result;
}

/* -------------------- END: LITERAL WATCHING -------------------- */

static void
delete_scope (QDPLL * qdpll, Scope * scope)
{
  QDPLLMemMan *mm = qdpll->mm;
  QDPLL_DELETE_STACK (mm, scope->vars);
  QDPLL_DELETE_STACK (mm, scope->cover_lits);
  qdpll_free (mm, scope, sizeof (Scope));
}


static void
delete_scope_list (QDPLL *qdpll, ScopeList *scope_list)
{
  Scope *s, *n;
  for (s = scope_list->first; s; s = n)
    {
      n = s->link.next;
      delete_scope (qdpll, s);
    }
}


static void
update_scope_nestings_and_ptrs_on_stack (QDPLL *qdpll, const int update_user_scopes)
{
  /* Update the nesting levels of the user scopes and collect pointers to the
     user scopes on stack 'qdpll->pcnf.user_scope_ptrs'. */
  if (update_user_scopes)
    QDPLL_RESET_STACK(qdpll->pcnf.user_scope_ptrs);
  /* User scope numbering starts at nesting level 1. */
  Nesting nesting = update_user_scopes ? 
    QDPLL_DEFAULT_SCOPE_NESTING + 1 : QDPLL_DEFAULT_SCOPE_NESTING;
  Scope *s;
  for (s = update_user_scopes ? 
         qdpll->pcnf.user_scopes.first : qdpll->pcnf.scopes.first; 
       s; s = s->link.next)
    {
      assert (!update_user_scopes || !s->is_internal);
      assert (update_user_scopes || s->is_internal);
      s->nesting = nesting++;
      if (update_user_scopes)
        QDPLL_PUSH_STACK(qdpll->mm, qdpll->pcnf.user_scope_ptrs, s);
    }
  assert (!update_user_scopes || QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs) == 
          qdpll_get_max_scope_nesting (qdpll));
}


/* Remove scopes which contain no variable. Typically called after no-occ
   variables have been eliminated. */
static void
cleanup_empty_scopes (QDPLL * qdpll, ScopeList *scopes)
{
  assert (scopes == &qdpll->pcnf.user_scopes || scopes == &qdpll->pcnf.scopes);
  unsigned int modified = 0;
  Scope *s, *n;
  for (s = scopes->first; s; s = n)
    {
      n = s->link.next;
      assert (scopes != &qdpll->pcnf.user_scopes || 
              s->nesting != QDPLL_DEFAULT_SCOPE_NESTING);
      assert (scopes != &qdpll->pcnf.user_scopes || !s->is_internal);
      assert (scopes != &qdpll->pcnf.scopes || s->is_internal);
      assert (s->nesting != QDPLL_DEFAULT_SCOPE_NESTING
              || QDPLL_SCOPE_EXISTS (s));
      /* Should keep one outermost existential scope as default scope. */
      if (!QDPLL_COUNT_STACK (s->vars)
          && s->nesting != QDPLL_DEFAULT_SCOPE_NESTING)
        {                       
          /* Unlink and delete scope. */
          UNLINK (*scopes, s, link);
          delete_scope (qdpll, s);
          modified = 1;
        }
    }

  /* Must never delete default scope. */
  assert (qdpll->pcnf.scopes.first && 
          qdpll->pcnf.scopes.first->nesting == 0 && 
          qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);

  if (modified)
    update_scope_nestings_and_ptrs_on_stack (qdpll, (scopes == &qdpll->pcnf.user_scopes));
}


static void
delete_variable (QDPLL * qdpll, Var * var)
{
  QDPLLMemMan *mm = qdpll->mm;
  QDPLL_DELETE_STACK (mm, var->pos_notify_clause_watchers);
  QDPLL_DELETE_STACK (mm, var->neg_notify_clause_watchers);
  QDPLL_DELETE_STACK (mm, var->pos_offset_in_notify_list);
  QDPLL_DELETE_STACK (mm, var->neg_offset_in_notify_list);
  QDPLL_DELETE_STACK (mm, var->pos_offset_in_watched_clause);
  QDPLL_DELETE_STACK (mm, var->neg_offset_in_watched_clause);
  QDPLL_DELETE_STACK (mm, var->pos_notify_lit_watchers);
  QDPLL_DELETE_STACK (mm, var->neg_notify_lit_watchers);
  QDPLL_DELETE_STACK (mm, var->neg_occ_clauses);
  QDPLL_DELETE_STACK (mm, var->pos_occ_clauses);
  QDPLL_DELETE_STACK (mm, var->neg_occ_cubes);
  QDPLL_DELETE_STACK (mm, var->pos_occ_cubes);
  QDPLL_DELETE_STACK (mm, var->type_red_member_lits);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_watched_neg_occ_clauses);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_watched_pos_occ_clauses);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_offset_of_neg_lit_in_watched_occ);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_offset_of_pos_lit_in_watched_occ);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_prepro_pos_blocking_lit_clauses);
  QDPLL_DELETE_STACK (mm, var->qbcp_qbce_prepro_neg_blocking_lit_clauses);

  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  dm->notify_reset_variable (dm, var->id);
}


static void
reset_variable (QDPLL * qdpll, Var * var)
{
  delete_variable (qdpll, var);
  assert (qdpll->pcnf.used_vars != 0);
  qdpll->pcnf.used_vars--;
  memset (var, 0, sizeof (Var));
}


static VarID
find_max_declared_user_var_id (QDPLL *qdpll, Var *start)
{
  assert (start >= qdpll->pcnf.vars && 
          start < qdpll->pcnf.vars + qdpll->pcnf.size_vars);

  VarID max = 0;
  Var *p, *e;
  for (e = qdpll->pcnf.vars, p = start; e <= p; p--)
    {
      assert (p < qdpll->pcnf.vars + qdpll->pcnf.size_user_vars || 
              !p->id || p->is_internal);
      assert (p >= qdpll->pcnf.vars + qdpll->pcnf.size_user_vars || 
              !p->id || !p->is_internal);
      if (p->id && !p->is_internal)
        {
          assert (!max);
          max = p->id;
          break;
        }
    }

  /* Check variables in user scopes. We might have kept IDs of deleted no occ
     variables there. */
  Scope *s;
  for (s = qdpll->pcnf.user_scopes.first; s; s = s->link.next)
    {
      VarID *vp, *ve;
      for (vp = s->vars.start, ve = s->vars.top; vp < ve; vp++)
        {
          VarID id = *vp;
          if (id > max)
            max = id;
        }
    }

  return max;
}


/* Remove variables without occurrences. This disturbs variable ordering in
   scopes. The parameter 'cleanup_user_prefix' indicates if user-variables which
   have no occurrences should be cleaned up. */
static void
cleanup_no_occ_variables (QDPLL * qdpll, const int cleanup_user_prefix)
{
  Var *vars = qdpll->pcnf.vars;
  unsigned int no_occ_user_var_deleted = 0;

  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      VarIDStack *scope_vars = &s->vars;
      VarID *p, *end, *last;
      for (p = scope_vars->start, end = scope_vars->top, last = end - 1;
           p < end; p++)
        {
          assert (*p > 0);
          assert (*p < qdpll->pcnf.size_vars);
          Var *v = VARID2VARPTR (vars, *p);
          /* Bug fix: must check if 'v->id' is non-zero to handle the case
             where an internal variable 'v' has been cleaned up before. Such
             cleaned up internal variables are kept in the default scope since
             deleting them would perhaps cause problems with frame indices and
             internal variables on stack 'qdpll->state.cur_used_internal_vars'. 
             Actually, this policy allows for empty frames, either because the
             user did not push any clauses or all pushed clauses were
             tautological. */
          /* Update: we never delete internal no-occ vars which are currently
             used as selector variables of active frames, i.e. on stack
             'cur_used_internal_vars', by checking the flag
             'v->is_cur_used_internal_var'. */
          if (v->id && !QDPLL_VAR_HAS_OCCS (v) && !v->is_cur_used_internal_var)
            {
              assert (!QDPLL_VAR_ASSIGNED(v));
              /* Bug fix: in incremental mode, user variables might lose all
                 their occs if clauses are popped off. */
              if (v->priority_pos != QDPLL_INVALID_PQUEUE_POS)
                var_pqueue_remove_elem (qdpll, v->priority_pos);
              *p-- = *last--;
              end--;
              scope_vars->top--;
              if (v->user_scope && cleanup_user_prefix)
                {
                  assert (!v->is_internal);
                  no_occ_user_var_deleted = 1;
                  /* If 'v' is a user variable then delete 'v' from user scope vars stack. */
                  unsigned int offset_in_user_scope = v->offset_in_user_scope_vars;
                  assert (!QDPLL_EMPTY_STACK(v->user_scope->vars));
                  assert (offset_in_user_scope < QDPLL_COUNT_STACK(v->user_scope->vars));
                  VarID last_id_in_user_vars = QDPLL_POP_STACK(v->user_scope->vars);
                  assert (last_id_in_user_vars);
                  v->user_scope->vars.start[offset_in_user_scope] = last_id_in_user_vars;
                  Var *last_var_in_user_vars = VARID2VARPTR(qdpll->pcnf.vars, last_id_in_user_vars);
                  last_var_in_user_vars->offset_in_user_scope_vars = offset_in_user_scope;
                }
              else
                assert (v->user_scope || !v->offset_in_user_scope_vars);
              reset_variable (qdpll, v);
            }
        }
    }

  /* Bug fix: must update 'pcnf.max_declared_user_var_id' if no-occ vars have
     been deleted. */
  if (no_occ_user_var_deleted)
    {
      assert (cleanup_user_prefix);
      qdpll->pcnf.max_declared_user_var_id = 
        find_max_declared_user_var_id (qdpll, qdpll->pcnf.vars + 
                                       qdpll->pcnf.size_user_vars - 1);
    }
}


/* Maintain prefix properties. Should be called before solving starts. This
   matters mostly for the dependency manager, not for the solver
   itself. Usually, 'cleanup_empty_scopes' should be called before calling
   this function. */
static void
merge_adjacent_same_type_scopes (QDPLL * qdpll)
{
  QDPLLMemMan *mm = qdpll->mm;
  unsigned int modified = 0;
  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
      if (n && s->type == n->type)
        {                       
          /* Adjacent scopes have same type -> merge 'n' into 's'. */
          VarIDStack *scope_vars = &s->vars;
          VarID *p, *e, v;
          for (p = n->vars.start, e = n->vars.top; p < e; p++)
            {
              v = *p;
              QDPLL_PUSH_STACK (mm, *scope_vars, v);
              assert (qdpll->pcnf.vars[v].scope == n);
              qdpll->pcnf.vars[v].scope = s;
            }

          UNLINK (qdpll->pcnf.scopes, n, link);
          delete_scope (qdpll, n);
          n = s;
          modified = 1;
        }
    }

  assert (qdpll->pcnf.scopes.first->nesting == 0 && 
          qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);

  if (modified)
    update_scope_nestings_and_ptrs_on_stack (qdpll, 0);
}


/* Cleanup formula. 
   The parameter 'cleanup_user_prefix' indicates if the prefix given by the user
   should be cleaned up by: removing variables which have no occurrences and
   removing empty quantifier blocks. 
   NEW: the solver never removes user-given variables or blocks. The removal
   must be triggered by the user by calling the 'qdpll_gc' function. */
void
clean_up_formula (QDPLL * qdpll, const int cleanup_user_prefix)
{
  cleanup_no_occ_variables (qdpll, cleanup_user_prefix);
  if (cleanup_user_prefix)
    cleanup_empty_scopes (qdpll, &qdpll->pcnf.user_scopes);
  cleanup_empty_scopes (qdpll, &qdpll->pcnf.scopes);
  merge_adjacent_same_type_scopes (qdpll);

  /* Schedule the import of user prefix next time 'import_user_scopes' is called. */
  qdpll->state.no_scheduled_import_user_scopes = 0;
}

static void
reset_watchers (QDPLL * qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      c->is_watched = 0;
      c->rwatcher_pos = c->lwatcher_pos = QDPLL_INVALID_WATCHER_POS;
      c->offset_in_notify_list[0] = c->offset_in_notify_list[1] = 0;
    }

  for (c = qdpll->pcnf.learnt_clauses.first; c; c = c->link.next)
    {
      c->is_watched = 0;
      c->rwatcher_pos = c->lwatcher_pos = QDPLL_INVALID_WATCHER_POS;
      c->offset_in_notify_list[0] = c->offset_in_notify_list[1] = 0;
    }

  for (c = qdpll->pcnf.learnt_cubes.first; c; c = c->link.next)
    {
      c->is_watched = 0;
      c->rwatcher_pos = c->lwatcher_pos = QDPLL_INVALID_WATCHER_POS;
      c->offset_in_notify_list[0] = c->offset_in_notify_list[1] = 0;
    }

  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          p->mark_is_neg_watching_cube = p->mark_is_pos_watching_cube = 0;
          QDPLL_RESET_STACK (p->pos_notify_clause_watchers);
          QDPLL_RESET_STACK (p->neg_notify_clause_watchers);
          QDPLL_RESET_STACK (p->pos_offset_in_notify_list);
          QDPLL_RESET_STACK (p->neg_offset_in_notify_list);
          QDPLL_RESET_STACK (p->pos_offset_in_watched_clause);
          QDPLL_RESET_STACK (p->neg_offset_in_watched_clause);
          QDPLL_RESET_STACK (p->pos_notify_lit_watchers);
          QDPLL_RESET_STACK (p->neg_notify_lit_watchers);
        }
    }

  /* Reset data structures for empty-formula-watching. */
  if (!qdpll->options.no_empty_formula_watching)
    {
      /* Reset marks of variables appearing in old watched clause. */
      update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 0);
      qdpll->empty_formula_watcher = 0;
      /* Schedule watcher update. */
      qdpll->state.empty_formula_watcher_scheduled_update = 1;
      /* Reset stack of watchers per decision level. */
      QDPLL_RESET_STACK (qdpll->empty_formula_watchers_per_dec_level);
    }
}


static QDPLLSolverState
set_up_watchers (QDPLL * qdpll)
{
  assert (qdpll->state.decision_level == 0);
  /* Handle empty formula. */
  if (qdpll->pcnf.clauses.cnt == 0)
    return QDPLL_SOLVER_STATE_SAT;
  if (!qdpll->options.no_empty_formula_watching)
    {
      /* Check if all clauses are blocked or satisfied. */
      assert (!qdpll->empty_formula_watcher);
      if (!update_empty_formula_watcher (qdpll))
        return QDPLL_SOLVER_STATE_SAT;
    }
  if (!qdpll->options.no_pure_literals)
    init_clause_watchers (qdpll);
  QDPLLSolverState state = init_literal_watchers (qdpll);
  return state;
}


/* Set variable ID and scope and add to scope. 
   NOTE: 'is_var_internal' is true iff the added variable is internal. In
   this case, it is added to the default internal scope and hence also
   'scope->is_internal'. Free variables of the original formula are added
   to this default internal scope as well, but 'is_var_internal' is false
   in this case. */
static void
declare_and_init_variable (QDPLL * qdpll, Scope * scope, 
                           VarID id, const int is_var_internal, 
                           const int push_on_scope_vars_stack)
{
  assert (scope);
  assert (!is_var_internal || scope->is_internal);
  assert (!scope->is_internal || scope == qdpll->pcnf.scopes.first);
  assert (id > 0);
  assert (id < qdpll->pcnf.size_vars);
  /* Internal variables must be added to the default existential block, which
     is leftmost. */
  assert (!is_var_internal || (scope && scope == qdpll->pcnf.scopes.first && 
                           scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING && 
                           scope->type == QDPLL_QTYPE_EXISTS));

  QDPLLMemMan *mm = qdpll->mm;
  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);

  qdpll->pcnf.used_vars++;

  /* Init variable */
  assert (!var->id);
  var->id = id;
  assert (!var->priority_pos);
  var->priority_pos = QDPLL_INVALID_PQUEUE_POS;
  assert (!var->priority);
  var->priority = 1;
  assert (!var->decision_level);
  var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
  assert (!var->trail_pos);
  var->trail_pos = QDPLL_INVALID_TRAIL_POS;
  var->is_internal = is_var_internal;

  /* Set internal or user-scope for internal/user variables. Internal
     variables do not have a user scope, and the internal scope of user
     variables will be set when the user scopes are imported. */
  assert (!var->scope);
  assert (!var->user_scope);
  /* Handle free variables properly: a free variable has no user
     scope, i.e. '!var_is_internal && scope->is_internal' in this
     case. */
  if (!is_var_internal && !scope->is_internal)
    var->user_scope = scope;
  else
    var->scope = scope;

  assert (!QDPLL_VAR_HAS_POS_OCCS (var));
  assert (!QDPLL_VAR_HAS_NEG_OCCS (var));
  assert (!QDPLL_VAR_HAS_POS_OCC_CUBES (var));
  assert (!QDPLL_VAR_HAS_NEG_OCC_CUBES (var));

  /* Add to scope */
  if (push_on_scope_vars_stack)
    {
      QDPLL_PUSH_STACK (mm, scope->vars, id);
      if (!scope->is_internal)
        {
          assert (QDPLL_COUNT_STACK(scope->vars) > 0);
          var->offset_in_user_scope_vars = (unsigned int)(QDPLL_COUNT_STACK(scope->vars) - 1);
        }
    }

  /* Inform DepMan that new variable has been declared and initialized. */
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  dm->notify_init_variable (dm, id);

  if (!is_var_internal && id > qdpll->pcnf.max_declared_user_var_id)
    qdpll->pcnf.max_declared_user_var_id = id;
}


/* Returns zero for successful completion. */
static char *
add_id_to_scope (QDPLL *qdpll, LitID id, Scope *scope, 
                 const int push_on_scope_vars_stack)
{
  assert (!scope->is_internal);
  char *result = 0;
  assert (id != 0);
  if (id < 0)
    result = "negative variable ID in scope!";
  else
    {
      qdpll_adjust_vars (qdpll, id);
      Var *vars = qdpll->pcnf.vars;
      if (vars[id].id != 0)
        {
          if (!vars[id].is_internal)
            result = "variable already quantified!";
          else
            result = "attempted to import internal variable!";
          /* Second case should never happen and corresponds to an
             internal error. The solver is responsible to handle internal
             variables. */
        }
      else
        declare_and_init_variable (qdpll, scope, id, 0, push_on_scope_vars_stack);
    }
  return result;
}


static Scope *
copy_scope (QDPLL *qdpll, Scope *s)
{
  Scope *result = (Scope *) qdpll_malloc (qdpll->mm, sizeof (Scope));
  result->type = s->type;
  result->nesting = s->nesting;
  result->is_internal = s->is_internal;

  VarID *p, *e;
  for (p = s->vars.start, e = s->vars.top; p < e; p++)
    QDPLL_PUSH_STACK(qdpll->mm, result->vars, *p);

  return result;
}


static void
import_user_scopes_internal_vars_aux (QDPLL *qdpll, VarIDStack *internal_ids)
{
  VarIDStack *stack = &qdpll->pcnf.scopes.first->vars; 
  VarID *p, *e;
  for (p = internal_ids->start, e = internal_ids->top; p < e; p++)
    {
      VarID id = *p;
      if (id)
        {
          assert (id < qdpll->pcnf.size_vars);
          assert (id >= qdpll->pcnf.size_user_vars);
          Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
          /* Bug fix: do not insert IDs of cleaned up no-occ internal vars into
             default scope. We keep such IDs on the stacks of current and popped off
             frames, just to maintain the relation between internal IDs and
             frames. */
          if (var->id)
            {
              assert (var->is_internal);
              QDPLL_PUSH_STACK(qdpll->mm, *stack, *p);
            }
        }
    }
}


/* Make the scopes in 'qdpll->pcnf.user_scopes' internal scopes, update the
   pointers to scopes in variables, delete old internal scope list in
   'qdpll->pcnf.scopes'. */
static void
import_user_scopes (QDPLL *qdpll)
{
  if (qdpll->state.no_scheduled_import_user_scopes)
    return;

#ifndef NDEBUG
  assert_full_prefix_integrity_user_scopes (qdpll);
#endif

  /* Prevent redundant future calls of this function by setting flag. */
  qdpll->state.no_scheduled_import_user_scopes = 1;

  /* Default internal scope must always exists. */
  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.last);
  assert (qdpll->pcnf.scopes.first->is_internal);
  assert (qdpll->pcnf.scopes.first->type == QDPLL_QTYPE_EXISTS);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);

  /* Keep free variables from input formula on variable stack of
     default internal scope. */
  VarIDStack free_vars;
  QDPLL_INIT_STACK(free_vars);
  VarID *p, *e;
  for (p = qdpll->pcnf.scopes.first->vars.start, 
         e = qdpll->pcnf.scopes.first->vars.top; p < e; p++)
    {
      VarID id = *p;
      Var *v = VARID2VARPTR(qdpll->pcnf.vars, id);
      assert (v->id);
      assert (v->scope == qdpll->pcnf.scopes.first);
      if (!v->is_internal && !v->user_scope)
        QDPLL_PUSH_STACK (qdpll->mm, free_vars, id);
    }
  /* Clean up variables in default internal scope; that scope might
     contain also user-variables which were merged into that scope
     during clean-up. */
  QDPLL_DELETE_STACK(qdpll->mm, qdpll->pcnf.scopes.first->vars);
  qdpll->pcnf.scopes.first->vars = free_vars;

  /* Copy user scopes in 'qdpll->pcnf.user_scopes' to be used as new
     list 'qdpll->pcnf.scopes'. */
  ScopeList copy_user_scopes = {0,0,0};
  Scope *us;
  for (us = qdpll->pcnf.user_scopes.first; us; us = us->link.next)
    {
      assert (!us->is_internal);
      Scope *copy = copy_scope (qdpll, us);
      assert (!copy->link.next);
      assert (!copy->link.prev);
      LINK_LAST (copy_user_scopes, copy, link);
      assert (!copy->is_internal);
      /* Scope 'copy' will appear in list 'qdpll->pcnf.scopes' of internal scopes later. */
      copy->is_internal = 1;
      /* Check variables in user scope 'us' and update their scope pointer;
         that pointer was set to a different scope previously (either through
         API or 'set_up_formula'). User-scopes might have been merged during
         clean-up, hence we must update the scope pointers of variables. */
      VarID *p, *e;
      for (p = us->vars.start, e = us->vars.top; p < e; p++)
        {
          VarID id = *p;
          Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
          assert (!var->is_internal);
          /* Re-declare variables which have been cleaned up internally
             because the user did not add clauses containing that
             variables. This is only relevant for incremental calls of the
             solver. */
          if (!var->id)
            {
              /* Assertion: 'qdpll_adjust_vars' is called from
                 'add_id_to_scope' but it will not enlarge the variable table
                 because this has been done previously at the time when the user
                 added 'id' through the API. */
              assert (id + 1 <= qdpll->pcnf.size_user_vars);
              /* Add variable to user-scope again but do not push it onto the
                 stack 'us->vars' since it is already there. */
              char *res = add_id_to_scope (qdpll, id, us, 0);
              assert (!var->offset_in_user_scope_vars);
              /* Set stack offset of previously reset variable. This is
                 normally done in 'add_id_to_scope' but 'var' is not pushed onto
                 the stack of scope vars above. */
              var->offset_in_user_scope_vars = (unsigned int)(p - us->vars.start);
              assert ((unsigned int)QDPLL_COUNT_STACK(us->vars) == 
                      (unsigned int)(e - us->vars.start));
              assert (e == us->vars.top);
              /* String 'res', if non-zero, is an error message and the solver will abort. */
              QDPLL_ABORT_QDPLL (res, "Importing user scope failed!");
            }
          /* Bug Fix: a subtle problem -- user might add the same ID multiple times to a user scope. */
          QDPLL_ABORT_QDPLL (var->offset_in_user_scope_vars != (unsigned int)(p - us->vars.start), 
                             "Variable is already declared!");
          assert (var->user_scope == us);
          /* Set scope pointer of 'var' to 'copy'. If the old scope pointed to
             is internal then it will be deleted. */
          assert (!var->scope || var->scope->is_internal);
          var->scope = copy;
        }
    }

  /* Delete old internal scopes in list 'qdpll->pcnf.scopes', if any, except
     the default scope. */
  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first->link.next; s; s = n)
    {
      assert (s->is_internal);
      assert (s->nesting > QDPLL_DEFAULT_SCOPE_NESTING);
      n = s->link.next;
      UNLINK (qdpll->pcnf.scopes, s, link);
      delete_scope (qdpll, s);
    }

  /* Must add internal variables to the default scope again. */
  import_user_scopes_internal_vars_aux (qdpll, &qdpll->state.cur_used_internal_vars);
  import_user_scopes_internal_vars_aux (qdpll, &qdpll->state.popped_off_internal_vars);

  /* Now 'qdpll->pcnf.scopes' contains only the default scope. */
  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.first == qdpll->pcnf.scopes.last);
  assert (qdpll->pcnf.scopes.first->is_internal);
  assert (qdpll->pcnf.scopes.first->type == QDPLL_QTYPE_EXISTS);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);

  /* The list 'copy_user_scopes' of copied user scopes becomes the new list of
     internal scopes. Append 'copy_user_scopes' to 'qdpll->pcnf.scopes'. */
  if (copy_user_scopes.first)
    {
      assert (copy_user_scopes.last);
      qdpll->pcnf.scopes.last = copy_user_scopes.last;
      assert (!qdpll->pcnf.scopes.first->link.next);
      qdpll->pcnf.scopes.first->link.next = copy_user_scopes.first;
      assert (!copy_user_scopes.first->link.prev);
      copy_user_scopes.first->link.prev = qdpll->pcnf.scopes.first;
      assert (qdpll->pcnf.scopes.cnt == 1);
      qdpll->pcnf.scopes.cnt += copy_user_scopes.cnt;
      assert (qdpll->pcnf.scopes.cnt == qdpll->pcnf.scopes.last->nesting + 1);
      assert (!qdpll->pcnf.scopes.first->link.prev);
      assert (!qdpll->pcnf.scopes.last->link.next);
    }
#ifndef NDEBUG
  assert_full_prefix_integrity_user_scopes (qdpll);
#endif
}


/* Clean up formula and do initialization tasks:
   Remove no-occ variables and empty scopes, 
   merge scopes of same type into one scope.
*/
static void
set_up_formula (QDPLL * qdpll)
{
  /* Set flag to schedule import of user prefix in 'import_user_scopes'. */
  qdpll->state.no_scheduled_import_user_scopes = 0;
  import_user_scopes (qdpll);
  /* Reset dependencies to toggle a recomputation after the following cleanup operations. */
  qdpll_reset_deps (qdpll);
  /* Last parameter of 'clean_up_formula' indicates that we do not discard no
     occ variables from user prefix. */
  clean_up_formula (qdpll, 0);
  /* Import of user prefix must be rescheduled after 'cleanup'. */
  assert (!qdpll->state.no_scheduled_import_user_scopes);
#ifndef NDEBUG
  assert_full_prefix_integrity_user_scopes (qdpll);
  assert_full_prefix_integrity (qdpll);
#endif
}


static int
compare_lits_by_user_variable_nesting (QDPLL * qdpll, LitID lit1, LitID lit2)
{
  Var *vars = qdpll->pcnf.vars;
  VarID var_id1 = LIT2VARID (lit1);
  VarID var_id2 = LIT2VARID (lit2);
  Var *var1 = VARID2VARPTR (vars, var_id1);
  Var *var2 = VARID2VARPTR (vars, var_id2);

  /* Compare variables by user-scope nesting. Free variables do not
     have a user scope, hence compare by default scope nesting, which is
     zero. */
  assert (var1->user_scope || var1->scope);
  assert (var2->user_scope || var2->scope);
  assert (var1->user_scope || var1->scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  assert (var2->user_scope || var2->scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING);

  unsigned int nesting1;
  int var1_is_internal = var1->is_internal;
  unsigned int nesting2;
  int var2_is_internal = var2->is_internal;;

  if (var1->user_scope)
    {
      nesting1 = var1->user_scope->nesting;
      assert (!var1_is_internal);
    }
  else
    nesting1 = var1->scope->nesting;

  if (var2->user_scope)
    {
      nesting2 = var2->user_scope->nesting;
      assert (!var2_is_internal);
    }
  else
    nesting2 = var2->scope->nesting;

  if (nesting1 < nesting2)
    return -1;
  else if (nesting1 > nesting2)
    return 1;
  else
    {
      if ((!var1_is_internal && !var2_is_internal) || 
          (var1_is_internal && var2_is_internal))
        {
          if (var_id1 < var_id2)
            return -1;
          else if (var_id1 > var_id2)
            return 1;
          else
            return 0;
        }
      else if (var1_is_internal && !var2_is_internal)
        {
          return -1;
        }
      else 
        {
          assert (!var1_is_internal && var2_is_internal);
          return 1;
        }
    }
}


static void
unmark_constraint_variables (QDPLL * qdpll, Constraint * constr)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *end, lit;
  for (p = constr->lits, end = p + constr->num_lits; p < end; p++)
    QDPLL_VAR_UNMARK (LIT2VARPTR (vars, *p));
}


static int
qpup_res_is_var_marked (Var *var);

static void
qpup_res_reduce_by_depschemes (QDPLL *qdpll, LitIDStack *stack, 
                               const QDPLLQuantifierType type);

/* Apply simple existential/universal reduction by user-scopes nestings. */
static void
top_level_reduce_constraint_simple (QDPLL * qdpll, Constraint * c,
                             const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_EXISTS || type == QDPLL_QTYPE_FORALL);
  assert (type != QDPLL_QTYPE_FORALL || c->is_cube);
  assert (type != QDPLL_QTYPE_EXISTS || !c->is_cube);
#ifndef NDEBUG
  assert_lits_sorted (qdpll, c->lits, c->lits + c->num_lits);
#endif
  Var *vars = qdpll->pcnf.vars;
  LitID lit, *p, *e;
  for (e = c->lits, p = e + c->num_lits - 1; p >= e; p--)
    {
      lit = *p;
      Var *v = LIT2VARPTR (vars, lit);
      assert (!(v->scope && v->user_scope) || 
              v->scope->type == v->user_scope->type);
      if (!v->is_internal && 
          ((v->user_scope && v->user_scope->type != type) || 
          (v->scope && v->scope->type != type)))
        c->num_lits--;
      else
        break;
    }

#ifndef NDEBUG
  Var *tmp = LIT2VARPTR (vars, c->lits[c->num_lits - 1]);
  assert (c->num_lits == 0 || tmp->is_internal || 
          (tmp->scope && tmp->scope->type == type) || 
          (tmp->user_scope && tmp->user_scope->type == type));
#endif
}



/* Check clause for multiple, complementary literals and universal-reduction.
   Returns 'NULL' if clause is not tautological, 
   otherwise returns pointer to tautological clause. 
*/
static Constraint *
cleanup_constraint (QDPLL * qdpll, Constraint * constr)
{
  assert (!constr->is_cube);
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *end, *last, lit;
  for (p = constr->lits, end = p + constr->num_lits, last = end - 1;
       p < end; p++)
    {
      lit = *p;
      assert (lit != 0);
      Var *var = LIT2VARPTR (vars, lit);
      if (!QDPLL_VAR_MARKED (var))
        {
          if (lit < 0)
            QDPLL_VAR_NEG_MARK (var);
          else
            QDPLL_VAR_POS_MARK (var);
        }
      else if ((QDPLL_VAR_POS_MARKED (var) && lit < 0) ||
               (QDPLL_VAR_NEG_MARKED (var) && lit > 0))
        {                       
          /* Constr is tautological */
          unmark_constraint_variables (qdpll, constr);
          return constr;
        }
      else
        {                       
          /* Constr contains multiple literals */
          assert ((QDPLL_VAR_POS_MARKED (var) && lit > 0) ||
                  (QDPLL_VAR_NEG_MARKED (var) && lit < 0));
          *p-- = *last;
          /* Clean old slot of moved literal. */
          *last-- = 0;
          end--;
          constr->num_lits--;
        }
    }

  unmark_constraint_variables (qdpll, constr);
  QDPLL_SORT (qdpll, int, compare_lits_by_user_variable_nesting, constr->lits,
              constr->num_lits);

  unsigned int num_lits_before_red = constr->num_lits;

  /* Apply simple universal/existential reduction. */
  top_level_reduce_constraint_simple (qdpll, constr, QDPLL_QTYPE_EXISTS);
  
  /* This function is supposed to be called on original, user-given constraints only. */
  assert (!constr->learnt);

  if (qdpll->options.trace)
    {
      if (constr->num_lits < num_lits_before_red)
        {
          /* Constr was reduced; add and trace explicit reduction step. */
          assert (constr->id == (qdpll->cur_constraint_id));
          /* Trace constr before reduction. */
          qdpll->trace_constraint (constr->id,
                                   constr->lits, num_lits_before_red, 0, 0);
          unsigned int old_constr_id = constr->id;
          constr->id = ++qdpll->cur_constraint_id;
          assert (constr->id == old_constr_id + 1);
          assert (qdpll->cur_constraint_id == constr->id);
          /* Trace reduction step, using new ID of reduced constr. */
          qdpll->trace_constraint (constr->id,
                                   constr->lits, constr->num_lits, old_constr_id, 0);
        }
      else
        {
          /* Constr unchanged, trace original constr as is. */
          assert (constr->num_lits == num_lits_before_red);
          qdpll->trace_constraint (constr->id, constr->lits, constr->num_lits, 0, 0);
        }
    }

  return 0;
}

static void increase_var_activity (QDPLL * qdpll, Var * var, Scope *s);

static void
qbcp_qbce_setup_first_call_aux (QDPLL *qdpll, Constraint *c)
{
#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_clauses_seen++;
#endif
  /* This function is supposed to be called only once and before watcher
     initialization. Hence no clause must be blocked or satisfied already. */
  assert (!c->qbcp_qbce_blocked);
  assert (!is_clause_satisfied (qdpll, c));
  assert (QDPLL_EMPTY_STACK (c->qbcp_qbce_notify_maybe_blocked_clauses));

  if (qdpll->options.qbcp_qbce_max_clause_size && 
      c->num_lits > qdpll->options.qbcp_qbce_max_clause_size)
    {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_ignored_clauses_by_size_limit++;
#endif
      if (qdpll->options.verbosity >= 3)
        {
          fprintf (stderr, "QBCE: skipping maybe blocked clause -- num-lits %d > limit %d: \n", 
                   c->num_lits, qdpll->options.qbcp_qbce_max_clause_size);
          print_constraint (qdpll, c);
        }
      return;
    }

  /* Set member 'non_blocking_literal' in 'pair' to 0 to indicate that we
     want to check every existential literal in 'c' if it is a blocking
     literal. */
  QBCENonBlockedWitness pair = {0, {c->num_lits > 0 ? c->lits[0] : 0, c}, 
                                {QDPLL_INVALID_WATCHER_POS}, 
                                QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses)};
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, pair);
}

/* Reschedule blocked-check for currently blocked clauses which contain a
   blocking literal 'l' and where newly added input clauses may make this
   clause non-blocked. Further, we use this function to reschedule checks if
   user provides assumptions. Assumptions may require reschedule of checks if
   a blocking literal is assigned as an assumptions, for example. See also
   function 'qdpll_assume'. */
static void
qbcp_qbce_reschedule_from_exists_var (QDPLL *qdpll, Var *var, LitID lit)
{
  /* Function must be called only if we apply any variant of QBCE. */
  assert (qdpll->options.qbce_preprocessing || 
          qdpll->options.qbce_inprocessing || 
          !qdpll->options.no_qbce_dynamic);
  assert (QDPLL_VAR_EXISTS (var) && !var->is_internal);
  /* If a variable 'v' does not have clauses where a literal of
     'v' is the blocking literal, then there is no need to collect
     them. */
  if (QDPLL_COUNT_STACK (var->qbcp_qbce_prepro_pos_blocking_lit_clauses) != 0 || 
      QDPLL_COUNT_STACK (var->qbcp_qbce_prepro_neg_blocking_lit_clauses) != 0)
    {
      if (!var->neg_lit_in_new_input_clause && 
          !var->pos_lit_in_new_input_clause)
        QDPLL_PUSH_STACK 
          (qdpll->mm, qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses, var->id);
      if (QDPLL_LIT_NEG (lit))
        var->neg_lit_in_new_input_clause = 1;
      else            
        var->pos_lit_in_new_input_clause = 1;
    }
}

/* Push constraint given through API on constraint stack, update occ_lists if
   needed. */
static void
import_original_constraint (QDPLL * qdpll, Constraint * constr)
{
  assert (!constr->is_cube);
  assert (!constr->learnt);
  const unsigned int qbce_enabled = 
    qdpll->options.qbce_preprocessing || 
    qdpll->options.qbce_inprocessing || 
    !qdpll->options.no_qbce_dynamic;
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses));
  const unsigned int qbce_blocked_input_clauses_present = 
    QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]);
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  if (!constr->is_cube)
    {
      LINK_LAST (qdpll->pcnf.clauses, constr, link);
      if (!qdpll->options.no_empty_formula_watching)
        {
          /* Store pair of clause and one of its literals for better cache performance. */
          BLitsOcc occ = {constr->num_lits > 0 ? constr->lits[0] : 0, constr};
          QDPLL_PUSH_STACK (mm, qdpll->empty_formula_watching_blit_occs, occ);
          assert (qdpll->pcnf.clauses.cnt == 
                  (unsigned int) QDPLL_COUNT_STACK (qdpll->empty_formula_watching_blit_occs));
        }
      /* Set flag to enable cube-checking before solving. */
      qdpll->state.clauses_added_since_cube_check++;
      qdpll->state.pending_cubes_check = 1;
      /* Push pairs of clause and maybe blocking literals on QBCE working queue. */
      if (qbce_enabled)
        qbcp_qbce_setup_first_call_aux (qdpll, constr);
    }
  else 
    LINK_LAST (qdpll->pcnf.learnt_cubes, constr, link);
  assert (qdpll->pcnf.clauses.cnt ==
          count_constraints (&(qdpll->pcnf.clauses)));
  LitID *p, *end;
  for (p = constr->lits, end = p + constr->num_lits; p < end; p++)
    {
      LitID lit = *p;
      assert ((VarID) LIT2VARID (lit) < qdpll->pcnf.size_vars);
      Var *var = LIT2VARPTR (vars, lit);

      if (qbce_enabled && qbce_blocked_input_clauses_present && 
          QDPLL_VAR_EXISTS (var) && !var->is_internal)
        qbcp_qbce_reschedule_from_exists_var (qdpll, var, lit);

      if (!constr->is_cube)
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (constr->num_lits > var->longest_neg_occ_size)
                var->longest_neg_occ_size = constr->num_lits;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (constr->num_lits > var->longest_pos_occ_size)
                var->longest_pos_occ_size = constr->num_lits;
            }
        }
      /* FIX: Increase variable priority. */
      increase_var_activity (qdpll, var, var->user_scope ? var->user_scope : var->scope);
      BLitsOcc blit = {lit, constr};
      /* Add all literals to occurrence stacks. */
      if (QDPLL_LIT_NEG (lit))
        QDPLL_PUSH_STACK (mm, var->neg_occ_clauses, blit);
      else
        QDPLL_PUSH_STACK (mm, var->pos_occ_clauses, blit);
    }
}


static Constraint *
create_constraint (QDPLL * qdpll, unsigned int num_lits, int is_cube)
{
  QDPLLMemMan *mm = qdpll->mm;
  Constraint *result = qdpll_malloc (mm,
                                     sizeof (Constraint) +
                                     num_lits * sizeof (LitID));
  result->id = ++(qdpll->cur_constraint_id);
  result->size_lits = num_lits;
  result->is_cube = is_cube;
  result->num_lits = num_lits;
  result->rwatcher_pos = result->lwatcher_pos = QDPLL_INVALID_WATCHER_POS;
  return result;
}


static void
delete_constraint (QDPLL * qdpll, Constraint * constraint)
{
  QDPLLMemMan *mm = qdpll->mm;
  QDPLL_DELETE_STACK (mm, constraint->qbcp_qbce_notify_maybe_blocked_clauses);
  QDPLL_DELETE_STACK (mm, constraint->qbcp_qbce_witness_clauses);
  QDPLL_DELETE_STACK (mm, constraint->qbcp_qbce_offset_of_witness_in_watched_occs);
  qdpll_free (mm, constraint,
              sizeof (Constraint) + constraint->size_lits * sizeof (LitID));
}


/* Add literals/variables to clause or scope */
static const char *
import_added_ids (QDPLL * qdpll)
{
  LitIDStack *add_stack = &(qdpll->add_stack);
  LitID id;
  LitID *sp = add_stack->start, *se = add_stack->top;

  /* Fix: call 'adjust_vars' once before starting to add parsed literals to
     new constraint or scope. Before, we adjusted the variables on demand
     while adding the literals to the constraint. This can cause problems in
     incremental mode as the renaming of internal variables is not done for
     the constraint that is currently being imported. Also, we avoid
     unnecessary resizing operations. */
  qdpll_adjust_vars (qdpll, qdpll->max_var_id_on_add_stack);

  if (qdpll->state.scope_opened)
    { 
      /* Schedule the import of user prefix next time 'import_user_scopes' is
         called. */
      qdpll->state.no_scheduled_import_user_scopes = 0;
                         
      /* Import scope's variables: the scope 'qdpll->state.scope_opened_ptr'
         has been opened by a previous call of 'qdpll_new_scope' or
         'qdpll_new_scope_at_nesting'. */
      Scope *scope = qdpll->state.scope_opened_ptr;
      assert (scope);
      /* The opened scope must not be internal, i.e. it was added by the user
         through the API. */
      assert (!scope->is_internal);

      while (sp < se)
        {
          id = *sp++;
          char *res = add_id_to_scope (qdpll, id, scope, 1);
          /* String 'res', if non-zero, is an error message and the solver will abort. */
          if (res)
            return res;
        }

      if (qdpll->options.trace)
        qdpll->trace_scope (scope);

      qdpll->state.scope_opened = 0;
      qdpll->state.scope_opened_ptr = 0;
    }
  else
    {
      /* Import clause's literals */
      unsigned int num_lits = QDPLL_COUNT_STACK (*add_stack);
      /* For incremental solving: add space to add selector variable. */
      if (qdpll->state.cur_open_group_id > 0)
        num_lits++;
      Constraint *constr = create_constraint (qdpll, num_lits, 0);
      LitID *p = constr->lits;

      /* For incremental solving: add literal of selector variable. */
      if (qdpll->state.cur_open_group_id > 0)
        {
          assert (qdpll->state.cnt_created_clause_groups > 0);
          assert (qdpll->state.cur_open_group_id <= 
                  QDPLL_COUNT_STACK (qdpll->state.cur_used_internal_vars));
          assert (qdpll->state.cnt_created_clause_groups <= 
                  QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));
          assert (qdpll->state.cur_used_internal_vars.start < 
                  qdpll->state.cur_used_internal_vars.top);
          VarID internal_id = *(qdpll->state.cur_used_internal_vars.start + 
                                (qdpll->state.cur_open_group_id - 1));
          assert (internal_id);
          Var *internal_var = VARID2VARPTR(qdpll->pcnf.vars, internal_id);
          assert (internal_var->is_internal && internal_var >= 
                  qdpll->pcnf.vars + qdpll->pcnf.size_user_vars);
          assert (internal_var->clause_group_id == qdpll->state.cur_open_group_id);
          /* Always add positive literal of selector variable. */
          *p++ = internal_id;
        }

      /* First, add lits to constraint, do NOT yet update occ-stacks. 
         NOTE: if clause is redundant, then might get vars which have no occs. */
      while (sp < se)
        {
          id = *sp++;
          assert (id != 0);
          VarID var_id = LIT2VARID (id);
          Var *var = qdpll->pcnf.vars + var_id;

          if (var->id == 0)
            {
              /* The following error must be avoided by the solver, not by the user. */
              if (var->is_internal || var >= qdpll->pcnf.vars + qdpll->pcnf.size_user_vars)
                return "attempted to import internal variable!";
              /* Declare var; (Q)DIMACS backward compatibility, i.e. put free
                 variables in an existential block which is leftmost. */
              Scope *scope = qdpll->pcnf.scopes.first;
              assert (scope);
              assert (scope->is_internal);
              assert (QDPLL_SCOPE_EXISTS (scope));
              assert (scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
              declare_and_init_variable (qdpll, scope, var_id, 0, 1);
              /* Reset dependency manager since the prefix was modified. */
            }
          assert (p < constr->lits + constr->num_lits);
          /* Add lits to constraint. */
          *p++ = id;            
        }

      /* Next, sort and clean up clause, then update occ-stacks */
      if (!cleanup_constraint (qdpll, constr))
        {
          import_original_constraint (qdpll, constr);
          assert (!constr->learnt);
        }
      else                      /* Constraint is tautological -> delete */
        delete_constraint (qdpll, constr);
    }

  qdpll->max_var_id_on_add_stack = 0;
  QDPLL_RESET_STACK (*add_stack);
  return 0;
}


/* ----- START: CUBE-FUNCTIONS ----- */

static int
has_variable_active_occs_in_cubes (QDPLL * qdpll, Var * var,
                                   BLitsOccStack * occ_cubes)
{
  if (QDPLL_VAR_ASSIGNED (var) /* && QDPLL_VAR_MARKED_PROPAGATED (var) */ )
    return 0;

  LitID lit = occ_cubes == &(var->neg_occ_cubes) ? -var->id : var->id;

  BLitsOcc *bp, *be;
  for (bp = occ_cubes->start, be = occ_cubes->top; bp < be; bp++)
    {
      assert (!is_cube_satisfied (qdpll, BLIT_STRIP_PTR (bp->constraint)));
      if (!is_cube_empty (qdpll, BLIT_STRIP_PTR (bp->constraint)))
        return 1;
    }

  return 0;
}


/* Variable 'var' was identified as pure in clauses. Check if this is
   also the case in learnt cubes. */
static int
is_var_pure_in_cubes (QDPLL * qdpll, Var * var,
                      const QDPLLAssignment implied_value)
{
  if (QDPLL_SCOPE_FORALL (var->scope))
    {
      if (implied_value == QDPLL_ASSIGNMENT_TRUE)
        {
          if (has_variable_active_occs_in_cubes
              (qdpll, var, &(var->pos_occ_cubes)))
            return 0;
        }
      else
        {
          if (has_variable_active_occs_in_cubes
              (qdpll, var, &(var->neg_occ_cubes)))
            return 0;
        }
    }
  else
    {
      assert (QDPLL_SCOPE_EXISTS (var->scope));
      if (implied_value == QDPLL_ASSIGNMENT_TRUE)
        {
          if (has_variable_active_occs_in_cubes
              (qdpll, var, &(var->neg_occ_cubes)))
            return 0;
        }
      else
        {
          if (has_variable_active_occs_in_cubes
              (qdpll, var, &(var->pos_occ_cubes)))
            return 0;
        }
    }
  return 1;
}


/* ----- END: CUBE-FUNCTIONS ----- */

static void
qbcp_qbce_init_stack_of_stacks_of_next_dec_level (QDPLL *qdpll, 
                                                  ConstraintPtrStackStack *stack)
{
  ConstraintPtrStack cstack;
  if (QDPLL_FULL_STACK (*stack))
    QDPLL_INIT_STACK (cstack);
  else
    {
      /* Reuse already present stack, which avoids malloc/free operations
         during backtracking and decision making. */
      assert (stack->top < stack->end);
      cstack = *(stack->top);
    }
  assert (QDPLL_EMPTY_STACK (cstack));
  QDPLL_PUSH_STACK (qdpll->mm, *stack, cstack);
}

static void
push_assigned_variable (QDPLL * qdpll, Var * var, QDPLLAssignment assignment,
                        QDPLLVarMode mode)
{
  assert (var->id);
  assert (mode > 0 && mode <= 5);
  assert (mode != QDPLL_VARMODE_UNDEF);
  assert (assignment != QDPLL_ASSIGNMENT_UNDEF);
  assert (var->assignment == QDPLL_ASSIGNMENT_UNDEF);
  assert (var->mode == QDPLL_VARMODE_UNDEF);
  assert (!QDPLL_VAR_ASSIGNED (var));
  assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
  assert (var->decision_level == QDPLL_INVALID_DECISION_LEVEL);

  /* An internal variable must only be assigned by assumptions. */
  assert (!var->is_internal || mode == QDPLL_VARMODE_ASSUMED);
  /* Assumptions must be assigned at decision level 0 only. */
  assert (mode != QDPLL_VARMODE_ASSUMED || qdpll->state.decision_level == 0);

#if COMPUTE_STATS
  qdpll->stats.pushed_assignments++;

  if (mode == QDPLL_VARMODE_UNIT)
    {
      qdpll->stats.pushed_unit_literals++;
      if (qdpll->state.decision_level == 0)
        qdpll->stats.pushed_top_unit_literals++;
      if (QDPLL_SCOPE_FORALL (var->scope))
        qdpll->stats.pushed_univ_unit_literals++;
    }
  else if (mode == QDPLL_VARMODE_PURE)
    {
      qdpll->stats.pushed_pure_literals++;
      if (qdpll->state.decision_level == 0)
        qdpll->stats.pushed_top_pure_literals++;
    }

  if (var->cached_assignment == -assignment)
    {
      qdpll->stats.assignment_flips++;
    }
#endif

  if ((QDPLL_SCOPE_EXISTS (var->scope) && !qdpll->options.no_exists_cache) ||
      (QDPLL_SCOPE_FORALL (var->scope) && !qdpll->options.no_univ_cache))
    var->cached_assignment = assignment;

  var->mode = mode;
  var->assignment = assignment;

  if (!qdpll->options.no_empty_formula_watching)
    {
      /* If the current assignment satisfies the clause being watched for empty
         formula detection, then schedule a watcher update. */
      if ((var->empty_formula_watcher_pos_occ && QDPLL_VAR_ASSIGNED_TRUE (var)) || 
          (var->empty_formula_watcher_neg_occ && QDPLL_VAR_ASSIGNED_FALSE (var)))
        qdpll->state.empty_formula_watcher_scheduled_update = 1;
    }

  assert (!(QDPLL_SCOPE_EXISTS (var->scope) && mode == QDPLL_VARMODE_UNIT)
          || (var->antecedent && !var->antecedent->is_cube));
  assert (!(var->antecedent && !var->antecedent->is_cube)
          || (QDPLL_SCOPE_EXISTS (var->scope) && mode == QDPLL_VARMODE_UNIT));
  assert (!(QDPLL_SCOPE_FORALL (var->scope) && mode == QDPLL_VARMODE_UNIT)
          || (var->antecedent && var->antecedent->is_cube));
  assert (!(var->antecedent && var->antecedent->is_cube)
          || (QDPLL_SCOPE_FORALL (var->scope) && mode == QDPLL_VARMODE_UNIT));
  assert (!var->antecedent || var->antecedent->is_reason);

  if (mode < 3 || mode == QDPLL_VARMODE_ASSUMED)
    {
      assert (mode == QDPLL_VARMODE_UNIT || mode == QDPLL_VARMODE_PURE || 
              mode == QDPLL_VARMODE_ASSUMED);
      var->decision_level = qdpll->state.decision_level;
    }
  else
    {
      assert (mode == QDPLL_VARMODE_LBRANCH || mode == QDPLL_VARMODE_RBRANCH);
      assert ((unsigned int) QDPLL_COUNT_STACK (qdpll->dec_vars) ==
              qdpll->state.decision_level);

      if (!qdpll->options.no_qbce_dynamic)
        {
          assert (qdpll->options.no_empty_formula_watching || 
                  qdpll->empty_formula_watcher);
          assert (qdpll->options.no_empty_formula_watching || 
                  !qdpll->empty_formula_watcher->constraint->qbcp_qbce_blocked);
          /* Initialize stack of blocked clauses found at next decision level. */
          assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 
                  qdpll->state.decision_level + 2);
          qbcp_qbce_init_stack_of_stacks_of_next_dec_level 
            (qdpll, &qdpll->qbcp_qbce_blocked_clauses);
          /* Initialize stack of marked clauses found at next decision level. */
          assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 
                  qdpll->state.decision_level + 1);
          qbcp_qbce_init_stack_of_stacks_of_next_dec_level 
            (qdpll, &qdpll->qbcp_qbce_marked_clauses);
        }

      if (!qdpll->options.no_empty_formula_watching)
        {
          assert (qdpll->empty_formula_watcher);
          assert (!qdpll->empty_formula_watcher->constraint->qbcp_qbce_blocked);
          assert (QDPLL_COUNT_STACK 
                  (qdpll->empty_formula_watchers_per_dec_level) == 
                  qdpll->state.decision_level);
          QDPLL_PUSH_STACK (qdpll->mm, qdpll->empty_formula_watchers_per_dec_level, 
                            qdpll->empty_formula_watcher);
        }

      var->decision_level = ++qdpll->state.decision_level;
      QDPLL_PUSH_STACK (qdpll->mm, qdpll->dec_vars, var->id);
      assert (qdpll->dec_vars.start[qdpll->state.decision_level - 1] ==
              var->id);
    }

  if (qdpll->options.qbce_inprocessing || !qdpll->options.no_qbce_dynamic)
    {
    }


#ifndef NDEBUG
#if QDPLL_ASSERT_FIND_IN_ASSIGNED_VARS
  assert (!find_in_assigned_vars (qdpll, var->id));
#endif
#endif

  /* Variable will be assigned in during BCP. */
  push_assigned_vars (qdpll, var->id);
  
  if (qdpll->options.verbosity > 1)
    {
      fprintf (stderr,
               "push assigned var.: id=%d, type=%c(%d), dlevel=%d, val=%d, mode=%d\n",
               var->id, QDPLL_SCOPE_EXISTS (var->scope) ? 'E' : 'A',
               var->scope->nesting, var->decision_level, var->assignment,
               var->mode);
    }
#ifndef NDEBUG
#if QDPLL_ASSERT_PUSHED_PURE_LITS
  if (mode == QDPLL_VARMODE_PURE)
    assert_pushed_pure_lits (qdpll);
#endif
#endif
}


/* ------------ START: INEFFICIENT UNIT/PURE LITERAL DETECTION ------------ */

static int
has_variable_active_occs_in_clauses (QDPLL * qdpll, Var * var,
                                     BLitsOccStack * occ_clauses,
                                     const int check_prop)
{
  assert (!check_prop);
  if (QDPLL_VAR_ASSIGNED (var))
    return 0;

  LitID lit = occ_clauses == &(var->neg_occ_clauses) ? -var->id : var->id;

  BLitsOcc *bp, *be;
  for (bp = occ_clauses->start, be = occ_clauses->top; bp < be; bp++)
    {
      if (BLIT_STRIP_PTR (bp->constraint)->qbcp_qbce_blocked)
        continue;
      assert (!BLIT_STRIP_PTR (bp->constraint)->is_cube);
      /* Assertion need NOT hold when bcp is NOT saturated. */
      assert (qdpll->bcp_ptr != qdpll->assigned_vars_top
              || !is_clause_empty (qdpll, BLIT_STRIP_PTR (bp->constraint)));

      if ((!check_prop
           && !is_clause_satisfied (qdpll, BLIT_STRIP_PTR (bp->constraint)))
          || (check_prop
              && !is_clause_satisfied_by_prop_var (qdpll,
                                                   BLIT_STRIP_PTR (bp->
                                                                   constraint))))
        return 1;
    }

  return 0;
}

/* ------------ END: INEFFICIENT UNIT/PURE LITERAL DETECTION ------------ */


/* -------------------- START: LEARNING -------------------- */

/* Returns the number of existential literals 
   at 'level' in the working clause. */
static unsigned int
count_type_lit_at_dec_level (QDPLL * qdpll, LitID * lit_start,
                             LitID * lit_end, unsigned int level,
                             const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (lit_start < lit_end);
  assert (level != QDPLL_INVALID_DECISION_LEVEL);
  return qdpll->cnt_hi_dl_type_lits;
}


/* Assumes that clause is sorted. */
static unsigned int
get_reason_asserting_level (QDPLL * qdpll, LitID * lit_start, LitID * lit_end,
                            Var * implied_var, const QDPLLQuantifierType type)
{
  assert (lit_start < lit_end);
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (type == implied_var->scope->type);
  Var *vars = qdpll->pcnf.vars;
  unsigned int level, highest = 0, next_highest = 0;
  QDPLLDepManGeneric *dm = qdpll->dm;

  LitID *p, *e;
  for (e = lit_start, p = lit_end - 1; e <= p; p--)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      level = var->decision_level;

      if (type != var->scope->type
          && !dm->depends (dm, var->id, implied_var->id))
        continue;

      if (level > highest)
        {
          assert (level != QDPLL_INVALID_DECISION_LEVEL);
          next_highest = highest;
          highest = level;
        }
      else if (level > next_highest)
        {
          assert (level != QDPLL_INVALID_DECISION_LEVEL);
          next_highest = level;
        }
    }

  return next_highest;
}


/* Returns the highest decision level of a 
   'type'-literal in the working reason. */
static unsigned int
get_highest_type_lit_dec_level (QDPLL * qdpll, LitID * lit_start,
                                LitID * lit_end,
                                const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (lit_start < lit_end);
  return qdpll->hi_type_dl;
}


/* Returns variable at assigned at decision level 'level'. Note that
   the result is unique if, and only if function
   'count_exist_lit_at_dec_level' has returned 1 on that level. */
static Var *
get_type_var_at_dec_level (QDPLL * qdpll, LitID * lit_start, LitID * lit_end,
                           unsigned int level, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (lit_start < lit_end);
  return qdpll->hi_dl_type_var;
}


/* Re-link learnt constraint 'c' to the beginning of the set of learnt
   constraints. Constraints which are heavily used should appear at the
   front of that list. */
static void
learnt_constraint_mtf (QDPLL * qdpll, Constraint * c)
{
#if COMPUTE_STATS
  qdpll->stats.total_learnt_mtf_calls++;
#endif
  if (!c->learnt)
    return;
  if (c->is_cube)
    {
      UNLINK (qdpll->pcnf.learnt_cubes, c, link);
      LINK_FIRST (qdpll->pcnf.learnt_cubes, c, link);
#if COMPUTE_STATS
      qdpll->stats.total_learnt_cubes_mtfs++;
#endif
    }
  else
    {
      UNLINK (qdpll->pcnf.learnt_clauses, c, link);
      LINK_FIRST (qdpll->pcnf.learnt_clauses, c, link);
#if COMPUTE_STATS
      qdpll->stats.total_learnt_clauses_mtfs++;
#endif
    }
}


/* We take the same magic numbers as in Minisat... */
static void
decay_var_activity (QDPLL * qdpll)
{
  qdpll->state.var_act_inc *= qdpll->var_act_decay;
}


static void
increase_var_activity (QDPLL * qdpll, Var * var, Scope *s)
{
  assert (var->scope || var->user_scope);
  assert (var->scope == s || var->user_scope == s);
  assert (!var->scope || 1 + var->scope->nesting);
  assert (!var->user_scope || 1 + var->user_scope->nesting);
  var->priority +=
    (qdpll->state.var_act_inc *
     (1 + (qdpll->options.var_act_bias * (double) s->nesting) / 10));
  /* Print bump message suggested by AVG. */
  if (qdpll->options.verbosity >= 3)
    fprintf (stderr, "BUMP: %d to %f\n", var->id, var->priority);
  if (var->priority > 1e100)
    {
#if COMPUTE_STATS
      qdpll->stats.total_var_act_rescales++;
#endif
      /* Scale down all variable activities. The heap order is not affected by that. */
      Var *p, *e;
      for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
        {
          if (p->id)
            p->priority *= 1e-100;
        }
      qdpll->state.var_act_inc *= 1e-100;
    }

  if (var->priority_pos != QDPLL_INVALID_PQUEUE_POS)
    var_pqueue_increase_key (qdpll, var->id);
}


static void
reset_stop_crit_data (QDPLL * qdpll)
{
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));
  qdpll->cnt_hi_dl_type_lits = 0;
  qdpll->hi_dl_type_var = 0;
  qdpll->hi_type_dl = 0;
  QDPLL_RESET_STACK (qdpll->smaller_type_lits);
}


static void
update_stop_crit_data (QDPLL * qdpll, Var * vars, LitID lit,
                       const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_EXISTS || type == QDPLL_QTYPE_FORALL);
  QDPLLMemMan *mm = qdpll->mm;
  Var *var = LIT2VARPTR (vars, lit);
  const QDPLLQuantifierType var_type = var->scope->type;
  if (var_type == type)
    {
      unsigned int cur_dl = var->decision_level;
      if (cur_dl > qdpll->hi_type_dl || !qdpll->hi_dl_type_var)
        {
          qdpll->hi_type_dl = cur_dl;
          qdpll->cnt_hi_dl_type_lits = 1;
          qdpll->hi_dl_type_var = var;
        }
      else if (cur_dl == qdpll->hi_type_dl)
        {
          assert (qdpll->hi_dl_type_var);
          assert (qdpll->hi_type_dl == qdpll->hi_dl_type_var->decision_level);
          qdpll->cnt_hi_dl_type_lits++;
        }
    }
  else
    {
      /* Collect literals of other type which potentially violate
         stop-crit. in the end. */
      if (!QDPLL_VAR_ASSIGNED (var)
          || var->decision_level >= qdpll->hi_type_dl
          ||
          ((type == QDPLL_QTYPE_FORALL
            && ((QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_NEG (lit))
                || (QDPLL_VAR_ASSIGNED_TRUE (var) && QDPLL_LIT_POS (lit))))
           || (type == QDPLL_QTYPE_EXISTS
               && ((QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_POS (lit))
                   || (QDPLL_VAR_ASSIGNED_TRUE (var)
                       && QDPLL_LIT_NEG (lit))))))
        QDPLL_PUSH_STACK (mm, qdpll->smaller_type_lits, lit);
    }

  /* Note: when using simple dep-man, then need not collect data for
     type-reduce. In fact, if we collect it then we must also properly
     unmark variables etc., which is not done at the moment. */

  if (!qdpll->options.depman_simple)
    {
      /* Update data for type-reduce. */
      assert (qdpll->state.decision_level != 0 || var->decision_level == 0 ||
              var->decision_level == QDPLL_INVALID_DECISION_LEVEL);
      assert (LEARN_VAR_MARKED (var));
      assert (QDPLL_LIT_POS (lit) || LEARN_VAR_NEG_MARKED (var));
      assert (QDPLL_LIT_NEG (lit) || LEARN_VAR_POS_MARKED (var));
      assert (!(LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var)) || 
	      qdpll->options.long_dist_res);
      if (var_type == QDPLL_QTYPE_FORALL)
        {
          Var *rep = VARID2VARPTR (vars,
                                   qdpll->dm->get_class_rep (qdpll->dm,
                                                             var->id, 0));
          if (!QDPLL_VAR_POS_MARKED (rep))
            {
              QDPLL_VAR_POS_MARK (rep);
              assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) == 0);
              QDPLL_PUSH_STACK (mm, qdpll->wreason_a, rep);
            }
          /* Collect class members. */
          QDPLL_PUSH_STACK (mm, rep->type_red_member_lits, lit);
        }
      else
        {
          /* NOTE: here 'type == EXISTS' means that we do CDCL and
             hence must forall-reduce clauses, and 'type == FORALL'
             indicates SDCL and exists-reducing cubes. Must collect
             clauses accordingly. */
          Var *rep = type == QDPLL_QTYPE_FORALL ? VARID2VARPTR (vars,
                                                                qdpll->dm->
                                                                get_class_rep
                                                                (qdpll->dm,
                                                                 var->id,
                                                                 1)) :
            VARID2VARPTR (vars,
                          qdpll->dm->get_class_rep (qdpll->dm, var->id, 0));
          if (!QDPLL_VAR_POS_MARKED (rep))
            {
              QDPLL_VAR_POS_MARK (rep);
              assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) == 0);
              QDPLL_PUSH_STACK (mm, qdpll->wreason_e, rep);
            }
          /* Collect class members. */
          QDPLL_PUSH_STACK (mm, rep->type_red_member_lits, lit);
        }
    }
}


static void
cover_by_clauses_collect_lit (QDPLL * qdpll, QDPLLMemMan * mm,
                              Var * var, LitID lit)
{
  assert (var);
  assert (lit);
  assert (LIT2VARPTR(qdpll->pcnf.vars, lit) == var);
  assert (qdpll->state.collect_full_cover_sets || !qdpll->options.no_qbce_dynamic ||
	  qdpll->state.sat_branch_detected || 
          qdpll->pcnf.user_scopes.last != var->user_scope);
  assert (qdpll->state.collect_full_cover_sets || !qdpll->options.no_qbce_dynamic || 
          qdpll->state.sat_branch_detected ||
          qdpll->pcnf.scopes.last != var->scope);
  assert ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)));
  assert (!LEARN_VAR_MARKED (var));
  if (QDPLL_LIT_POS (lit))
    LEARN_VAR_POS_MARK (var);
  else
    LEARN_VAR_NEG_MARK (var);
  if (var->is_internal)
    QDPLL_PUSH_STACK (mm, qdpll->internal_cover_lits, lit);
  else if (var->user_scope)
    QDPLL_PUSH_STACK (mm, var->user_scope->cover_lits, lit);
  else
    {
      assert (var->scope && var->scope == qdpll->pcnf.scopes.first);
      QDPLL_PUSH_STACK (mm, var->scope->cover_lits, lit);
    }
}


static void
cover_by_clauses_collect_lits_sorted_aux (QDPLL * qdpll, QDPLLMemMan * mm,
                                          LitIDStack * lit_stack, LitIDStack * cover_lits)
{
  LitID *p, *e;
  for (p = cover_lits->start, e = cover_lits->top; p < e; p++)
    {
      LitID lit = *p;
      Var *v = LIT2VARPTR (qdpll->pcnf.vars, lit);
      assert (LEARN_VAR_MARKED (v));
      assert ((QDPLL_VAR_ASSIGNED_TRUE (v) && LEARN_VAR_POS_MARKED (v)) ||
              (QDPLL_VAR_ASSIGNED_FALSE (v) && LEARN_VAR_NEG_MARKED (v)));
      assert (cover_lits == &qdpll->internal_cover_lits || !v->is_internal);
      assert (cover_lits != &qdpll->internal_cover_lits || v->is_internal);
      update_stop_crit_data (qdpll, qdpll->pcnf.vars, lit, QDPLL_QTYPE_FORALL);
      QDPLL_PUSH_STACK (mm, *lit_stack, lit);
    }
  QDPLL_RESET_STACK (*cover_lits);
}


/* Collect cover-lits already in-order by traversing scopes. This
   avoids possibly expensive sorting of cube-literals. */
static void
cover_by_clauses_collect_lits_sorted (QDPLL * qdpll, QDPLLMemMan * mm,
                                      LitIDStack * lit_stack)
{
  /* Data for stop-crit and type-reduce must be reset and will be
     initialized here. */
  assert (qdpll->cnt_hi_dl_type_lits == 0);
  assert (qdpll->hi_dl_type_var == 0);
  assert (qdpll->hi_type_dl == 0);
  assert (QDPLL_EMPTY_STACK (qdpll->smaller_type_lits));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));
  Var *vars = qdpll->pcnf.vars;

  assert (QDPLL_EMPTY_STACK (*lit_stack));

  /* First import internal variables collected at separate stack. Separate
     collection is necessary to make internal literals appear at the left end of
     constraint literal lists. */
  cover_by_clauses_collect_lits_sorted_aux (qdpll, mm,
                                            lit_stack, &qdpll->internal_cover_lits);

  /* Then collect variables added to the default scope. */
  cover_by_clauses_collect_lits_sorted_aux (qdpll, mm,
                                            lit_stack, &qdpll->pcnf.scopes.first->cover_lits);
#ifndef NDEBUG
  if (!qdpll->state.collect_full_cover_sets)
    {
      if (qdpll->options.no_qbce_dynamic && 
	  !qdpll->state.sat_branch_detected)
        {
          /* No literal is marked in innermost scope, since that
             literals would be immediately removed by type-reduce. */
          assert (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.last));
          assert (QDPLL_EMPTY_STACK (qdpll->pcnf.scopes.last->cover_lits));
          do
            {
              VarID *p, *e;
              for (p = qdpll->pcnf.scopes.last->vars.start, 
                     e = qdpll->pcnf.scopes.last->vars.top; p < e; p++)
                {
                  Var *v = VARID2VARPTR (vars, *p);
                  assert (!LEARN_VAR_MARKED (v));
                }
            }
          while (0);
        }
    }
#endif

  /* Re-collect all marked literals by traversing all scopes from
     outer- to innermost. Marked literals can then be collected in scope
     order, thus explicit sorting can be avoided. */
  Scope *s;
  for (s = qdpll->pcnf.user_scopes.first; s; s = s->link.next)
    cover_by_clauses_collect_lits_sorted_aux (qdpll, mm,
                                              lit_stack, &s->cover_lits);
#ifndef NDEBUG
  assert_lits_sorted (qdpll, lit_stack->start, lit_stack->top);
#endif
}

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS

/* Check if the original ocurrence 'c' of 'univ_var' is blocked or is
   satisfied by a collected variable other than 'univ_var', which we
   want to eliminate. */
static int
cover_by_assignment_is_univ_var_orig_occ_covered (QDPLL *qdpll, 
                                                  Var *univ_var, 
                                                  Constraint *c)
{
  assert (!c->is_cube);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "  cover-by-assignment: checking original occurrence ");
      print_constraint (qdpll, c);
      if (c->qbcp_qbce_blocked)
        fprintf (stderr, "  ...which is blocked\n");
    }

  /* Ignore blocked occurrences. */
  if (c->qbcp_qbce_blocked)
    return 1;

  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    { 
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Check if a collected variable satisfies 'c'. */
      if (var != univ_var && LEARN_VAR_MARKED (var) && 
          ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
           (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var))))
        {
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "  ...which is satisfied by collected literal\n");
          return 1;
        }
    }

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "  ...which is neither blocked no satisfied by collected literal\n");

  return 0;
}


static int
cover_by_assignment_check_blocked_clauses_aux 
(QDPLL *qdpll, Var *univ_var, Constraint *blocked_clause)
{
  assert (QDPLL_VAR_FORALL (univ_var));
  assert (blocked_clause->qbcp_qbce_blocked);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "  cover-by-assignment: checking blocked clause ");
      print_constraint (qdpll, blocked_clause);
    }

  /* Check if 'blocked_clause' is satisfied by collected variable. */
  LitID *p, *e;
  for (p = blocked_clause->lits, 
         e = p + blocked_clause->num_lits; p < e; p++)
    { 
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Check if a collected variable satisfies 'c'. */
      if (var != univ_var && LEARN_VAR_MARKED (var) && 
          ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
           (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var))))
        {
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "  ...which is satisfied by a collected literal\n");
          return 1;
        }
    }

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "  ...which is not satisfied by a collected literal\n");

  /* At this point, 'blocked_clause' is not satisfied by a
     collected variable. Check if it is blocked with an unassigned
     blocking literal. In this case, it is still blocked if we
     eliminate 'univ_var' from the initial cube's assignment. */
  LitID blocking_lit = blocked_clause->qbcp_qbce_blocking_lit;
  assert (blocking_lit);
  Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);
  if (!QDPLL_VAR_ASSIGNED (blocking_var))
    {
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "  ...which is blocked with UNassigned blocking literal %d\n", blocking_lit);
      return 1;
    }
  else
    if (qdpll->options.verbosity >= 2)
      fprintf (stderr, "  ...which is blocked with assigned blocking literal %d\n", blocking_lit);

  return 0;
}

static void
cover_by_assignment_push_blocked_clauses_of_exists_var (QDPLL *qdpll, 
                                                               Var *exists_var, 
                                                               LitID exists_lit,
                                                               ConstraintPtrStack *check_clauses_stack, 
                                                               ConstraintPtrStack *marked_clauses_stack)
{
  assert ((VarID) LIT2VARID (exists_lit) == exists_var->id);
  assert (QDPLL_VAR_EXISTS (exists_var));

  BLitsOccStack *occs = QDPLL_LIT_NEG (exists_lit) ? 
    &exists_var->pos_occ_clauses : &exists_var->neg_occ_clauses;

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "cover-by-assignment: exists-var %d has %d original occs pushed to be checked\n", 
             exists_var->id, (unsigned int) QDPLL_COUNT_STACK (*occs));
  
  BLitsOcc *op, *oe;
  for (op = occs->start, oe = occs->top; op < oe; op++)
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      BLitsOcc occ = *op;
      Constraint *c = occ.constraint;
      if (qdpll->options.verbosity >= 2)
        {
          fprintf (stderr, "  cover-by-assignment: exists-var occurrence ");
          print_constraint (qdpll, c);
          if (c->qbcp_qbce_blocked)
            fprintf (stderr, "  ...is blocked\n");
          else
            fprintf (stderr, "  ...is not blocked\n");
          if (c->qbcp_qbce_multi_purpose_mark)
            fprintf (stderr, "  ...marked already\n");
          else
            fprintf (stderr, "  ...not marked already\n");
        }
      /* Non-blocked occs must be satisfied anyway. */
      if (!c->qbcp_qbce_blocked)
        continue;
      /* Follow chain of blocked clauses. */
      else if (LIT2VARPTR(qdpll->pcnf.vars, c->qbcp_qbce_blocking_lit) != exists_var)
        continue;
      if (!c->qbcp_qbce_multi_purpose_mark)
        {
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "  ...which is pushed to be checked\n");
          c->qbcp_qbce_multi_purpose_mark = 1;
          QDPLL_PUSH_STACK (qdpll->mm, *marked_clauses_stack, c);
          QDPLL_PUSH_STACK (qdpll->mm, *check_clauses_stack, c);
        }
    }
}

static int
cover_by_assignment_check_maybe_blocked_clauses_on_exists_var (QDPLL *qdpll, 
                                                               Var *univ_var,
                                                               Var *exists_var, 
                                                               LitID exists_lit,
                                                               ConstraintPtrStack *check_clauses_stack, 
                                                               ConstraintPtrStack *marked_clauses_stack)
{
  assert (QDPLL_EMPTY_STACK (*check_clauses_stack));
  assert (QDPLL_VAR_FORALL (univ_var));
  assert (QDPLL_VAR_EXISTS (exists_var));
  assert ((VarID) LIT2VARID (exists_lit) == exists_var->id);

  /* Collect blocked occurrences of 'exists_var' to be inspected. */
  cover_by_assignment_push_blocked_clauses_of_exists_var 
    (qdpll, exists_var, exists_lit, check_clauses_stack, marked_clauses_stack);

  Constraint *c;
  while (!QDPLL_EMPTY_STACK (*check_clauses_stack))
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      c = QDPLL_POP_STACK (*check_clauses_stack);
      assert (c->qbcp_qbce_multi_purpose_mark);
      assert (c->qbcp_qbce_blocked);
      if (!cover_by_assignment_check_blocked_clauses_aux 
          (qdpll, univ_var, c))
        return 0;
      else
        {
          /* Push blocked occurrences of existential literals in 'c'. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              if (QDPLL_VAR_EXISTS (var))
                cover_by_assignment_push_blocked_clauses_of_exists_var 
                  (qdpll, var, lit, check_clauses_stack, marked_clauses_stack);
            }
        }
    }

  return 1;
}

/* Go over all blocked clauses and check if we can eliminate 'univ_var'. This
   function may incur less overhead than if we check blocked clauses by
   traversing the occurrence lists of variables. */
static int
cover_by_assignment_check_blocked_clauses (QDPLL *qdpll, Var *univ_var)
{
  assert (QDPLL_VAR_FORALL (univ_var));

  ConstraintPtrStack *sp, *se;
  for (sp = qdpll->qbcp_qbce_blocked_clauses.start, 
         se = qdpll->qbcp_qbce_blocked_clauses.top; sp < se; sp++)
    {
      ConstraintPtrStack stack = *sp;
      Constraint **cp, **ce;
      for (cp = stack.start, ce = stack.top; cp < ce; cp++)
        {
#if COMPUTE_STATS
          qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
          Constraint *c = *cp;
          assert (c->qbcp_qbce_blocked);
          if (!cover_by_assignment_check_blocked_clauses_aux 
              (qdpll, univ_var, c))
            return 0;
        } 
    }

  return 1;
}

/* Returns non-zero if and only if we want to keep 'univ_var' to be
   included in the initial cube. */
static int
cover_by_assignment_keep_univ_var (QDPLL *qdpll, Var *univ_var, 
                                   ConstraintPtrStack *check_clauses_stack, 
                                   ConstraintPtrStack *marked_clauses_stack)
{
#if COMPUTE_STATS
  qdpll->stats.elim_univ_vars_calls++;
#endif
  qdpll->state.elim_univ_tried++;

  assert (QDPLL_EMPTY_STACK (*check_clauses_stack));
  assert (QDPLL_EMPTY_STACK (*marked_clauses_stack));
  int result = 0;

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "cover-by-assignment: checking to eliminate variable %d\n", univ_var->id);

  assert (QDPLL_VAR_ASSIGNED (univ_var));
  assert (QDPLL_VAR_FORALL (univ_var));
  assert (univ_var->mode != QDPLL_VARMODE_PURE);
  BLitsOccStack *orig_occs = QDPLL_VAR_ASSIGNED_FALSE (univ_var) ? 
    &univ_var->neg_occ_clauses : &univ_var->pos_occ_clauses;

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "cover-by-assignment: variable %d has %d original occs to be checked\n", 
             univ_var->id, (unsigned int) QDPLL_COUNT_STACK (*orig_occs));

  /* Check if all input clause occurrences of 'univ_var' are satisfied
     by some other collected variable. If not, then we must keep
     'univ_var'. */
  BLitsOcc *op, *oe;
  for (op = orig_occs->start, oe = orig_occs->top; !result && op < oe; op++)
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      BLitsOcc occ = *op;
      Constraint *c = occ.constraint;
      if (!cover_by_assignment_is_univ_var_orig_occ_covered (qdpll, univ_var, c))
        result = 1;
      else
        {
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; !result && p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              if (QDPLL_VAR_EXISTS (var) && 
                  !cover_by_assignment_check_maybe_blocked_clauses_on_exists_var 
                  (qdpll, univ_var, var, lit, check_clauses_stack, marked_clauses_stack))
                result = 1;
            }
        }
    }

  /* Reset clause marks. */
  while (!QDPLL_EMPTY_STACK (*marked_clauses_stack))
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      Constraint *c = QDPLL_POP_STACK (*marked_clauses_stack);
      assert (c->qbcp_qbce_multi_purpose_mark);
      c->qbcp_qbce_multi_purpose_mark = 0;
    }
  assert (QDPLL_EMPTY_STACK (*marked_clauses_stack));
  QDPLL_RESET_STACK (*check_clauses_stack);

  return result;
}


static void
cover_by_assignment_collect_univ_vars_from_orig_occ (QDPLL *qdpll, Constraint *c)
{
  assert (!c->learnt);
  assert (!c->is_cube);
  assert (!c->qbcp_qbce_blocked);
  Var *min_sat_univ_var = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Search for satisfying literals. */
      if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
        {
          if (LEARN_VAR_MARKED (var))
            {
              /* Clause is satisfied by a collected variable. Skip the rest,
                 no need to collect another literal from this clause. */
              break;
            }
          else
            {
              /* The satisfying literal has not been collected. */
              if (QDPLL_VAR_FORALL (var))
                {
                  if (var->mode != QDPLL_VARMODE_PURE && !min_sat_univ_var)
                    {
                      /* Found a satisfying universal literal. If there are
                         multiple, then store only the leftmost one (note that we
                         traverse the literals from left to right), similar to to
                         our heuristics in traditional QCDCL cube learning. */
                      min_sat_univ_var = var;
                    }
                }
              else
                {
                  /* NOTE: found a satisfying existential literal which has
                     not been collected. This case, however, should never
                     occur because we collect all existentials beforehand. */
                  assert (QDPLL_VAR_EXISTS (var));
                  assert (LEARN_VAR_MARKED (var));
                  QDPLL_ABORT_QDPLL (1, "reached unexpected branch in code!");
                }            

            }
        }
    }
  /* Check if we need to collect a universal variable in order to satisfy this clause. */
  if (p == e)
    {
      assert (min_sat_univ_var);
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "cover-by-assignment: collecting univ %d\n", 
                 QDPLL_VAR_ASSIGNED_FALSE (min_sat_univ_var) ? 
                 -min_sat_univ_var->id : min_sat_univ_var->id);
      cover_by_clauses_collect_lit (qdpll, qdpll->mm, min_sat_univ_var, 
                                    QDPLL_VAR_ASSIGNED_FALSE (min_sat_univ_var) ? 
                                    -min_sat_univ_var->id : min_sat_univ_var->id);
      qdpll->state.univ_vars_cur_collected++;
    }
}

/* Check if the blocked clause 'c' is a root of the CNF traversal. */
static int
cover_by_assignment_collect_univ_vars_init_blocked_clause (QDPLL *qdpll, Constraint *c)
{
  assert (c->qbcp_qbce_blocked);
  LitID blocking_lit = c->qbcp_qbce_blocking_lit;
  assert (blocking_lit);
  Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);

  /* If the blocking literal of 'c' is unassigned then the clause is blocked
     under the current assignment and hence no actions are required. */
  if (!QDPLL_VAR_ASSIGNED (blocking_var))
    return 0;

  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Search for literals which have been collected and which satisfy the
         clause. */
      if (LEARN_VAR_MARKED (var) && 
          ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
           (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var))))
        return 0;
    }

  /* Clause is not satisfied by a collected variable and its blocking variable
     is assigned. Traversal starts at this clause. */
  return 1;
}

static void
cover_by_assignment_collect_univ_vars (QDPLL *qdpll, 
                                       VarPtrStack *univ_vars_stack, 
                                       ConstraintPtrStack *check_clauses_stack, 
                                       ConstraintPtrStack *marked_clauses_stack)
{
  qdpll->state.elim_univ_tried += QDPLL_COUNT_STACK (*univ_vars_stack);
  Var **vp, **ve;
  for (vp = univ_vars_stack->start, ve = univ_vars_stack->top; vp < ve; vp++)
    {
      Var *var = *vp;
      assert (QDPLL_VAR_ASSIGNED (var));
      BLitsOccStack *occs = QDPLL_VAR_ASSIGNED_FALSE (var) ? 
        &var->neg_occ_clauses : &var->pos_occ_clauses;
      BLitsOcc *op, *oe;
      for (op = occs->start, oe = occs->top; op < oe; op++)
        {
#if COMPUTE_STATS
          qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
          BLitsOcc occ = *op;
          Constraint *c = occ.constraint;
          if (!c->qbcp_qbce_blocked && !c->qbcp_qbce_multi_purpose_mark)
            {
              c->qbcp_qbce_multi_purpose_mark = 1;
              QDPLL_PUSH_STACK (qdpll->mm, *check_clauses_stack, c);
            }
        }
    } 

  /* Check original occurrences of universal variables, collect universals
     which are necessary to cover the occurrences. */
  while (!QDPLL_EMPTY_STACK (*check_clauses_stack))
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      Constraint *c = QDPLL_POP_STACK (*check_clauses_stack);
      assert (!c->qbcp_qbce_blocked);
      assert (c->qbcp_qbce_multi_purpose_mark);
      /* Clear clause marks. */
      c->qbcp_qbce_multi_purpose_mark = 0;
      cover_by_assignment_collect_univ_vars_from_orig_occ (qdpll, c);
    }

  /* Collect universals reachable from blocked clauses. First collect blocked
     clauses which are roots of the traversal. */
  ConstraintPtrStack *sp, *se;
  for (sp = qdpll->qbcp_qbce_blocked_clauses.start, 
         se = qdpll->qbcp_qbce_blocked_clauses.top; sp < se; sp++)
    {
      ConstraintPtrStack stack = *sp;
      Constraint **cp, **ce;
      for (cp = stack.start, ce = stack.top; cp < ce; cp++)
        {
#if COMPUTE_STATS
          qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
          Constraint *c = *cp;
          assert (c->qbcp_qbce_blocked);
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "seen blocked clause at level %d:\n", 
                       sp - qdpll->qbcp_qbce_blocked_clauses.start);
              print_constraint (qdpll, c);
            }
          if (!c->qbcp_qbce_multi_purpose_mark && 
              (cover_by_assignment_collect_univ_vars_init_blocked_clause (qdpll, c)))
            {
              if (qdpll->options.verbosity >= 2)
                {
                  fprintf (stderr, "pushing root blocked clause:");
                  print_constraint (qdpll, c);
                }
              c->qbcp_qbce_multi_purpose_mark = 1;
              QDPLL_PUSH_STACK (qdpll->mm, *check_clauses_stack, c);
              QDPLL_PUSH_STACK (qdpll->mm, *marked_clauses_stack, c);
            }
        } 
    }

  /* Traverse clauses from collected blocked root clauses. */
  while (!QDPLL_EMPTY_STACK (*check_clauses_stack))
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      Constraint *c = QDPLL_POP_STACK (*check_clauses_stack);
      assert (c->qbcp_qbce_multi_purpose_mark);
      if (c->qbcp_qbce_blocked)
        {
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "processing blocked clause:");
              print_constraint (qdpll, c);
              fprintf (stderr, "...with blocking literal %d\n", c->qbcp_qbce_blocking_lit);
            }
          LitID blocking_lit = c->qbcp_qbce_blocking_lit;
          assert (blocking_lit);
          Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);
          BLitsOccStack *occs = QDPLL_LIT_NEG (blocking_lit) ? 
            &blocking_var->pos_occ_clauses : &blocking_var->neg_occ_clauses;
          BLitsOcc *op, *oe;
          for (op = occs->start, oe = occs->top; op < oe; op++)
            {
#if COMPUTE_STATS
              qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
              BLitsOcc occ = *op;
              Constraint *c = occ.constraint;
              if (!c->qbcp_qbce_multi_purpose_mark)
                {
                  if (qdpll->options.verbosity >= 2)
                    {
                      fprintf (stderr, "pushing clause:");
                      print_constraint (qdpll, c);
                    }
                  c->qbcp_qbce_multi_purpose_mark = 1;
                  QDPLL_PUSH_STACK (qdpll->mm, *check_clauses_stack, c);
                  QDPLL_PUSH_STACK (qdpll->mm, *marked_clauses_stack, c);
                }
            }
        }
      else
        {
          /* Non-blocked clauses. */
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "processing non-blocked clause:");
              print_constraint (qdpll, c);
            }
          /* Collect universals from non-blocked clauses and push new clauses
             from existential pure literals. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var  = LIT2VARPTR (qdpll->pcnf.vars, lit);
              if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) || 
                   (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
                {
                  if (QDPLL_VAR_FORALL (var) && !LEARN_VAR_MARKED (var) &&
                      var->mode != QDPLL_VARMODE_PURE)
                    {
                      if (qdpll->options.verbosity >= 2)
                        fprintf (stderr, "cover-by-assignment: collecting univ %d\n", 
                                 QDPLL_VAR_ASSIGNED_FALSE (var) ? 
                                 -var->id : var->id);
                      cover_by_clauses_collect_lit (qdpll, qdpll->mm, var, 
                                                    QDPLL_VAR_ASSIGNED_FALSE (var) ? 
                                                    -var->id : var->id);
                      qdpll->state.univ_vars_cur_collected++;
                    }
                  else if (QDPLL_VAR_EXISTS (var) && var->mode == QDPLL_VARMODE_PURE)
                    {
                      /* Push other occurrences of pure variable. A universal
                         variable might have triggered that existential to become
                         pure, and that pure assignment in turn might have
                         produced further blocked clauses. Hence we might have to
                         collect that universal variable. */
                      BLitsOccStack *occs = QDPLL_VAR_ASSIGNED_FALSE (var) ? 
                        &var->pos_occ_clauses : &var->neg_occ_clauses;
                      BLitsOcc *op, *oe;
                      for (op = occs->start, oe = occs->top; op < oe; op++)
                        {
#if COMPUTE_STATS
                          qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
                          BLitsOcc occ = *op;
                          Constraint *c = occ.constraint;
                          if (!c->qbcp_qbce_multi_purpose_mark)
                            {
                              if (qdpll->options.verbosity >= 2)
                                {
                                  fprintf (stderr, "pushing clause:");
                                  print_constraint (qdpll, c);
                                }
                              c->qbcp_qbce_multi_purpose_mark = 1;
                              QDPLL_PUSH_STACK (qdpll->mm, *check_clauses_stack, c);
                              QDPLL_PUSH_STACK (qdpll->mm, *marked_clauses_stack, c);
                            }
                        }
                    }
                }
            }
          
        }
    }

  /* Unmark clauses. */
  while (!QDPLL_EMPTY_STACK (*marked_clauses_stack))
    {
#if COMPUTE_STATS
      qdpll->stats.elim_univ_vars_clauses_seen++;
#endif
      Constraint *c = QDPLL_POP_STACK (*marked_clauses_stack);
      assert (c->qbcp_qbce_multi_purpose_mark);
      c->qbcp_qbce_multi_purpose_mark = 0;
    }
}

#endif

static void
cover_by_assignment_toggle_dynamic_elim_univs (QDPLL *qdpll)
{
  /* Check whether to turn off elimination of universal variables based on
     success rate, if this has not already been switched off previously. */
  if (!qdpll->state.elim_univ_dynamic_disabled &&
      qdpll->options.elim_univ_dynamic_switch &&
      qdpll->state.elim_univ_tried >= qdpll->options.elim_univ_dynamic_switch_delay)
    {
      /* Do this check every 'qdpll->options.elim_univ_dynamic_switch_delay' calls. */
      float success_rate = qdpll->state.elim_univ_tried ? 
        (qdpll->state.elim_univ_eliminated / (float) qdpll->state.elim_univ_tried) : 0; 
      success_rate *= 100;
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "elim-univ success rate after %d tries: %f\n", 
                 qdpll->state.elim_univ_tried, success_rate);
      if (success_rate <= qdpll->options.elim_univ_dynamic_success_threshold)
        {
          if (qdpll->options.verbosity >= 1)
            fprintf (stderr, "elim-univ: disabled due to threshold %d and current success rate %f after %d tries\n", 
                     qdpll->options.elim_univ_dynamic_success_threshold, success_rate, qdpll->state.elim_univ_tried);
          qdpll->state.elim_univ_dynamic_disabled = 1;
        }
    }
}

/* Take the current assignment as initial cube. This approach is intended for
   use with QBCE where some input clauses may become blocked. If QBCE is not
   applied, then likely 'cover_by_clauses' will produce better (?) cubes since
   we try to prefer existential literals. */
static int
cover_by_assignment (QDPLL * qdpll, LitIDStack * lit_stack)
{
#if COMPUTE_STATS
  qdpll->stats.initial_cubes++;
  qdpll->stats.qbcp_qbce_total_current_blocked_clauses += 
    qdpll->stats.qbcp_qbce_current_blocked_clauses;
#endif
  assert (qdpll->state.sat_branch_detected ||
	  !qdpll->options.no_qbce_dynamic);
#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  /* First collect ALL assigned existential variables in the initial cube. Then
     go over assigned universal variables and check if we can exclude some of
     them. */
  VarPtrStack univ_vars_stack;
  QDPLL_INIT_STACK (univ_vars_stack);
  ConstraintPtrStack check_clauses_stack;
  QDPLL_INIT_STACK (check_clauses_stack);
  ConstraintPtrStack marked_clauses_stack;
  QDPLL_INIT_STACK (marked_clauses_stack);
#endif

  assert (QDPLL_COUNT_STACK (*lit_stack) == 0);
  assert (QDPLL_COUNT_STACK (qdpll->internal_cover_lits) == 0);
  /* Must collect EVERY enqueued assignment, even those not yet propagated,
     because we used empty formula watching to detect empty CNF under the current
     assignment. */
  QDPLLMemMan *mm = qdpll->mm;
  VarID *p, *e;
  for (p = qdpll->assigned_vars, e = qdpll->assigned_vars_top; p < e; p++)
    {
      VarID vid = *p;
      Var *var = VARID2VARPTR (qdpll->pcnf.vars, vid);
      assert (QDPLL_VAR_ASSIGNED (var));
      if ((!QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS || QDPLL_VAR_FORALL(var)) && 
          var->mode == QDPLL_VARMODE_PURE)
        continue;

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
      if (QDPLL_VAR_FORALL(var))
        {
          /* Collect universal variables on stack to be checked later. */
          QDPLL_PUSH_STACK (qdpll->mm, univ_vars_stack, var);
          continue;
        }
#endif

      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "cover-by-assignment: collecting %d\n", 
                 QDPLL_VAR_ASSIGNED_FALSE (var) ? -vid : vid);

      cover_by_clauses_collect_lit (qdpll, mm, var, 
                                    QDPLL_VAR_ASSIGNED_FALSE (var) ? -vid : vid);
    }

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
#if COMPUTE_STATS
  qdpll->stats.elim_univ_vars_total_univ_vars += QDPLL_COUNT_STACK (univ_vars_stack);
#endif
  unsigned int cur_total_univ_vars = QDPLL_COUNT_STACK (univ_vars_stack);
  qdpll->state.univ_vars_cur_collected = 0;
  if (!qdpll->state.elim_univ_dynamic_disabled)
    cover_by_assignment_collect_univ_vars (qdpll, &univ_vars_stack, 
                                           &check_clauses_stack, 
                                           &marked_clauses_stack);
  else
    {
      /* Collect every universal variable on stack 'univ_vars'. */
      Var **vp, **ve;
      for (vp = univ_vars_stack.start, ve = univ_vars_stack.top; vp < ve; vp++)
        {
          Var *var = *vp;
          assert (QDPLL_VAR_ASSIGNED (var));
          assert (QDPLL_VAR_FORALL (var));
          assert (var->mode != QDPLL_VARMODE_PURE);
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "cover-by-assignment: collecting univ %d\n", 
                     QDPLL_VAR_ASSIGNED_FALSE (var) ? -var->id : var->id);
          cover_by_clauses_collect_lit (qdpll, mm, var, 
                                        QDPLL_VAR_ASSIGNED_FALSE (var) ? -var->id : var->id);
          qdpll->state.univ_vars_cur_collected++;
        }
    }
 assert (cur_total_univ_vars >= qdpll->state.univ_vars_cur_collected);
 qdpll->state.elim_univ_eliminated += 
   (cur_total_univ_vars - qdpll->state.univ_vars_cur_collected);
 cover_by_assignment_toggle_dynamic_elim_univs (qdpll);
#if COMPUTE_STATS
 qdpll->stats.initial_cubes_univ_lits += qdpll->state.univ_vars_cur_collected;
 qdpll->stats.elim_univ_vars_eliminated += 
   (cur_total_univ_vars - qdpll->state.univ_vars_cur_collected);
#endif
#endif

  cover_by_clauses_collect_lits_sorted (qdpll, mm, lit_stack);

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "cover-by-assignment: collected %d currently assigned variables, %d total variables.\n", 
             (unsigned int) QDPLL_COUNT_STACK (*lit_stack), qdpll->pcnf.used_vars);

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  QDPLL_DELETE_STACK (qdpll->mm, univ_vars_stack);
  QDPLL_DELETE_STACK (qdpll->mm, check_clauses_stack);
  QDPLL_DELETE_STACK (qdpll->mm, marked_clauses_stack);
#endif

#if COMPUTE_STATS
  qdpll->stats.initial_cubes_sizes += QDPLL_COUNT_STACK (*lit_stack);
#endif

  return 0;
}


/* Generate cover in linear time, i.e. traverse original clauses exactly once. 
   Maybe this is worse than generating covers from assigned vars. */
static int
cover_by_clauses (QDPLL * qdpll, LitIDStack * lit_stack,
                  LitIDStack * lit_stack_tmp)
{
  /* With dynamic QBCE or trivial truth, construct initial cube from
     assignment instead. */
  QDPLL_ABORT_QDPLL (qdpll->state.sat_branch_detected ||
		     !qdpll->options.no_qbce_dynamic, 
                     "unexpected call of cover-by-clauses!");
#if COMPUTE_STATS
  qdpll->state.univ_vars_cur_collected = 0;
#endif
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  assert (QDPLL_COUNT_STACK (*lit_stack) == 0);
  assert (QDPLL_COUNT_STACK (qdpll->internal_cover_lits) == 0);
#ifndef NDEBUG
  do
    {
      Scope *s;
      for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
        assert (QDPLL_EMPTY_STACK (s->cover_lits));
      for (s = qdpll->pcnf.user_scopes.first; s; s = s->link.next)
        assert (QDPLL_EMPTY_STACK (s->cover_lits));
    }
  while (0);
#endif
#if COMPUTE_STATS
  qdpll->stats.initial_cubes++;
  qdpll->stats.qbcp_qbce_total_current_blocked_clauses += 
    qdpll->stats.qbcp_qbce_current_blocked_clauses;
  /* Abusing stack for stats-computation. */
  assert (QDPLL_COUNT_STACK (qdpll->wreason_a) == 0);
#endif
  const int collect_full_cover_set = qdpll->state.collect_full_cover_sets && 
    qdpll->options.incremental_use && 
    (qdpll->state.cnt_created_clause_groups > 0 || 
     QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0);
  const Scope *last_scope = qdpll->pcnf.scopes.last;
  assert (QDPLL_SCOPE_EXISTS (last_scope));
  Constraint *c;

  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      assert (!c->learnt);
      assert (!c->is_cube);

      /* Relevant only if we do QBCE pre/inprocessing. */
      if (c->qbcp_qbce_blocked)
        {
          assert (qdpll->options.qbce_preprocessing || 
                  qdpll->options.qbce_inprocessing);
          continue;
        }

      unsigned int clause_cover_lits_cnt = 0;
      unsigned int clause_covered_by_collected_lit = 0;
      LitID *p, *e, lit;
      Var *max_e_true_var = 0, *min_a_true_var = 0;
      LitID max_e_true_lit = 0, min_a_true_lit = 0;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        {
          lit = *p;
          Var *lit_var = LIT2VARPTR (vars, lit);

          if (QDPLL_SCOPE_FORALL (lit_var->scope)
              && lit_var->mode == QDPLL_VARMODE_PURE)
            continue;
          /* Search for positive literals. */
          if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (lit_var)) ||
              (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (lit_var)))
            {
              clause_cover_lits_cnt++;
              /* Skip clauses that are already covered by collected
                 literal or covered by innermost existential variable ->
                 never collect such literals since they will be reduced
                 anyway. */
              if (LEARN_VAR_MARKED (lit_var) || lit_var->scope == last_scope)
                {
                  clause_covered_by_collected_lit = 1;
                  if (lit_var->scope == last_scope)
                    {
                      if (qdpll->options.trace && !lit_var->mark_qrp)
                        {
                          lit_var->mark_qrp = 1;        /* prevent duplicates  */
                          QDPLL_PUSH_STACK (mm, *lit_stack_tmp,
                                            QDPLL_VAR_ASSIGNED_TRUE (lit_var)
                                            ? lit_var->id : -lit_var->id);
                        }
#if COMPUTE_STATS
                      /* BUG-FIX: must not count literal multiple times! */
                      if (!lit_var->mark_stats_type_reduce_lits)
                        {
                          lit_var->mark_stats_type_reduce_lits = 1;
                          QDPLL_PUSH_STACK (mm, qdpll->wreason_a, lit_var);
                        }
#endif
                    }
                    if ((LEARN_VAR_MARKED (lit_var) || !collect_full_cover_set))
                    goto SKIP;
                }
              if (QDPLL_SCOPE_FORALL (lit_var->scope))
                {
                  if (!min_a_true_var
                      || lit_var->scope->nesting <
                      min_a_true_var->scope->nesting)
                    {
                      min_a_true_var = lit_var;
                      min_a_true_lit = lit;
                    }
                }
              else
                {
                  if (!max_e_true_var
                      || max_e_true_var->scope->nesting <
                      lit_var->scope->nesting)
                    {
                      max_e_true_var = lit_var;
                      max_e_true_lit = lit;
                    }
                }
            }
        }
      assert (max_e_true_var || min_a_true_var);
      assert (!max_e_true_var || max_e_true_lit);
      assert (!min_a_true_var || min_a_true_lit);
      /* Prefer existential literals. */
      if (max_e_true_var)
        {
          if (collect_full_cover_set || !clause_covered_by_collected_lit)
            cover_by_clauses_collect_lit (qdpll, mm, max_e_true_var,
                                          max_e_true_lit);
          /* Clause is not covered by already collected lit (otherwise we
             would have jumped to label 'SKIP' below). Collect a new variable,
             set mark: refrain from trying to remove the collected var from the
             cover if the current clause is satisfied exactly by that var. */
          assert (clause_cover_lits_cnt > 0);
          if (clause_cover_lits_cnt == 1)
            {
              assert (!min_a_true_var);
            }
        }
      else
        {
#if COMPUTE_STATS
          qdpll->state.univ_vars_cur_collected++;
#endif
          assert (min_a_true_var);
          if (collect_full_cover_set || !clause_covered_by_collected_lit)
            cover_by_clauses_collect_lit (qdpll, mm, min_a_true_var,
                                          min_a_true_lit);
          assert (clause_cover_lits_cnt > 0);
          if (clause_cover_lits_cnt == 1)
            {
              assert (!max_e_true_var);
            }
        }
    SKIP:;
    }

#if COMPUTE_STATS
  Var **p, **e;
  for (p = qdpll->wreason_a.start, e = qdpll->wreason_a.top; p < e; p++)
    {
      assert ((*p)->mark_stats_type_reduce_lits);
      (*p)->mark_stats_type_reduce_lits = 0;
    }
  qdpll->stats.total_type_reduce_lits +=
    QDPLL_COUNT_STACK (qdpll->wreason_a);
  QDPLL_RESET_STACK (qdpll->wreason_a);
#endif

  cover_by_clauses_collect_lits_sorted (qdpll, mm, lit_stack);

#if COMPUTE_STATS
  qdpll->stats.initial_cubes_sizes += QDPLL_COUNT_STACK (*lit_stack);
  qdpll->stats.initial_cubes_univ_lits += qdpll->state.univ_vars_cur_collected;
#endif

  /* for resolution proof extraction we need to know, if any lits from the 
     innermost scope where reduced */
  return QDPLL_COUNT_STACK (*lit_stack_tmp);
}


static void
store_cover_set_aux (QDPLL *qdpll)
{
  assert (qdpll->cover_sets.cnt == 
          COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size);
  Constraint *least_recently_added = qdpll->cover_sets.last;
  UNLINK (qdpll->cover_sets, least_recently_added, link);
  assert (qdpll->cover_sets.cnt < 
          COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size);
  delete_constraint (qdpll, least_recently_added);
}


static void
store_cover_set (QDPLL *qdpll, LitIDStack *lit_stack)
{
  Constraint *cover_set = create_constraint (qdpll, QDPLL_COUNT_STACK(*lit_stack), 1);
  cover_set->learnt = 1;
  assert (cover_set->is_cube);
  LitID *p, *e, *dest = cover_set->lits;
  for (p = lit_stack->start, e = lit_stack->top; p < e; p++, dest++)
    { 
      assert (dest < cover_set->lits + cover_set->num_lits);   
      *dest = *p;
    }
  assert (qdpll->cover_sets.cnt <= COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size);
  /* If the list of cover sets is full then delete the least-recently added cover set.*/
  if (qdpll->cover_sets.cnt == COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size)
    store_cover_set_aux (qdpll);
  LINK_FIRST(qdpll->cover_sets, cover_set, link);
  assert (qdpll->cover_sets.cnt <= COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size);
}


/* Initialize the literal-stack with literals of either the
   conflicting clause or of a cover set / satisfied cube. This is the
   working reason to start with. */
static void
get_initial_reason (QDPLL * qdpll, LitIDStack ** lit_stack,
                    LitIDStack ** lit_stack_tmp,
                    const QDPLLQuantifierType type)
{
#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  Var *vars = qdpll->pcnf.vars;
  QDPLLMemMan *mm = qdpll->mm;
  LitIDStack *stack = *lit_stack;
  Var *var;
  LitID *p, *e, lit;
  Constraint *res_cons = qdpll->result_constraint;
  assert (!qdpll->options.trace || !qdpll->res_cons_id);
  if ((res_cons) || type == QDPLL_QTYPE_EXISTS)
    {
      assert (!qdpll->state.sat_branch_detected);
      /* We enter this branch when learning a clause by trivial falsity or
         dynamic nenofex. This
         clause will be used as the start point for the derivation of further
         clauses, unless it is already asserting or empty. */
      assert (res_cons || qdpll->state.unsat_branch_clause);
      if (res_cons)
        {
          assert (!res_cons->qbcp_qbce_blocked);
          qdpll->res_cons_id = res_cons->id;
          assert (type != QDPLL_QTYPE_EXISTS || (res_cons && !res_cons->is_cube));
          assert (type == QDPLL_QTYPE_EXISTS || (res_cons && res_cons->is_cube));
          learnt_constraint_mtf (qdpll, res_cons);
        }

      /* Push and mark literals of reason clause onto 'lit-stack',
         which is the working reason. */
      if (res_cons)
        {
          p = res_cons->lits;
          e = p + res_cons->num_lits;
        }
      else
        {
          assert (qdpll->state.unsat_branch_clause);
          /* For QPUP tracing: must set 'qdpll->res_cons_id' to ID of unsat
             branch clause. */
          qdpll->res_cons_id = qdpll->state.unsat_branch_clause->id;
          p = qdpll->state.unsat_branch_clause->lits;
          e = p + qdpll->state.unsat_branch_clause->num_lits;
        }
      /* Can happen that input formula contains clause with universal literals
         only. Initial reason will then be empty. This may also happen if the
         clause learned by trivial falsity is empty after universal
         reduction. */
      assert (qdpll->state.decision_level == 0 || p < e || 
              qdpll->state.unsat_branch_clause);
      for (; p < e; p++)
        {
          lit = *p;
          var = LIT2VARPTR (vars, lit);
          /* Increase activity of variable in conflicting clause. */
          increase_var_activity (qdpll, var, var->scope);
          assert (qdpll->options.long_dist_res || !LEARN_VAR_MARKED (var));
          if (QDPLL_LIT_NEG (lit))
            LEARN_VAR_NEG_MARK (var);
          else
            LEARN_VAR_POS_MARK (var);
          QDPLL_PUSH_STACK (mm, *stack, lit);
          update_stop_crit_data (qdpll, vars, lit, type);
        }
      /* Working reason is already sorted here. */
      qdpll->dm->reduce_lits (qdpll->dm, lit_stack, lit_stack_tmp, type, 1);
    }
  else
    {
      unsigned int nlits;
      LitIDStack tmp;
      QDPLL_INIT_STACK (tmp);
      ConstraintID cid = 0;

      assert (type == QDPLL_QTYPE_FORALL && !res_cons);
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "SDCL: generating new cover set.\n");

      /* Variable 'qdpll->res_cons_id' is needed for tracing in QPUP learning only. */

      /* Find cover set. */
      nlits = QDPLL_COUNT_STACK (**lit_stack);

      if (nlits)
        abort();

        /* When using dynamic QBCE, we stop as soon as the formula is empty
           under the current assignment and QBCE. We simply the the FULL
           current assignment as initial cube. The soundness is explained by
           the fact that the formula is satisfiable under the current
           assignment and QBCE. Without QBCE or with QBCE pre/inprocessing, we
           compute initial cubes as usual. */
      int res;
      if (!qdpll->state.sat_branch_detected &&
	  (qdpll->options.qbce_preprocessing || qdpll->options.qbce_inprocessing || 
	   qdpll->options.no_qbce_dynamic))
	{
	  res = cover_by_clauses (qdpll, stack, &tmp) && qdpll->options.trace;
	  if (res)
	    {
	      qdpll->trace_full_cover_set (qdpll,
					   (cid = ++(qdpll->cur_constraint_id)),
					   tmp.start, QDPLL_COUNT_STACK (tmp),
					   (*lit_stack)->start,
					   QDPLL_COUNT_STACK (**lit_stack));
	      qdpll->res_cons_id = cid;
	    }
	}
      else
        {
          /* NOTE: this branch is taken if we successfully applied
             dynamic Nenofex test or trivial truth, or if dynamic QBCE is
             enabled. */
          res = cover_by_assignment (qdpll, stack);
          /* NOTE: returned value 'res' is relevant only for tracing in
             traditional QCDCL when we call 'cover_by_clauses' above. It is
             used to indicate dynamic discarding of innermost existential
             literals, for which a separate entry in the trace file will be
             printed. */
          assert (!res);
        }

      if (qdpll->options.trace && nlits - (QDPLL_COUNT_STACK (**lit_stack)))
        {
          qdpll->trace_constraint (++(qdpll->cur_constraint_id),
                                   (*lit_stack)->start,
                                   QDPLL_COUNT_STACK (**lit_stack), cid, 0);
          qdpll->res_cons_id = qdpll->cur_constraint_id;
        }

      nlits = QDPLL_COUNT_STACK (**lit_stack);

      if (qdpll->state.collect_full_cover_sets)
        {
          if  (qdpll->options.incremental_use && (qdpll->state.cnt_created_clause_groups > 0 || 
                                                  QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0))
            store_cover_set (qdpll, *lit_stack);
        }
      else
        assert (qdpll->cover_sets.cnt == 0);

      qdpll->dm->reduce_lits (qdpll->dm, lit_stack, lit_stack_tmp, type, 1);

      /* Working reason is now sorted. */
      if (qdpll->options.trace && QDPLL_COUNT_STACK (**lit_stack)
          && (nlits - QDPLL_COUNT_STACK (**lit_stack)))
        {
          qdpll->trace_constraint (qdpll->cur_constraint_id + 1,
                                   (*lit_stack)->start,
                                   QDPLL_COUNT_STACK (**lit_stack),
                                   qdpll->cur_constraint_id, 0);
          qdpll->cur_constraint_id += 1;
          qdpll->res_cons_id = qdpll->cur_constraint_id;
        }

      QDPLL_DELETE_STACK (mm, tmp);
    }
#if COMPUTE_TIMES
  qdpll->time_stats.total_ireason_time += (time_stamp () - start);
#endif
}


static int
is_var_at_type_dec_level_adv (QDPLL * qdpll, Var * var,
                              const QDPLLQuantifierType type)
{
  assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
  assert (var->decision_level <= qdpll->state.decision_level);
  assert ((unsigned int) QDPLL_COUNT_STACK (qdpll->dec_vars) ==
          qdpll->state.decision_level);

  /* we do NOT force to resolve out top-level literals. Just
     keep them in working reason. The following two lines make sure that we
     continue resolution if the working reason reason contains only literals
     from top-level. */
  if (var->decision_level == 0)
    return 0;

  Var *dec_var =
    VARID2VARPTR (qdpll->pcnf.vars,
                  qdpll->dec_vars.start[var->decision_level - 1]);
  assert (dec_var->decision_level == var->decision_level);
  assert (dec_var->mode == QDPLL_VARMODE_LBRANCH
          || dec_var->mode == QDPLL_VARMODE_RBRANCH);
  return dec_var->scope->type == type;
}


/* Returns true if variable is assigned at a level which has
   an existential decision variable. */
static int
is_var_at_type_dec_level (QDPLL * qdpll, Var * var,
                          const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  return is_var_at_type_dec_level_adv (qdpll, var, type);
}


/* ---------- START: CDCL ---------- */


/* Check condition by inspecting collected lits which possibly violate
   condition. This should be faster since we need not check all
   literals in a constraint. */
static int
all_smaller_type_lits_have_value_adv (QDPLL * qdpll,    /*LitIDStack * lit_stack,
                                                           Var * other_type_var, */
                                      const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  Var *hi_dl_var = qdpll->hi_dl_type_var;
  const VarID hi_dl_var_id = hi_dl_var->id;
  const unsigned int hi_dl_var_dec_level = hi_dl_var->decision_level;
  assert (hi_dl_var->scope->type != type);
  assert (hi_dl_var_dec_level == qdpll->hi_type_dl);
  assert (qdpll->cnt_hi_dl_type_lits == 1);
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = qdpll->smaller_type_lits.start,
       e = qdpll->smaller_type_lits.top; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      assert (var->scope->type == type);
      if ((!QDPLL_VAR_ASSIGNED (var)
           || var->decision_level >= qdpll->hi_type_dl
           ||
           ((type == QDPLL_QTYPE_FORALL
             && ((QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_NEG (lit))
                 || (QDPLL_VAR_ASSIGNED_TRUE (var) && QDPLL_LIT_POS (lit))))
            || (type == QDPLL_QTYPE_EXISTS
                && ((QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_POS (lit))
                    || (QDPLL_VAR_ASSIGNED_TRUE (var)
                        && QDPLL_LIT_NEG (lit))))))
          && dm->depends (dm, var->id, hi_dl_var_id))
        return 0;
    }
  return 1;
}


/* Assumes that the clause is sorted and that 'other_type_var' is the only type-literal 
   at the maximal type-decision level. */
static int
all_smaller_type_lits_have_value (QDPLL * qdpll,
                                  const QDPLLQuantifierType type)
{
  return all_smaller_type_lits_have_value_adv (qdpll, type);
}


static void
check_marks_and_push (QDPLL * qdpll, Var * var, LitID lit, LitIDStack * stack,
                      const QDPLLQuantifierType type)
{
  if (QDPLL_LIT_NEG (lit))
    {
      if (!LEARN_VAR_MARKED (var))
        {
          LEARN_VAR_NEG_MARK (var);
          QDPLL_PUSH_STACK (qdpll->mm, *stack, lit);
          update_stop_crit_data (qdpll, qdpll->pcnf.vars, lit, type);
          if (!qdpll->options.bump_vars_once)
            increase_var_activity (qdpll, var, var->scope);
        }
      else if (LEARN_VAR_POS_MARKED (var))
        {
          /* EXPECTED DEAD-CODE. Otherwise would get constraints with
             complementary literals, unless when using long-distance resolution. */
          QDPLL_ABORT_QDPLL(!qdpll->options.long_dist_res, "unexpected tautology!");
          assert (var->scope->type != type);
          if (!LEARN_VAR_NEG_MARKED (var))
            {
              LEARN_VAR_NEG_MARK (var);
              QDPLL_PUSH_STACK (qdpll->mm, *stack, lit);
              /* NOTE: we do not call update_stop_crit here since the literal
                 of the other phase has been collected already. */
              if (!qdpll->options.bump_vars_once)
                increase_var_activity (qdpll, var, var->scope);
            }
        }
    }
  else
    {
      assert (QDPLL_LIT_POS (lit));
      if (!LEARN_VAR_MARKED (var))
        {
          LEARN_VAR_POS_MARK (var);
          QDPLL_PUSH_STACK (qdpll->mm, *stack, lit);
          update_stop_crit_data (qdpll, qdpll->pcnf.vars, lit, type);
          if (!qdpll->options.bump_vars_once)
            increase_var_activity (qdpll, var, var->scope);
        }
      else if (LEARN_VAR_NEG_MARKED (var))
        {
          /* EXPECTED DEAD-CODE. Otherwise would get constraints with
             complementary literals, unless when using long-distance resolution. */
          QDPLL_ABORT_QDPLL(!qdpll->options.long_dist_res, "unexpected tautology!");
          assert (var->scope->type != type);
          if (!LEARN_VAR_POS_MARKED (var))
            {
              LEARN_VAR_POS_MARK (var);
              QDPLL_PUSH_STACK (qdpll->mm, *stack, lit);
              /* NOTE: we do not call update_stop_crit here since the literal
                 of the other phase has been collected already. */
              if (!qdpll->options.bump_vars_once)
                increase_var_activity (qdpll, var, var->scope);
            }
        }
    }
}

/* Perform q-resolution.*/
static ConstraintID
resolve_and_reduce (QDPLL * qdpll, ConstraintID ant1_id,
                    LitIDStack ** lit_stack, LitIDStack ** lit_stack_tmp,
                    Var * var, const QDPLLQuantifierType type)
{
  assert (!var->antecedent->qbcp_qbce_blocked);
  LitID *other_lits_start = var->antecedent->lits;
  LitID *other_lits_end = other_lits_start + var->antecedent->num_lits;
  ConstraintID res_id = ++(qdpll->cur_constraint_id);

  assert (QDPLL_COUNT_STACK (**lit_stack) > 0);
  assert (*lit_stack != *lit_stack_tmp);
  assert (*lit_stack != &(qdpll->add_stack)
          || *lit_stack_tmp == &(qdpll->add_stack_tmp));
  assert (*lit_stack_tmp != &(qdpll->add_stack)
          || *lit_stack == &(qdpll->add_stack_tmp));
  assert (other_lits_start < other_lits_end);
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (type == var->scope->type);
#if COMPUTE_STATS
  if (type == QDPLL_QTYPE_EXISTS)
    qdpll->stats.num_unsat_res_steps++;
  else
    qdpll->stats.num_sat_res_steps++;
#endif
#ifndef NDEBUG
  assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_stop_crit_data (qdpll, *lit_stack, type);
#endif
  if (qdpll->options.verbosity > 1)
    {
      const char prefix = type == QDPLL_QTYPE_EXISTS ? 'C' : 'S';
      const char *type_str = type == QDPLL_QTYPE_EXISTS ? "clause" : "cube";
      fprintf (stderr, "\n%cDCL: pivot variable: %d\n", prefix, var->id);
      fprintf (stderr, "%cDCL: working %s: ", prefix, type_str);
      print_lits (qdpll, (*lit_stack)->start,
                  QDPLL_COUNT_STACK (**lit_stack), 0);

      fprintf (stderr, "%cDCL: antecedent: ", prefix);
      print_lits (qdpll, other_lits_start,
                  other_lits_end - other_lits_start, 0);
    }

  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  unsigned int del = 0;
  LitIDStack *tmp = *lit_stack_tmp;
  assert (QDPLL_COUNT_STACK (*tmp) == 0);
  assert (QDPLL_COUNT_STACK (**lit_stack) != 0);
  LitID *p1, *p2;
  const LitID *e1 = (*lit_stack)->top;
  const LitID *e2 = other_lits_end;
  LitID lit1, lit2;
  Var *var1, *var2;
  VarID vid1;
  VarID vid2;
  unsigned int nesting1;
  unsigned int nesting2;

  /* Reset stop-crit-data, will be set from scratch during merging. */
  reset_stop_crit_data (qdpll);

  p1 = (*lit_stack)->start;
  p2 = other_lits_start;
  assert (p1 < e1);
  assert (p2 < e2);
  lit1 = *p1;
  lit2 = *p2;
#ifndef NDEBUG
  int wreason_seen_pivot = 0;
#endif
  /* Merge sorted lists */
  while (1)
    {
      if (compare_lits_by_user_variable_nesting (qdpll, lit1, lit2) <= 0)
        {
          var1 = LIT2VARPTR (vars, lit1);
          assert (QDPLL_LIT_NEG (lit1) || LEARN_VAR_POS_MARKED (var1));
          assert (QDPLL_LIT_POS (lit1) || LEARN_VAR_NEG_MARKED (var1));
          /* Must ignore pivot variable. */
          if (var1 != var)
            {
              QDPLL_PUSH_STACK (mm, *tmp, lit1);
              update_stop_crit_data (qdpll, vars, lit1, type);
            }
          else
            {
#ifndef NDEBUG
              wreason_seen_pivot = 1;
#endif
              LEARN_VAR_UNMARK (var1);
            }
          p1++;
          if (p1 >= e1)
            break;
          lit1 = *p1;
        }
      else
        {
          var2 = LIT2VARPTR (vars, lit2);
          /* Must ignore pivot variable. */
          if (var2 == var)
            {
              ;
            }
          else
            check_marks_and_push (qdpll, var2, lit2, tmp, type);
          p2++;
          if (p2 >= e2)
            break;
          lit2 = *p2;
        }
    }
  assert (p1 >= e1 || p2 >= e2);

  while (p1 < e1)
    {
      lit1 = *p1;
      var1 = LIT2VARPTR (vars, lit1);
      /* Must not have top-level assignments in working reason,
         these were eliminated before. */
      assert (QDPLL_LIT_NEG (lit1) || LEARN_VAR_POS_MARKED (var1));
      assert (QDPLL_LIT_POS (lit1) || LEARN_VAR_NEG_MARKED (var1));
      /* Must ignore pivot variable. */
      if (var1 != var)
        {
          QDPLL_PUSH_STACK (mm, *tmp, lit1);
          update_stop_crit_data (qdpll, vars, lit1, type);
        }
      else
        {
#ifndef NDEBUG
          wreason_seen_pivot = 1;
#endif
          LEARN_VAR_UNMARK (var1);
        }
      p1++;
    }

  while (p2 < e2)
    {
      lit2 = *p2;
      var2 = LIT2VARPTR (vars, lit2);
      /* Must ignore pivot variable and top-level assignments. */
      if (var2 == var)
        {
          ;
        }
      else
        check_marks_and_push (qdpll, var2, lit2, tmp, type);
      p2++;
    }

  /* Swap stacks. */
  LitIDStack *swap_tmp = *lit_stack;
  assert (tmp == *lit_stack_tmp);
  *lit_stack = tmp;
  *lit_stack_tmp = swap_tmp;
  QDPLL_RESET_STACK (**lit_stack_tmp);

#ifndef NDEBUG
  assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
#endif

  qdpll->dm->reduce_lits (qdpll->dm, lit_stack, lit_stack_tmp, type, 1);

  if (qdpll->options.trace)
    qdpll->trace_constraint (res_id, (*lit_stack)->start,
                             QDPLL_COUNT_STACK (**lit_stack), ant1_id,
                             var->antecedent->id);

  return res_id;
}


/* Checks whether the generated clause on 
   'lit_stack' is a suitable conflict clause. */
static int
stop_resolution (QDPLL * qdpll, LitIDStack * lit_stack,
                 const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
#ifndef NDEBUG
  assert_stop_crit_data (qdpll, lit_stack, type);
#endif

  unsigned int max_type_level =
    get_highest_type_lit_dec_level (qdpll, lit_stack->start, lit_stack->top,
                                    type);

  if (count_type_lit_at_dec_level
      (qdpll, lit_stack->start, lit_stack->top, max_type_level, type) != 1)
    return 0;
  else
    if (!is_var_at_type_dec_level
        (qdpll,
         (get_type_var_at_dec_level (qdpll, lit_stack->start, lit_stack->top,
                                     max_type_level, type)), type))
    return 0;
  else if (!all_smaller_type_lits_have_value (qdpll,
                                              type == QDPLL_QTYPE_EXISTS ?
                                              QDPLL_QTYPE_FORALL :
                                              QDPLL_QTYPE_EXISTS))
    return 0;
  else
    return 1;
}


/* Check if resolving 'lit_stack' with antecedent of 'var' would
   produce a tautology. In this case resolution is blocked.  */
static Var *
peek_tautology (QDPLL * qdpll, LitIDStack * lit_stack, Var * var)
{
  assert (!qdpll->options.long_dist_res);
  assert (var->antecedent);
  Var *vars = qdpll->pcnf.vars;
  Var *lit_var;
  LitID *p, *e, lit;
  for (p = var->antecedent->lits, e = p + var->antecedent->num_lits; p < e;
       p++)
    {
      lit = *p;
      lit_var = LIT2VARPTR (vars, lit);
      /* Ignore the pivot variable. */
      if (var == lit_var)
        continue;
      if ((QDPLL_LIT_NEG (lit) && LEARN_VAR_POS_MARKED (lit_var)) ||
          (QDPLL_LIT_POS (lit) && LEARN_VAR_NEG_MARKED (lit_var)))
        {
          if (qdpll->options.verbosity > 1)
            {
              fprintf (stderr, "peek tautology: tested var is %d\n", var->id);
              fprintf (stderr, "peek tautology: lit stack is\n");
              print_lits (qdpll, lit_stack->start,
                          lit_stack->top - lit_stack->start, 0);
              fprintf (stderr, "peek tautology: ante. is\n");
              print_lits (qdpll, var->antecedent->lits,
                          var->antecedent->num_lits, 0);

              fprintf (stderr, "peek tautology: true by lit %d\n", lit);
            }
          return lit_var;
        }
    }
  return 0;
}


static VarID
choose_var (QDPLL * qdpll, LitIDStack * lit_stack,
            const QDPLLQuantifierType type)
{
#if COMPUTE_STATS
  qdpll->stats.num_learn_choose_vars++;
#endif

  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (QDPLL_COUNT_STACK (*lit_stack) != 0);
  Var *pivot, *var, *blocking = 0, *vars = qdpll->pcnf.vars;
  LitID *p, *e, lit;

  /* First, get maximum trail var. */
  pivot = 0;
  for (p = lit_stack->start, e = lit_stack->top; p < e; p++)
    {
      lit = *p;
      var = LIT2VARPTR (vars, lit);
      if (var->mode == QDPLL_VARMODE_UNIT && var->scope->type == type)
        {
          assert (var->trail_pos != QDPLL_INVALID_TRAIL_POS);
          assert (!pivot || pivot->trail_pos != QDPLL_INVALID_TRAIL_POS);
          if (!pivot || pivot->trail_pos < var->trail_pos)
            pivot = var;
        }
    }

  if (!pivot)
    QDPLL_ABORT_QDPLL (1, "Fatal error: did not find pivot by trail!");

  if (!qdpll->options.long_dist_res && (blocking = peek_tautology (qdpll, lit_stack, pivot)))
    {
      /* If maximum trail var produces tautology, try to resolve on
         literals which prevent forall reduction of literal producing tautology. */
      pivot = 0;
      for (p = lit_stack->start, e = lit_stack->top; p < e; p++)
        {
          lit = *p;
          var = LIT2VARPTR (vars, lit);
          if (var->mode == QDPLL_VARMODE_UNIT && var->scope->type == type)
            {
              if (!pivot || pivot->trail_pos < var->trail_pos)
                if (qdpll->dm->depends (qdpll->dm, blocking->id, var->id) &&
                    !peek_tautology (qdpll, lit_stack, var))
                  pivot = var;
            }
        }
    }
  else
    {
#if COMPUTE_STATS
      qdpll->stats.num_learn_trail_pivot++;
#endif
    }

  if (!pivot)
    QDPLL_ABORT_QDPLL (1, "Fatal error: did not find pivot by deps!");

  return pivot->id;
}


static int
working_clause_is_tautologous (QDPLL * qdpll, LitIDStack * lit_stack,
                               const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = lit_stack->start, e = lit_stack->top; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      assert (LEARN_VAR_MARKED (var));

      if (LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var))
        {
          assert (0);
          assert (type != QDPLL_SCOPE_FORALL (var->scope));
          return 1;
        }
    }

  return 0;
}


static int
constraint_has_only_assumption_lits (QDPLL *qdpll, LitID *start, LitID *end);


/* Returns non-zero if a valid reason was derived 
   or 0 if either aborted or done. */
static int
generate_reason (QDPLL * qdpll, ConstraintID cid, LitIDStack ** lit_stack,
                 LitIDStack ** lit_stack_tmp, const QDPLLQuantifierType type)
{
  assert (*lit_stack != *lit_stack_tmp);
  assert (*lit_stack != &(qdpll->add_stack)
          || *lit_stack_tmp == &(qdpll->add_stack_tmp));
  assert (*lit_stack_tmp != &(qdpll->add_stack)
          || *lit_stack == &(qdpll->add_stack_tmp));
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);

  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  VarID varid;

  int is_init_reason_empty = QDPLL_EMPTY_STACK (**lit_stack);

AGAIN:

  /* Handle solving under assumptions: if the current constraint contains only
     assumptions then we are done. This is similar to an empty constraint.
     NOTE: we test the flag 'assumptions_given' not to add overhead for
     checking the current resolvent's literals when solving without
     assumptions. */

  if (QDPLL_EMPTY_STACK (**lit_stack) || 
      (qdpll->state.assumptions_given && 
       constraint_has_only_assumption_lits (qdpll, (*lit_stack)->start, (*lit_stack)->top)))
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "%s: derived empty %s\n",
                 type == QDPLL_QTYPE_EXISTS ? "CDCL" : "SDCL",
                 type == QDPLL_QTYPE_EXISTS ? "clause" : "cube");

      /* introduce an additional explicit reduction step */
      if (qdpll->options.trace && is_init_reason_empty
          && (qdpll->result_constraint == NULL ||
              qdpll->result_constraint->size_lits))
        qdpll->trace_constraint (++(qdpll->cur_constraint_id),
                                 (*lit_stack)->start,
                                 QDPLL_COUNT_STACK (**lit_stack), cid, 0);
      return 0;
    }

  int stop = stop_resolution (qdpll, *lit_stack, type);
  assert (qdpll->options.long_dist_res || !working_clause_is_tautologous (qdpll, *lit_stack, type));
  if (stop)
    return 1;
  else
    {

    DO_RES:
      /* Choose 'var' in rev.chron. order from trail s.t. 'var' appears in 
         working reason. */
      varid = choose_var (qdpll, *lit_stack, type);

      if (!varid)
        QDPLL_ABORT_QDPLL (1, "Fatal error: did not find pivot variable!\n");

      Var *var = VARID2VARPTR (vars, varid);
      assert (type == QDPLL_QTYPE_FORALL
              || (var->antecedent && !var->antecedent->is_cube));
      assert (type == QDPLL_QTYPE_EXISTS
              || (var->antecedent && var->antecedent->is_cube));

      assert (var->antecedent);
      assert (var->antecedent->is_reason);

      if (!qdpll->options.bump_vars_once)
        learnt_constraint_mtf (qdpll, var->antecedent);

      cid =
        resolve_and_reduce (qdpll, cid, lit_stack, lit_stack_tmp, var, type);

      /* Stack 'lit_stack' will now hold the resolvent's literals. */
      goto AGAIN;
    }
}


/* Setting watchers wrt. to decision levels and dependencies. One
   watcher is set to implied literal.  */
static void
set_learnt_constraint_lit_watchers (QDPLL * qdpll,
                                    Constraint * learnt_constraint,
                                    const unsigned int asserting_level,
                                    Var * implied,
                                    const QDPLLQuantifierType type)
{
  assert (implied->decision_level != QDPLL_INVALID_DECISION_LEVEL &&
          implied->decision_level > asserting_level);
  assert (learnt_constraint->is_cube || type == QDPLL_QTYPE_EXISTS);
  assert (!learnt_constraint->is_cube || type == QDPLL_QTYPE_FORALL);
  Var *vars = qdpll->pcnf.vars;
  QDPLLDepManGeneric *dm = qdpll->dm;
  const unsigned int implied_level = implied->decision_level;
  const VarID implied_id = implied->id;
  assert (implied_level > asserting_level &&
          implied_level != QDPLL_INVALID_DECISION_LEVEL);
  unsigned int hoffset = QDPLL_INVALID_WATCHER_POS,
    nhoffset = QDPLL_INVALID_WATCHER_POS;
  LitID *p, *e;
  for (e = learnt_constraint->lits, p = e + learnt_constraint->num_lits - 1;
       e <= p; p--)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      const unsigned int level = var->decision_level;
      assert (level != QDPLL_INVALID_DECISION_LEVEL
              || type != var->scope->type);
      /* Assumes that constraint is asserting. */
      assert (var->scope->type != type || level <= asserting_level ||
              var == implied);
      if (level == asserting_level)
        {
          /* Set 'nhoffset' exactly once. This maybe avoids irrelevant depends-checks. */
          if (nhoffset == QDPLL_INVALID_WATCHER_POS &&
              (type == var->scope->type
               || dm->depends (dm, var->id, implied_id)))
            {
              nhoffset = p - e;
              if (hoffset != QDPLL_INVALID_WATCHER_POS)
                break;
            }
        }
      else if (level == implied_level && type == var->scope->type)
        {
          assert (hoffset == QDPLL_INVALID_WATCHER_POS);
          hoffset = p - e;
          if (nhoffset != QDPLL_INVALID_WATCHER_POS)
            break;
        }
    }

  /* Do not set watchers in units since we will backtrack to level 0. */
  if (learnt_constraint->num_lits != 1)
    {
      QDPLL_ABORT_QDPLL ((hoffset == QDPLL_INVALID_WATCHER_POS ||
                          nhoffset == QDPLL_INVALID_WATCHER_POS),
                         "Failed to set lit-watcher in learnt constraint!");
      assert (hoffset != QDPLL_INVALID_WATCHER_POS &&
              nhoffset != QDPLL_INVALID_WATCHER_POS);
      unsigned int right_offset, left_offset;
      if (hoffset < nhoffset)
        {
          left_offset = hoffset;
          right_offset = nhoffset;
        }
      else
        {
          left_offset = nhoffset;
          right_offset = hoffset;
        }
      init_literal_watcher (qdpll, learnt_constraint, left_offset,
                            right_offset);
    }
  else
    assert (hoffset == 0 && nhoffset == QDPLL_INVALID_WATCHER_POS);
}


/* Chronological backtracking. */
static unsigned int
chron_backtracking (QDPLL * qdpll, const QDPLLQuantifierType type)
{
  /* The function relies on the following two properties for easy
     flipping of assignments. */
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (QDPLL_ASSIGNMENT_TRUE == -QDPLL_ASSIGNMENT_FALSE);
  assert (QDPLL_ASSIGNMENT_FALSE == -QDPLL_ASSIGNMENT_TRUE);
  VarID *p, *e, id;
  Var *vars = qdpll->pcnf.vars;
  for (p = qdpll->assigned_vars_top - 1, e = qdpll->assigned_vars; p >= e;
       p--)
    {
      id = *p;
      Var *assigned_var = VARID2VARPTR (vars, id);
      assert (QDPLL_VAR_ASSIGNED (assigned_var));
      assert (assigned_var->mode != QDPLL_VARMODE_UNDEF);
      if (type == assigned_var->scope->type
          && assigned_var->mode == QDPLL_VARMODE_LBRANCH)
        {
          assert (assigned_var->decision_level !=
                  QDPLL_INVALID_DECISION_LEVEL);
          assert (!qdpll->state.forced_assignment.antecedent);
          assert (!qdpll->state.forced_assignment.var);
          assert (!qdpll->state.forced_assignment.assignment);
          assert (!qdpll->state.forced_assignment.mode);
          /* Set forced assignment (flipping decision variable) to be enqueued afterwards. */
          qdpll->state.forced_assignment.var = assigned_var;
          qdpll->state.forced_assignment.assignment =
            -assigned_var->assignment;
          qdpll->state.forced_assignment.mode = QDPLL_VARMODE_RBRANCH;
          return assigned_var->decision_level;
        }
    }

  /* No proof obligation left. */
  return QDPLL_INVALID_DECISION_LEVEL;
}

static unsigned int analyze_solution_no_sdcl (QDPLL * qdpll);
static unsigned int analyze_conflict_no_cdcl (QDPLL * qdpll);

/* START: QPUP code. */

/* Marks used for implication graph traversal. */ 
static int
qpup_is_var_pos_marked (Var *var)
{
  return var->qpup_mark_pos; 
}

static int
qpup_is_var_neg_marked (Var *var)
{
  return var->qpup_mark_neg; 
}

static int
qpup_is_var_marked (Var *var)
{
  return qpup_is_var_neg_marked (var) || qpup_is_var_pos_marked (var); 
}

static void
qpup_mark_var (Var *var, int set_pos_mark)
{
  if (set_pos_mark)
    var->qpup_mark_pos = 1;
  else
    var->qpup_mark_neg = 1;
}

static void
qpup_mark_var_by_lit (Var *var, LitID lit)
{
  assert ((VarID)LIT2VARID(lit) == var->id);
  if (QDPLL_LIT_NEG (lit))
    qpup_mark_var (var, 0);
  else
    qpup_mark_var (var, 1);
}

static void
qpup_unmark_var (Var *var)
{
  var->qpup_mark_pos = var->qpup_mark_neg = 0;
}

/* Marks used for resolution. */ 

static int
qpup_res_is_var_pos_marked (Var *var)
{
  return var->qpup_res_mark_pos; 
}

static int
qpup_res_is_var_neg_marked (Var *var)
{
  return var->qpup_res_mark_neg; 
}

static int
qpup_res_is_var_marked (Var *var)
{
  return qpup_res_is_var_neg_marked (var) || qpup_res_is_var_pos_marked (var); 
}

static void
qpup_res_mark_var (Var *var, int set_pos_mark)
{
  if (set_pos_mark)
    var->qpup_res_mark_pos = 1;
  else
    var->qpup_res_mark_neg = 1;
}

static void
qpup_res_mark_var_by_lit (Var *var, LitID lit)
{
  assert ((VarID)LIT2VARID(lit) == var->id);
  if (QDPLL_LIT_NEG (lit))
    qpup_res_mark_var (var, 0);
  else
    qpup_res_mark_var (var, 1);
}

static void
qpup_res_unmark_var (Var *var)
{
  var->qpup_res_mark_pos = var->qpup_res_mark_neg = 0;
}

static void
qpup_collect_qpup_node (QDPLL *qdpll, Var *var)
{
  pqueue_insert (qdpll->mm, qdpll->qpup_nodes, var, var->trail_pos);
  assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
  if (!qdpll->qpup_var_at_max_dec_level || qdpll->qpup_var_at_max_dec_level->decision_level < var->decision_level)
    {
      /* Found new maximum decision level. */
      qdpll->qpup_var_at_max_dec_level = var;
      qdpll->qpup_cnt_at_max_dec_level = 1;
    }
  else if (qdpll->qpup_var_at_max_dec_level->decision_level == var->decision_level)
    qdpll->qpup_cnt_at_max_dec_level++;
}

/* Variable 'implied_var' is the implied variable and literal 'lit' occurs in
   the antecedent constraint of 'implied_var'. */
static void
qpup_check_marks_and_collect (QDPLL * qdpll, LitID lit, Var *implied_var, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);

  QDPLLMemMan *mm = qdpll->mm;
  Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);

  if (var->scope->type == type)
    {
      /* Can never see existential (universal) pure literals during CDCL
         (SDCL). E.g. an existential pure literal can only satisfy clauses and
         hence such literal cannot occur in the antecedent clause of an
         existential unit. */
      assert (var->mode != QDPLL_VARMODE_PURE);
      if (!qpup_is_var_marked(var))
        {
          qpup_mark_var_by_lit (var, lit);
          qpup_collect_qpup_node (qdpll, var);
        }
    }
  else
    {
      /* Variable 'var' is universal in CDCL and existential in SDCL. */
      if (!qpup_is_var_marked(var))
        {
          /* Collect universal (existential) literals in CDCL (SDCL) for dependency checking. */
          qpup_mark_var_by_lit (var, lit);
          QDPLL_PUSH_STACK(mm, qdpll->qpup_vars, var);
          /* Collect universal (existential) decision variables. IMPORTANT: we
             might see a universal literal of a decision variable in an
             antecedent although that literal was implicitly reduced during QBCP. In this
             case we do not collect the universal variable if it was assigned at
             a larger decision level. This amount to checking if the literal was
             reduced implicitly. */
          if ((!implied_var || var->decision_level <= implied_var->decision_level) && 
              (var->mode == QDPLL_VARMODE_LBRANCH || var->mode == QDPLL_VARMODE_RBRANCH || 
               var->mode == QDPLL_VARMODE_ASSUMED))
            qpup_collect_qpup_node (qdpll, var);
        }
      else
        qpup_mark_var_by_lit (var, lit);
    }
}

/* Push unmarked variables from literal set 'lits_start,lits_end' onto stack 'qdpll->qpup_nodes'. */
static void
qpup_traverse_implication_graph_push_nodes (QDPLL * qdpll, LitID *lits_start, LitID *lits_end, 
                                      Var *implied_var, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (lits_start || !lits_end);
  assert (lits_start <= lits_end);
  assert (!implied_var || QDPLL_VAR_ASSIGNED(implied_var));
  assert (!implied_var || implied_var->scope->type == type);
  assert (!implied_var || implied_var->mode == QDPLL_VARMODE_UNIT);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "QPUP graph traversal: pushing unmarked nodes from set:\n ");
      print_lits(qdpll, lits_start, lits_end - lits_start, 0);
    }

  LitID *p;
  for (p = lits_start; p < lits_end; p++)
    {
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, *p);
      if (var != implied_var)
        qpup_check_marks_and_collect (qdpll, *p, implied_var, type);
    }
}

/* Select the variable from stack 'qdpll->qpup_nodes' which is largest on
   trail, i.e. which has been propagated most recently. This variable is goint
   to be visited next during the search for a suitable UIP node. After a UIP
   has been found, this function is called to check the remaining nodes on
   stack 'qdpll->qpup_nodes' whether any of them prevents constraint reduction
   of relevant variables. */
static Var *
qpup_select_next_node (QDPLL *qdpll)
{
  Var *result;

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "\nQPUP selecting next node from set (format (id,trailpos)): ");
      PriorityQueueElem *p, *e;
      for (p = qdpll->qpup_nodes->queue, e = p + qdpll->qpup_nodes->cnt; p < e; p++)
        {
          Var *var = p->data;
          fprintf (stderr, "(%d,%d) ", var->id, var->trail_pos);
        }
      fprintf (stderr, "\n");
    }

  result = pqueue_remove_min (qdpll->qpup_nodes);

  if (!qdpll->qpup_uip)
    {
      if (qdpll->qpup_cnt_at_max_dec_level > 0)
        qdpll->qpup_cnt_at_max_dec_level--;
      if (qdpll->qpup_cnt_at_max_dec_level == 1)
        qdpll->qpup_var_at_max_dec_level = pqueue_access_min (qdpll->qpup_nodes);     
    }

 return result;
}

static Var *
qpup_find_unique_var_at_max_dec_level (QDPLL *qdpll)
{
  assert (!qdpll->qpup_uip);

  if (qdpll->qpup_recompute_var_at_max_dec_level)
    {
      qdpll->qpup_recompute_var_at_max_dec_level = 0;
      Var *var_at_max_dec_level = 0;
      unsigned int cnt_at_max_dec_level = 0;
      PriorityQueueElem *p, *e;
      for (p = qdpll->qpup_nodes->queue, e = p + qdpll->qpup_nodes->cnt; p < e; p++)
        {
          Var *var = p->data;
          assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
          if (!var_at_max_dec_level || var_at_max_dec_level->decision_level < var->decision_level)
            {
              /* Found new maximum decision level. */
              var_at_max_dec_level = var;
              cnt_at_max_dec_level = 1;
            }
          else if (var_at_max_dec_level->decision_level == var->decision_level)
            cnt_at_max_dec_level++;
        }
      qdpll->qpup_var_at_max_dec_level = var_at_max_dec_level;
      qdpll->qpup_cnt_at_max_dec_level = cnt_at_max_dec_level;
    }

  /* Explicitly handle decision level 0: if the maximum decision level is 0
     then we want to continue anyway to derive the empty
     constraint. This is relevant only if a trace is printed out. */
  if (!qdpll->qpup_var_at_max_dec_level || qdpll->qpup_var_at_max_dec_level->decision_level == 0)
    return 0;
  else
    {
      assert (qdpll->qpup_var_at_max_dec_level);
      assert (qdpll->qpup_var_at_max_dec_level->decision_level != QDPLL_INVALID_DECISION_LEVEL);
      assert (qdpll->qpup_cnt_at_max_dec_level > 0);
      if (qdpll->qpup_cnt_at_max_dec_level == 1)
        {
          /* Must reset computed maximum var if we are at UIP which is not suitable. */
          assert (!qdpll->qpup_recompute_var_at_max_dec_level);
          qdpll->qpup_recompute_var_at_max_dec_level = 1;
          return qdpll->qpup_var_at_max_dec_level;
        }
      else 
        return 0;
    }
}


/* Check if there is a variable 'u' on stack 'qdpll->qpup_vars' where variable
   'var' depends on. For example, this check is carried out on UIP
   candidates. Since the variable related to the UIP is part of the learnt
   constraint, we have to make sure that this variable does not block
   reduction of literals which would produce a tautology. Additionally, the
   variable of the UIP must be asserted after backtracking. In order to
   produce asserting constraints, we have to make sure that the UIP variable
   does not depend on variables of the other type which are assigned at equal
   or larger decision level than the decision level of the UIP. Such variables
   would be unassigned after backtracking and prevent the constraint from
   being asserting. */
static Var *
qpup_check_dependency (QDPLL *qdpll, Var *var, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (var->scope->type == type);
  QDPLLDepManGeneric *dm = qdpll->dm;
  const unsigned int long_dist_res = qdpll->options.long_dist_res;

  Var **p, **e;
  for (p = qdpll->qpup_vars.start, e = qdpll->qpup_vars.top; p < e; p++)
    {
      Var *u = *p;
      assert (qpup_is_var_neg_marked (u) || qpup_is_var_pos_marked (u));
      assert (u->scope->type != type);

      if (!long_dist_res && qpup_is_var_neg_marked (u) && qpup_is_var_pos_marked (u))
        {
          /* Positive and negative literals of variable 'u' were collected:
             check whether 'u' would make learnt clause a tautology. A
             tautology would be produced if 'var' prevents reduction of
             'u'. If so, then 'var' has to be resolved out. */

          /* When using QPUP-based long-distance resolution, we never
             enter this branch. */

          if (dm->depends(dm, u->id, var->id))
            return u;
        }
      else if (!qdpll->qpup_uip)
        {
          /* If 'qdpll->qpup_uip' is NULL then we haven't found the UIP and we
             must check if the UIP candidate depends on a collected universal
             variable which appeared in only one phase. If so then the candidate
             is no UIP since the resulting clause would not be
             asserting. Otherwise if 'qdpll->qpup_uip' is not NULL then this
             function is called from function '...check_remaining_nodes...' on
             open, unvisited nodes on stack 'qdpll->qpup_nodes'. No dependency
             checking is required in this case since these nodes are all assigned
             at smaller decision levels than the decision level of the UIP node,
             since we traverse the graph in reverse trail ordering. Note that
             tautology checking is handled in the if-branch above. This branch
             affects only the criteria for producing asserting constraints. */

          /* Either only positive or only negative literals of variable 'u'
             were collected, i.e. literals of 'u' would not produce a
             tautology; check whether 'u' would prevent learnt clause from
             being asserting. */

          if ((!(QDPLL_VAR_ASSIGNED(u) && u->decision_level < var->decision_level)) 
              && dm->depends(dm, u->id, var->id))
            return u;
        }
    }

  return 0;
}

/* Returns zero if no proper UIP was found and a pointer to the UIP
   otherwise. The stack 'qdpll->qpup_nodes' is inspected for that purpose. A
   node is a suitable UIP if (1) it is the only node assigned at the highest
   decision level among all nodes on the stack, (2) if it is assigned at an
   existential/universal decision level during CDCL/SDCL and (3) if it does
   not prevent the reduction of tautology-producing literals or literals which
   prevent asserting learnt constraints. These three conditions are checked in
   this function. If a suitable UIP was found, then the traversal in function
   'find_relevant_uip' will stop. */
static Var *
qpup_find_and_check_uip_candidate(QDPLL *qdpll, const QDPLLQuantifierType type)
{
  /* Check whether the relevant 1-UIP node was found, which is similar
     to the stop-criteria in classical CDCL. */
  Var *uip_candidate = qpup_find_unique_var_at_max_dec_level (qdpll);

  if (uip_candidate)
    {
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "QPUP UIP search: node %d is a UIP candidate.\n", uip_candidate->id);
          
      /* At this point, variable 'unique_var_at_max_dec_level' is a
         UIP candidate. */

      /* Check if 'uip_candidate' is assigned at a decision level
         where the decision variable is existential (universal) in CDCL (SDCL). */
      assert (uip_candidate->decision_level >= 1);
      assert (uip_candidate->mode == QDPLL_VARMODE_UNIT || 
              uip_candidate->mode == QDPLL_VARMODE_LBRANCH || uip_candidate->mode == QDPLL_VARMODE_RBRANCH);
      Var *decision_var =
        VARID2VARPTR (qdpll->pcnf.vars,
                      qdpll->dec_vars.start[uip_candidate->decision_level - 1]);
      assert (decision_var->decision_level == uip_candidate->decision_level);
      assert (decision_var->mode == QDPLL_VARMODE_LBRANCH
              || decision_var->mode == QDPLL_VARMODE_RBRANCH);
      if (decision_var->scope->type == type)
        {
          assert (uip_candidate->scope->type == type);

          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "QPUP UIP search: candidate %d passed level check.\n", uip_candidate->id);

          Var *depends_on;
          if (!(depends_on = qpup_check_dependency (qdpll, uip_candidate, type)))
            {
              if (qdpll->options.verbosity >= 2)
                fprintf (stderr, "QPUP UIP search: candidate %d passed dependency check, UIP found.\n", uip_candidate->id);
              /* Relevant UIP found, abort traversal. */
              assert (!qdpll->qpup_uip);
              qdpll->qpup_uip = uip_candidate;
              return uip_candidate;
            }
          else
            {
              if (qdpll->options.verbosity >= 2)
                fprintf (stderr, "QPUP UIP search: candidate %d depends on variable %d, continuing.\n", uip_candidate->id, depends_on->id);
              return 0;
            }
        }
      else
        {
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "QPUP UIP search: candidate %d failed level check, continuing.\n", uip_candidate->id);
          return 0;
        }
    }
  else
    {
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "QPUP UIP search: no suitable UIP candidate found, continuing.\n");
      return 0;
    }
}

static void
qpup_collect_weak_predict_lits (QDPLL *qdpll, Var *var, LitID lit, const QDPLLQuantifierType type);

static void
qpup_find_relevant_uip (QDPLL *qdpll, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "QPUP: UIP search started.\n");

  /* First phase: traverse implication graph and find the relevant UIP. The
     relevant UIP is the variable which will be asserted after backtracking. */

  Var *cur;
  while (!qpup_find_and_check_uip_candidate(qdpll, type) && (cur = qpup_select_next_node (qdpll)))
    {
      assert (QDPLL_VAR_ASSIGNED(cur));
      assert (cur->mode == QDPLL_VARMODE_LBRANCH || cur->mode == QDPLL_VARMODE_RBRANCH || 
              cur->mode == QDPLL_VARMODE_UNIT || 
              (qdpll->state.assumptions_given && cur->mode == QDPLL_VARMODE_ASSUMED));

      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "\nQPUP UIP search: cur node = %d, decision level %d, trail position %d\n", 
                 cur->id, cur->decision_level, cur->trail_pos);

      if (cur->mode == QDPLL_VARMODE_LBRANCH || cur->mode == QDPLL_VARMODE_RBRANCH || 
          cur->mode == QDPLL_VARMODE_ASSUMED)
        {
          assert (cur->mode != QDPLL_VARMODE_ASSUMED || qdpll->state.assumptions_given);
          /* Variable 'cur' was assigned as decision or assumption. */
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "QPUP UIP search: cur node %d is %s.\n", cur->id, 
                     cur->mode == QDPLL_VARMODE_ASSUMED ? "assumption" : "decision");
          if (cur->mode == QDPLL_VARMODE_ASSUMED && cur->scope->type == type && 
              !qdpll->options.no_lazy_qpup)
            qpup_collect_weak_predict_lits (qdpll, cur, 0, type);
        }
      else
        {
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "QPUP UIP search: cur node %d is a unit, pushing predecessors.\n", cur->id);
          assert (cur->mode == QDPLL_VARMODE_UNIT);
          assert (cur->scope->type == type);
          assert (cur->antecedent);
          assert (!cur->antecedent->qbcp_qbce_blocked);
          /* Collect literals of 'cur' antecedent, ignoring 'cur' itself. */
          qpup_traverse_implication_graph_push_nodes (qdpll, 
                                                cur->antecedent->lits, 
                                                cur->antecedent->lits + cur->antecedent->num_lits, 
                                                cur, type);
          /* Collect traversed units on separate stack. That is used later for
             the actual production of QPUP clauses. */
          QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_units, cur);
        }
    }

  /* NOTE: if 'qdpll->qpup_uip' is NULL after the while-loop then the empty constraint will be
     derived in the end. */
  if (qdpll->options.verbosity >= 2)
    {
      if (!qdpll->qpup_uip)
        fprintf (stderr, "QPUP UIP search: no proper UIP found; expecting derivation "\
                 "of the empty constraint or asserting initial cube.\n");
      fprintf (stderr, "QPUP: UIP search completed.\n");
    }
}

static void
qpup_collect_weak_predict_lits_push (QDPLL *qdpll, Var *var, LitID lit)
{
  if (var->is_internal)
    QDPLL_PUSH_STACK(qdpll->mm, qdpll->internal_cover_lits, lit);
  else if (var->user_scope)
    QDPLL_PUSH_STACK(qdpll->mm, var->user_scope->cover_lits, lit);
  else
    {
      assert (var->scope == qdpll->pcnf.scopes.first);
      QDPLL_PUSH_STACK(qdpll->mm, var->scope->cover_lits, lit);
    }
}

static void
qpup_collect_weak_predict_lits (QDPLL *qdpll, Var *var, LitID lit, const QDPLLQuantifierType type)
{
  assert (!qdpll->options.no_lazy_qpup);
  /* Handle assumptions in lazy QPUP: we allow this function to be called
     BEFORE UIP is found, but only to collect existential (universal)
     assumptions in CDCL (SDCL) during UIP search. This is needed only if no
     UIP is found under assumptions, i.e. an assumption-constraint will be
     derived. */
  assert (qdpll->qpup_uip || 
          (var->mode == QDPLL_VARMODE_ASSUMED && var->scope->type == type));
  assert (!lit || var == LIT2VARPTR(qdpll->pcnf.vars, lit));
  if (!lit)
    {
      /* Workaround: need to figure out phase of literal to be collected in
         certain cases. */
      lit = var->id;
      if (type == QDPLL_QTYPE_EXISTS)
        {
          if (var->assignment == QDPLL_ASSIGNMENT_TRUE)
            lit = -lit;
        }
      else if (var->assignment == QDPLL_ASSIGNMENT_FALSE)
        lit = -lit;
    }

  if (var->scope->type == type)
    {
      /* In CDCL (SDCL), 'var' is existential (universal). */
      /* Here, no double pushing can occur. */
      assert (!var->qpup_neg_predict_mark);
      assert (!var->qpup_pos_predict_mark);
      if (QDPLL_LIT_NEG (lit))
        var->qpup_neg_predict_mark = 1;
      else
        var->qpup_pos_predict_mark = 1;
      if (var->is_internal)
        QDPLL_PUSH_STACK(qdpll->mm, qdpll->internal_cover_lits, lit);
      else if (var->user_scope)
        QDPLL_PUSH_STACK(qdpll->mm, var->user_scope->cover_lits, lit);
      else
        {
          assert (var->scope == qdpll->pcnf.scopes.first);
          QDPLL_PUSH_STACK(qdpll->mm, var->scope->cover_lits, lit);
        }
    }
  else
    {
      /* In CDCL (SDCL), 'var' is universal (existential). */
      /* Skip literals which would produce a tautology; they will not occur in
         the learned constraint. */
      if (!qdpll->options.long_dist_res && 
          qpup_is_var_pos_marked(var) && qpup_is_var_neg_marked(var))
        return;
      /* Skip literals where the UIP variable depends on AND which are (1)
         either unassigned or (2) assigned at a larger or equal decision level
         than the UIP variable. Such literals would become unassigned after
         backtracking to the asserting level and thus the learned constraint
         would not be asserting. Hence these literals cannot occur in the
         learned clause. */
      if ((!(QDPLL_VAR_ASSIGNED(var) && var->decision_level < qdpll->qpup_uip->decision_level)) 
          && qdpll->dm->depends(qdpll->dm, var->id, qdpll->qpup_uip->id))
        return;
      /* Otherwise, collect literal if not already present. Must also handle
         long-distance resolution by possibly collecting complementary
         universal literals. Note that universal literals may be collected
         here (even complementary ones when not using long-distance
         resolution) although they may be universal-reduced from the clause to
         be learned in the end. */
      if (QDPLL_LIT_NEG (lit))
        {
          if (!var->qpup_neg_predict_mark)
            {
              var->qpup_neg_predict_mark = 1;
              qpup_collect_weak_predict_lits_push (qdpll, var, lit);
            }
        }
      else
        {
          assert (QDPLL_LIT_POS (lit));
          if (!var->qpup_pos_predict_mark)
            {
              var->qpup_pos_predict_mark = 1;
              qpup_collect_weak_predict_lits_push (qdpll, var, lit);
            }
        }
    }
}

static void
qpup_collect_weak_predict_lits_aux_collect (QDPLL *qdpll, LitIDStack *cover_lits, 
                                            const QDPLLQuantifierType type)
{
  LitID kept_selector_lit = 0;
  Var *kept_selector_var = 0;
  const unsigned int clause_group_api_called = qdpll->state.clause_group_api_called;

  LitID *p, *e;
  for (p = cover_lits->start, e = cover_lits->top; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      assert (cover_lits == &qdpll->internal_cover_lits || !var->is_internal);
      assert (cover_lits != &qdpll->internal_cover_lits || var->is_internal);
      assert (var->qpup_neg_predict_mark || var->qpup_pos_predict_mark);
      if (QDPLL_LIT_NEG (lit))
        {
          assert (var->qpup_neg_predict_mark);
          var->qpup_neg_predict_mark = 0;
        }
      if (QDPLL_LIT_POS (lit))
        {
          assert (var->qpup_pos_predict_mark);
          var->qpup_pos_predict_mark = 0;
        }
      if (clause_group_api_called)
        {
          /* Cannot use "KEEP-ONE_SELECTOR-LITERAL" optimization if clause
             groups are used. */
          QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_weak_predict_lits, lit);
          if (!qdpll->options.bump_vars_once)
            increase_var_activity (qdpll, var, var->scope);
        }
      else
        {
          if (var->is_internal && type == QDPLL_QTYPE_EXISTS)
            {
              assert (!var->is_internal || 
                      (QDPLL_LIT_NEG(lit) && QDPLL_VAR_ASSIGNED_TRUE(var)) || 
                      (QDPLL_LIT_POS(lit) && QDPLL_VAR_ASSIGNED_FALSE(var)));
              assert (var->scope == qdpll->pcnf.scopes.first);
              assert (var->clause_group_id > 0);
              assert (qdpll->state.cur_used_internal_vars.start[var->clause_group_id - 1] == var->id);
              if (!kept_selector_var || kept_selector_var->clause_group_id < var->clause_group_id)
                {
                  kept_selector_var = var;
                  kept_selector_lit = lit;
                }
            }
          else
            {
              /* Same code as in branch 'if (clause_group_api_called)' above. */
              QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_weak_predict_lits, lit);
              if (!qdpll->options.bump_vars_once)
                increase_var_activity (qdpll, var, var->scope);
            }
        }
    }
  if (!clause_group_api_called)
    {
      if (kept_selector_var)
        {
          assert (type == QDPLL_QTYPE_EXISTS);
          assert (cover_lits == &qdpll->internal_cover_lits);
          assert (kept_selector_lit);
          /* Same code as in branch 'if (clause_group_api_called)' above. */
          QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_weak_predict_lits, kept_selector_lit);
          if (!qdpll->options.bump_vars_once)
            increase_var_activity (qdpll, kept_selector_var, kept_selector_var->scope);
          kept_selector_var = 0;
          kept_selector_lit = 0;
        }
    }
  QDPLL_RESET_STACK(*cover_lits);
}


static void
qpup_collect_weak_predict_lits_aux (QDPLL *qdpll, LitIDStack *empty_constraint_lits, const QDPLLQuantifierType type)
{
  assert (!qdpll->options.no_lazy_qpup);
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_weak_predict_lits));
  Var *vars = qdpll->pcnf.vars;

  /* If a UIP was found then check visited units and their antecedents to
     collect relevant literals. If no UIP was found (i.e. we will derive the
     empty constraint) then still we have to traverse used antecedents to unmark
     the variables. */

  /* A predicted literal 'lit' will be pushed on the stack
     'cover_lits' in its scope 'var(lit)->scope'. This way, we can
     collect all predicted literals in sorted order already, no explicit
     sorting is necessary. */

  if (!QDPLL_EMPTY_STACK(qdpll->qpup_units))
    {
      Var **vp, **ve;
      for (vp = qdpll->qpup_units.top - 1, ve = qdpll->qpup_units.start; ve <= vp; vp--)
        {
          Var *var = *vp;
          assert (var->antecedent);
          assert (!var->antecedent->qbcp_qbce_blocked);
          if (!qdpll->options.bump_vars_once)
            learnt_constraint_mtf (qdpll, var->antecedent);
          LitID *p, *e;
          for (p = var->antecedent->lits, e = p + var->antecedent->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *v = LIT2VARPTR(vars, lit);
              if (!qdpll->options.bump_vars_once)
                increase_var_activity (qdpll, v, v->scope);
              qpup_unmark_var (v);
              /* If UIP found: collect universal (existential) variables in CDCL (SDCL). */
              if (v->scope->type != type && qdpll->qpup_uip)
                qpup_collect_weak_predict_lits (qdpll, v, lit, type);
            }
        }
    }

  LitID *p, *e;
  for (p = empty_constraint_lits->start, e = empty_constraint_lits->top; p < e; p++)
    {
      LitID lit = *p;
      Var *v = LIT2VARPTR(vars, lit);
      if (!qdpll->options.bump_vars_once)
        increase_var_activity (qdpll, v, v->scope);
      qpup_unmark_var (v);
      /* If UIP found: collect universal (existential) variables in CDCL (SDCL). */
      if (v->scope->type != type && qdpll->qpup_uip)
        qpup_collect_weak_predict_lits (qdpll, v, lit, type);
    }

  /* First, import internal variables collected on separate stack. */
  qpup_collect_weak_predict_lits_aux_collect (qdpll, &qdpll->internal_cover_lits, type);
  /* Then collect variables from default scope. */
  qpup_collect_weak_predict_lits_aux_collect (qdpll, &qdpll->pcnf.scopes.first->cover_lits, type);

  /* Push collected literals in order of scopes on stack
     'qdpll->qpup_weak_predicted_lits'. */
  Scope *s;
  for (s = qdpll->pcnf.user_scopes.first; s; s = s->link.next)
    qpup_collect_weak_predict_lits_aux_collect (qdpll, &s->cover_lits, type);
#ifndef NDEBUG
  assert_lits_sorted (qdpll, qdpll->qpup_weak_predict_lits.start, 
                      qdpll->qpup_weak_predict_lits.top);
#endif
}


/* Print information about a literal which will definitely occur in
   the learned clause. This function considers only existential
   (universal) literals in CDCL (SDCL).*/
static void
qpup_print_info_kept_literals (QDPLL *qdpll, Var * var, const QDPLLQuantifierType type)
{
  const char *type_string = type == QDPLL_QTYPE_EXISTS ? 
    "QPUP predict exist." : "QPUP predict univ.";
  LitID lit = var->id;
  if (type == QDPLL_QTYPE_EXISTS)
    {
      if (var->assignment == QDPLL_ASSIGNMENT_TRUE)
        lit = -lit;
    }
  else if (var->assignment == QDPLL_ASSIGNMENT_FALSE)
    lit = -lit;
  fprintf (stderr, "%s lit. %d: DEFINITELY IN\n", type_string, lit);
  /* Here, no double pushing can occur. */
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_kept_lits, lit);
}


/* After the UIP has been found, check whether there are nodes on stack
   'qdpll->qpup_nodes' which would prevent the production of an asserting
   constraint or which would prevent the reduction of literals yielding
   tautologies. */
static void
qpup_check_remaining_nodes (QDPLL *qdpll, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "\nQPUP: node checking started on %u remaining nodes.\n", (unsigned int)qdpll->qpup_nodes->cnt);

  /* Second phase: check remaining nodes on stack. */

  Var *cur;
  while ((cur = qpup_select_next_node (qdpll)))
    {
      assert (qdpll->qpup_uip);
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "QPUP node checking: cur node = %d, decision level %d, trail position %d\n", 
                 cur->id, cur->decision_level, cur->trail_pos);

      /* Ignore found UIP. */
      if (cur == qdpll->qpup_uip)
        {
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "QPUP node checking: cur node is found UIP, skip.\n");
              qpup_print_info_kept_literals (qdpll, cur, type);
            }
          if (!qdpll->options.no_lazy_qpup)
            qpup_collect_weak_predict_lits (qdpll, cur, 0, type);
          continue;
        }

      assert (QDPLL_VAR_ASSIGNED(cur));
      assert (QDPLL_VAR_ASSIGNED(qdpll->qpup_uip));
      assert (cur->decision_level < qdpll->qpup_uip->decision_level);

      if (cur->mode == QDPLL_VARMODE_LBRANCH || cur->mode == QDPLL_VARMODE_RBRANCH || 
          cur->mode == QDPLL_VARMODE_ASSUMED)
        {
          /* Variable 'cur' was assigned as decision or assumption. */
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "QPUP node checking: cur node %d is %s.\n", cur->id, cur->mode == QDPLL_VARMODE_ASSUMED ? "assumption" : "decision");
              qpup_print_info_kept_literals (qdpll, cur, type);
            }
          if (!qdpll->options.no_lazy_qpup)
            qpup_collect_weak_predict_lits (qdpll, cur, 0, type);
        }
      else
        {
          assert (cur->mode == QDPLL_VARMODE_UNIT);
          assert (cur->scope->type == type);

          Var *depends_on;
          if (!(depends_on = qpup_check_dependency (qdpll, cur, type)))
            {
              /* Variable 'cur' was assigned as unit but does not prevent constraint reduction. */
              if (qdpll->options.verbosity >= 2)
                {
                  fprintf (stderr, "QPUP node checking: cur node %d does not prevent reduction.\n", cur->id);
                  qpup_print_info_kept_literals (qdpll, cur, type);
                }
              if (!qdpll->options.no_lazy_qpup)
                qpup_collect_weak_predict_lits (qdpll, cur, 0, type);
            }
          else
            {
              if (qdpll->options.verbosity >= 2 && depends_on)
                fprintf (stderr, "QPUP node checking: cur node %d prevents reduction of %d, pushing predecessors.\n", cur->id, depends_on->id);

              /* There is a universal vars on stack 'qdpll->qpup_vars'
                 where 'cur' depends on. That is, 'cur' would prevent
                 universal reduction of that variable during QPUP. Continue
                 traversal until literals which block universal reduction are
                 resolved out. Collect literals like in first phase. See also 
                 function 'qpup_check_dependency(...)' for additional comments. */
              assert (cur->antecedent);
              assert (!cur->antecedent->qbcp_qbce_blocked);
              qpup_traverse_implication_graph_push_nodes (qdpll, 
                                                    cur->antecedent->lits, 
                                                    cur->antecedent->lits + cur->antecedent->num_lits, 
                                                    cur, type);
              /* Collect traversed units on separate stack. That is used later for
                 the actual production of QPUP clauses. */
              QDPLL_PUSH_STACK(qdpll->mm, qdpll->qpup_units, cur);
            }
        }
    }

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "QPUP: node checking completed.\n");
}


/* Called from function 'qpup_print_info_literals_aux(...)'. */
static void
qpup_print_info_literals (QDPLL *qdpll, LitID lit, LitID *ante_lits_start, 
                          LitID *ante_lits_end, const QDPLLQuantifierType type)
{
  assert (qdpll->options.verbosity >= 2);
  assert (ante_lits_start <= ante_lits_end);
  assert (qdpll->qpup_uip);
  assert (QDPLL_VAR_ASSIGNED(qdpll->qpup_uip));
  Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
  const char *type_string = type == QDPLL_QTYPE_EXISTS ? "QPUP predict univ." : "QPUP predict exist.";

  /* This function ignores existential (universal) literals in CDCL (SDCL). */
  if ((type == QDPLL_QTYPE_EXISTS && !QDPLL_VAR_FORALL(var)) || 
      (type == QDPLL_QTYPE_FORALL && !QDPLL_VAR_EXISTS(var)))
    return;

  /* A universal literal will DEFINITELY NOT occur in the learned
     clause if it would produce a tautology (i.e. its variable has
     complementary marks set) or if the UIP variable depends on it and
     the universal variable would become unassigned after
     backtracking. */
  if (qpup_is_var_pos_marked(var) && qpup_is_var_neg_marked(var))
    {
      /* The literal's variable would produce a tautology. */
      if (!qdpll->options.long_dist_res)
        fprintf (stderr, " %s lit. %d compl. occs: DEFINITELY OUT\n", type_string, lit);
      else
        fprintf (stderr, " %s lit. %d compl. occs: MAYBE IN\n", type_string, lit);
    }
  else
    {
      /* Check if there is a literal in the antecedent which definitely
         prevents reduction of 'var'. */
      LitID *p, *e;
      for (p = ante_lits_start, e = ante_lits_end; p < e; p++)
        {
          Var *v = LIT2VARPTR(qdpll->pcnf.vars, *p);
          if (v->scope->type != var->scope->type && qdpll->dm->depends (qdpll->dm, var->id, v->id))
            {
              /* Variable 'v' in the antecedent would prevent reduction of
                 'var'. Check if 'v' was collected on stack 'qpup_kept_lits' as
                 'DEFINITELY IN' the learned clause. In this case, both variables 
                 'var' and 'v' will be carried over during QPUP computations to
                 the final learned constraint. */
              LitID *p1, *e1;
              for (p1 = qdpll->qpup_kept_lits.start, e1 = qdpll->qpup_kept_lits.top; p1 < e1; p1++)
                {
                  Var *v1 = LIT2VARPTR(qdpll->pcnf.vars, *p1);
                  if (v == v1)
                    break;
                }
              if (p1 < e1)
                {
                  fprintf (stderr, " %s lit. %d < %d: DEFINITELY IN\n", type_string, lit, *p1);
                  break;
                }
            }
        }
      /* Variables labelled as 'MAYBE IN' may or may not occur in the learned
         clause: we were not able to make a definite decision at this point based
         on local information in the antecedent only. However, it should never be
         the case that the learned clause contains a universal which was neither
         labelled 'DEFINITELY IN' nor 'MAYBE IN'. */
      if (p == e)
        fprintf (stderr, " %s lit. %d: MAYBE IN\n", type_string, lit);
    }
}


/* Check antecedent constraints and empty constraint for literals which
   definitely (not) occur or may occur in the learned constraint. */
static void
qpup_print_info_literals_aux (QDPLL *qdpll, LitIDStack *empty_constraint_lits, const QDPLLQuantifierType type)
{
  if (!qdpll->qpup_uip)
    return;
  assert (qdpll->options.verbosity >= 2);

  fprintf (stderr, "\nQPUP predicting %s literals:\n", type == QDPLL_QTYPE_EXISTS ? "universal" : "existential");

  if (!QDPLL_EMPTY_STACK(qdpll->qpup_units))
    {
      Var **vp, **ve;
      for (vp = qdpll->qpup_units.top - 1, ve = qdpll->qpup_units.start; ve <= vp; vp--)
        {
          Var *var = *vp;
          assert (var->antecedent);
          assert (!var->antecedent->qbcp_qbce_blocked);
          LitID *p, *e;
          for (p = var->antecedent->lits, e = p + var->antecedent->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *v = LIT2VARPTR(qdpll->pcnf.vars, lit);
              qpup_print_info_literals (qdpll, lit, var->antecedent->lits, 
                                        var->antecedent->lits + var->antecedent->num_lits, type);
            }
        }
    }

  LitID *p, *e;
  for (p = empty_constraint_lits->start, e = empty_constraint_lits->top; p < e; p++)
    {
      LitID lit = *p;
      Var *v = LIT2VARPTR(qdpll->pcnf.vars, lit);
      qpup_print_info_literals (qdpll, lit, empty_constraint_lits->start, empty_constraint_lits->top, type);
    }

  fprintf (stderr, "QPUP predicting %s literals completed.\n", type == QDPLL_QTYPE_EXISTS ? "universal" : "existential");
}

/* Traverse the implication graph backwards starting from the empty clause. In
   CDCL, existential units and decisions are nodes to be visited. */
static void
qpup_traverse_implication_graph (QDPLL *qdpll, LitIDStack *constraint_lits, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  /* Initialize search: collect nodes to be visited from empty constraint. */
  qpup_traverse_implication_graph_push_nodes (qdpll, constraint_lits->start, constraint_lits->top, 0, type);
  /* Find the relevant UIP. */
  qpup_find_relevant_uip (qdpll, type);
  /* Check unvisited nodes on the stack which would prevent
     universal reduction during QPUP computation. */
  qpup_check_remaining_nodes (qdpll, type);

  if (qdpll->options.verbosity >= 2)
    qpup_print_info_literals_aux (qdpll, constraint_lits, type);
}

/* For assertion checking only; Returns non-zero iff literal 'lit' is
   contained in the array of literals bounded by 'start' and 'end'. */
static int 
qpup_res_find_lit (LitID *start, LitID *end, LitID lit)
{
  assert (start <= end);

  LitID *p;
  for (p = start; p < end; p++)
    if (*p == lit)
      return 1;

  return 0;
}

/* For assertion checking only: returns non-zero if the literal set contains
   duplicate literals. */
static int
qpup_has_duplicate_lits (LitID *start, LitID *end)
{
  assert (start <= end);

  LitID *p;
  for (p = start; p < end; p++)
    {
      LitID lit = *p;
      if (qpup_res_find_lit (p + 1, end, lit))
        return 1;
    }

  return 0;
}


/* For assertion checking only: returns non-zero if the literal set is
   a tautology. */
static int
qpup_is_tautology (LitID *start, LitID *end)
{
  assert (start <= end);

  LitID *p;
  for (p = start; p < end; p++)
    {
      LitID lit = *p;
      if (qpup_res_find_lit (start, end, -lit))
        return 1;
    }

  return 0;
}

static void
qpup_res_reduce_by_depschemes_aux (QDPLL *qdpll, LitID lit, const QDPLLQuantifierType type)
{
  Var *vars = qdpll->pcnf.vars;
  Var *var = LIT2VARPTR(vars, lit);
  const QDPLLQuantifierType var_type = var->scope->type;
  QDPLLMemMan *mm = qdpll->mm;

  if (QDPLL_LIT_NEG (lit))
    LEARN_VAR_NEG_MARK (var);
  else
    LEARN_VAR_POS_MARK (var);

  assert (qdpll->state.decision_level != 0 || var->decision_level == 0 ||
          var->decision_level == QDPLL_INVALID_DECISION_LEVEL);
  assert (LEARN_VAR_MARKED (var));
  assert (QDPLL_LIT_POS (lit) || LEARN_VAR_NEG_MARKED (var));
  assert (QDPLL_LIT_NEG (lit) || LEARN_VAR_POS_MARKED (var));

  if (var_type == QDPLL_QTYPE_FORALL)
    {
      Var *rep = VARID2VARPTR (vars,  
                               qdpll->dm->get_class_rep (qdpll->dm,
                                                         var->id, 0));
      if (!QDPLL_VAR_POS_MARKED (rep))
        {
          QDPLL_VAR_POS_MARK (rep);
          assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) == 0);
          QDPLL_PUSH_STACK (mm, qdpll->wreason_a, rep);
        }
      /* Collect class members. */
      QDPLL_PUSH_STACK (mm, rep->type_red_member_lits, lit);
    }
  else
    {
      /* NOTE: here 'type == EXISTS' means that we do CDCL and
         hence must forall-reduce clauses, and 'type == FORALL'
         indicates SDCL and exists-reducing cubes. */
      Var *rep = type == QDPLL_QTYPE_FORALL ? 
        VARID2VARPTR (vars, qdpll->dm->get_class_rep (qdpll->dm, var->id, 1)) :
        VARID2VARPTR (vars, qdpll->dm->get_class_rep (qdpll->dm, var->id, 0));
      if (!QDPLL_VAR_POS_MARKED (rep))
        {
          QDPLL_VAR_POS_MARK (rep);
          assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) == 0);
          QDPLL_PUSH_STACK (mm, qdpll->wreason_e, rep);
        }
      /* Collect class members. */
      QDPLL_PUSH_STACK (mm, rep->type_red_member_lits, lit);
    }
}


static void
qpup_res_reduce_by_depschemes (QDPLL *qdpll, LitIDStack *stack, const QDPLLQuantifierType type)
{
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));

  LitIDStack tmp;
  QDPLL_INIT_STACK(tmp);
  LitIDStack *tmp_p = &tmp;

  /* Collect data to be used in function 'typ_reduce'. */
  LitID *p, *e;
  for (p = stack->start, e = stack->top; p < e; p++)
    qpup_res_reduce_by_depschemes_aux (qdpll, *p, type);

  qdpll->dm->reduce_lits (qdpll->dm, &stack, &tmp_p, type, 1);

  for (p = stack->start, e = stack->top; p < e; p++)
    LEARN_VAR_UNMARK (LIT2VARPTR(qdpll->pcnf.vars, *p));

  QDPLL_DELETE_STACK(qdpll->mm, *tmp_p);

  *tmp_p = *stack;
}


/* Constraint reduction. */
static void
qpup_res_reduce (QDPLL *qdpll, LitIDStack *stack, const ConstraintID trace_id, const QDPLLQuantifierType type)
{
#ifndef NDEBUG
  assert_lits_sorted (qdpll, stack->start, stack->top);
  do{
    Var *p, *e;
    for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
      {
        assert (!LEARN_VAR_MARKED(p));
        assert (!QDPLL_VAR_MARKED(p));
      }
  } while(0);
#endif

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, " QPUP res-reduce: sorted constraint: ");
      print_lits (qdpll, stack->start, QDPLL_COUNT_STACK(*stack), 0);
    }

  unsigned int num_lits_before_red = QDPLL_COUNT_STACK(*stack);

  /* Cut off trailing literals of universal/existential variables, which
     corresponds to reductions by the trivial dependency scheme. This is always
     possible to the hierarchy of dependency schemes induced by subset relationship. */
  while (QDPLL_COUNT_STACK(*stack))
    {
      Var *v = LIT2VARPTR(qdpll->pcnf.vars, *(stack->top - 1));
      if (!v->is_internal && v->scope->type != type)
        {
          QDPLL_POP_STACK(*stack);
          assert (!LEARN_VAR_MARKED (v));
          qpup_res_unmark_var(v);
        }
      else 
        break;
    }

  /* Additionally, perform dependency scheme specific reductions. */
  if (!qdpll->options.depman_simple)
    qpup_res_reduce_by_depschemes (qdpll, stack, type);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, " QPUP res-reduce: reduced constraint: ");
      print_lits (qdpll, stack->start, QDPLL_COUNT_STACK(*stack), 0);
    }

  if (qdpll->options.trace)
    {
      if (QDPLL_COUNT_STACK(*stack) < num_lits_before_red)
        {
          /* Trace reduced constraint. */
          qdpll->cur_constraint_id++;
          qdpll->trace_constraint (qdpll->cur_constraint_id, stack->start,
                                   QDPLL_COUNT_STACK (*stack), trace_id, 0);
        }
      else
        assert (QDPLL_COUNT_STACK(*stack) == num_lits_before_red);
    }
}

/* Parameter 'check_marks == false' if we collect a marked literal
   which is part of the working reason already. Only push the literal on
   the stack. Otherwise, a potentially unseen literal is marked and collected. */
static void
qpup_res_merge_lits_aux (QDPLL *qdpll, QDPLLMemMan *mm, Var *vars, LitIDStack *stack, 
                         LitID lit, Var *pivot, const int check_marks)
{
  Var *v = LIT2VARPTR(vars, lit);
  assert (qdpll->options.long_dist_res || 
          !(qpup_res_is_var_pos_marked(v) && qpup_res_is_var_neg_marked(v)));
  /* Ignore literal of pivot variable. */
  if (v != pivot)
    {
      /* Additional safeguard: must not add complementary literals. */
      QDPLL_ABORT_QDPLL (!qdpll->options.long_dist_res &&
                         ((QDPLL_LIT_NEG(lit) && qpup_res_is_var_pos_marked(v)) || 
                          (QDPLL_LIT_POS(lit) && qpup_res_is_var_neg_marked(v))), 
                         "fatal error: generated tautology!");
      if (check_marks)
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (!qpup_res_is_var_neg_marked(v))
                {
                  qpup_res_mark_var (v, 0);
                  QDPLL_PUSH_STACK(mm, *stack, lit);
                  if (!qdpll->options.bump_vars_once)
                    increase_var_activity (qdpll, v, v->scope);
                }
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (!qpup_res_is_var_pos_marked(v))
                {
                  qpup_res_mark_var (v, 1);
                  QDPLL_PUSH_STACK(mm, *stack, lit);
                  if (!qdpll->options.bump_vars_once)
                    increase_var_activity (qdpll, v, v->scope);

                }
            }
        }
      else
        {
          assert (qpup_res_is_var_marked(v));
          QDPLL_PUSH_STACK(mm, *stack, lit);
        }
    }
  else
    qpup_res_unmark_var(v);
}

/* Perform one step of Q-resolution without reduction. Reduction is done by
   function 'qpup_res_reduce(...)'. Assumption: literals in 'start1,end1' are
   already marked and will be collected without mark testing. Literals from
   'start2,end2' are pushed onto the stack only if not marked already. This
   way, it is possible to keep variables marked across different calls of this
   function. After the final resolvent has been produced, variables are
   unmarked. */
static void
qpup_res_merge_literals (QDPLL *qdpll, Var *pivot, LitIDStack *resolvent_lits, 
                         LitID *start1, LitID *end1, Constraint *antecedent2, const QDPLLQuantifierType type)
{
#if COMPUTE_STATS
  if (type == QDPLL_QTYPE_EXISTS)
    qdpll->stats.num_unsat_res_steps++;
  else
    qdpll->stats.num_sat_res_steps++;
#endif

  const unsigned int long_dist_res = qdpll->options.long_dist_res;

  LitID *start2 = antecedent2->lits;
  LitID *end2 = start2 + antecedent2->num_lits;

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "  QPUP merge-literals: pivot %d\n", pivot->id);
      fprintf (stderr, "   side constraint 1: ");
      print_lits(qdpll, start1, end1 - start1, 0);
      fprintf (stderr, "   side constraint 2: ");
      print_lits(qdpll, start2, end2 - start2, 0);
    }

  assert (start1 < end1);
  assert (start2 < end2);
#ifndef NDEBUG
  assert_lits_sorted (qdpll, start1, end1);
  assert_lits_sorted (qdpll, start2, end2);
#endif
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LitIDStack tmp;
  QDPLL_INIT_STACK(tmp);

  LitID *p1 = start1;
  LitID *p2 = start2;

  while (1)
    {
      assert (p1 < end1);
      assert (p2 < end2);
      LitID lit1 = *p1;
      LitID lit2 = *p2;
      int compared = compare_lits_by_user_variable_nesting (qdpll, lit1, lit2);
      if (compared < 0)
        {
          qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit1, pivot, 0);
          p1++;
          if (p1 == end1)
            break;
        }
      else if (compared > 0)
        {
          qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit2, pivot, 1);
          p2++;
          if (p2 == end2)
            break;
        }
      else
        {
          /* Special case: poth pointers point at literal of same
             variable. Collect one literal, increase both pointers. */
          assert (compared == 0);
          assert (LIT2VARID(lit1) == LIT2VARID(lit2));
          VarID varid1 = LIT2VARID(lit1);
          /* Ignore literal of pivot variable, done inside 'qpup_res_merge_lits_aux'. */
          qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit1, pivot, 0);
          if (long_dist_res)
            {
              /* When using long-distance resolution, then collect also
                 complementary literals of variables other than the pivot. */
              if (lit1 == -lit2 && varid1 != pivot->id)
                qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit2, pivot, 1);
            }
          else
            {
              /* Additional safeguard: must avoid tautology unless we apply
                 long-distance resolution. */
              QDPLL_ABORT_QDPLL((lit1 == -lit2 && varid1 != pivot->id), 
                                "fatal error: generated tautology!");
            }
          p1++;
          p2++;
          if (p1 == end1 || p2 == end2)
            break;
        }
    }
  assert (p1 == end1 || p2 == end2);

  for (; p1 < end1; p1++)
    {
      LitID lit = *p1;
      qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit, pivot, 0);
    }

  for (; p2 < end2; p2++)
    {
      LitID lit = *p2;
      qpup_res_merge_lits_aux (qdpll, mm, vars, &tmp, lit, pivot, 1);
    }

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "  QPUP merge-literals resolvent on %d: ", pivot->id);
      print_lits(qdpll, tmp.start, tmp.top - tmp.start, 0);
    }

#ifndef NDEBUG
  assert (qdpll->options.long_dist_res || !qpup_is_tautology(tmp.start, tmp.top));
  assert (!qpup_has_duplicate_lits(tmp.start, tmp.top));
  assert_lits_sorted (qdpll, tmp.start, tmp.top);
#endif

  /* Swap literal stacks: 'tmp' currently stores the literals of the
     resolvent; copy to stack 'resolvent_lits'. */
  LitIDStack swap = tmp;
  tmp = *resolvent_lits;
  *resolvent_lits = swap;

  QDPLL_DELETE_STACK(mm, tmp);
}


/* Compute the QPUP constraint for variable 'pivot' and store its literals in
   'resolvent_lits'. If 'pivot' is NULL then QPUP is computed for the empty
   constraint. Successively resolve the original antecedent with the
   previously computed QPUP constraints of unit literals. */
static ConstraintID
qpup_compute (QDPLL *qdpll, Var *pivot, LitIDStack *resolvent_lits, 
              LitID *orig_ante_lits_start, LitID *orig_ante_lits_end, const ConstraintID trace_id, const QDPLLQuantifierType type)
{
  assert (orig_ante_lits_start <= orig_ante_lits_end);
  assert (QDPLL_EMPTY_STACK(*resolvent_lits));

  ConstraintID ante_trace_id = trace_id;

  LitID *lp, *le;

  /* Collect and mark literals of original antecedent on stack 'resolvent_lits'. */
  for (lp = orig_ante_lits_start, le = orig_ante_lits_end; lp < le; lp++)
    {
      LitID lit = *lp;
      Var *v = LIT2VARPTR(qdpll->pcnf.vars, lit);
      assert (!QDPLL_LIT_NEG (lit) || !qpup_res_is_var_neg_marked (v));
      assert (!QDPLL_LIT_POS (lit) || !qpup_res_is_var_pos_marked (v));
      qpup_res_mark_var_by_lit(v, lit);
      QDPLL_PUSH_STACK(qdpll->mm, *resolvent_lits, lit);
      if (!qdpll->options.bump_vars_once)
        increase_var_activity (qdpll, v, v->scope);
    }

  /* Resolve the current resolvent given by stack 'resolvent_lits'
     with precomputed qpup constraints. */
  for (lp = orig_ante_lits_start, le = orig_ante_lits_end; lp < le; lp++)
    {
      Var *v = LIT2VARPTR(qdpll->pcnf.vars, *lp);
      /* On-the-fly clearing pos/neg-marks of variables visited during
         implication graph traversal. Might unmark variable multiple times. */
      qpup_unmark_var (v);
      assert (!v->qpup_constraint || (v != pivot && v->scope->type == type && v->mode == QDPLL_VARMODE_UNIT));

      if (v->qpup_constraint)
        {
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, " QPUP compute: resolving on %d, using qpup(%d) with constr_id=%d: ", v->id, v->id, v->qpup_constraint->id);
              print_constraint (qdpll, v->qpup_constraint);
            }

          /* Resolve on 'v': collect literals from 'v->qpup_constraint',
             which must have been computed already since nodes are processed
             in propagation order (i.e. in trail order). */

          qpup_res_merge_literals (qdpll, v, resolvent_lits, 
                                   resolvent_lits->start, resolvent_lits->top, 
                                   v->qpup_constraint, type);

          if (qdpll->options.trace)
            {
              qdpll->cur_constraint_id++;
              qdpll->trace_constraint (qdpll->cur_constraint_id, resolvent_lits->start,
                                       QDPLL_COUNT_STACK (*resolvent_lits), ante_trace_id,
                                       v->qpup_constraint->id);
              ante_trace_id = qdpll->cur_constraint_id;
            }
        }
    }

  /* Unmark variables on stack 'resolvent_lits'. */
  for (lp = resolvent_lits->start, le = resolvent_lits->top; lp < le; lp++)
    {
      LitID lit = *lp;
      Var *v = LIT2VARPTR(qdpll->pcnf.vars, lit);
      assert (qpup_res_is_var_marked(v));
      assert (qdpll->options.long_dist_res || 
              !(qpup_res_is_var_pos_marked(v) && qpup_res_is_var_neg_marked(v)));
      if (QDPLL_LIT_NEG (lit))
        {
          assert (v->qpup_res_mark_neg);
          v->qpup_res_mark_neg = 0;
        }
      else
        {
          assert (v->qpup_res_mark_pos);
          v->qpup_res_mark_pos = 0;
        }
    }

  if (qdpll->options.trace)
    {
      /* Print dummy step if no resolution step occurred. This overhead can be
         avoided if no explicit QPUP constraints are allocated but original
         antecedents are re-used if possible. */
      if (ante_trace_id == trace_id)
        {
          qdpll->cur_constraint_id++;
          qdpll->trace_constraint (qdpll->cur_constraint_id, resolvent_lits->start,
                                   QDPLL_COUNT_STACK (*resolvent_lits), ante_trace_id,
                                   0);
          ante_trace_id = qdpll->cur_constraint_id;
        }
    }

  return ante_trace_id;
}

/* Produce the QPUP constraint for variable 'pivot'. The literals of the
   resulting constraint are stored on stack 'resolvent_lits'. Literals of the
   original antecedent constraint of 'pivot' are given by
   'orig_ante_lits_start,orig_ante_lits_end'. */
static void
qpup_resolve_and_reduce (QDPLL *qdpll, Var *pivot, LitIDStack *resolvent_lits, 
                         LitID *orig_ante_lits_start, LitID *orig_ante_lits_end, const ConstraintID trace_id, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || !qdpll->options.trace || trace_id);
  /* For tracing only: 'qpup_constr_id' is the ID of the final constraint produced by 'qpup_compute'. */
  ConstraintID qpup_constr_id = qpup_compute (qdpll, pivot, resolvent_lits, 
                orig_ante_lits_start, orig_ante_lits_end, trace_id, type);
  
  /* Universal reduction on collected literals to get final resolvent. */
  qpup_res_reduce (qdpll, resolvent_lits, qpup_constr_id, type);
}

/* Compute QPUP constraints for visited nodes until finally the learnt
   constraint is obtained. The parameter 'empty_constraint_lits' is a stack of
   literals of the conflicting clause/initial cube. The QPUP constraint of the
   conflicting clause/initial cube will be learnt. */
static Constraint *
qpup_do_forward_resolutions (QDPLL *qdpll, LitIDStack *empty_constraint_lits, const QDPLLQuantifierType type)
{
  assert (qdpll->qpup_nodes->cnt == 0);

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "\nQPUP: forward resolutions started.\n");

  /* Consider visited nodes (i.e. variables which were assigned as units) in
     propagation order. Since variables on stack 'qdpll->qpup_units' were
     pushed in reverse propagation order, we go from top to bottom in that
     stack to get the desired ordering. */

  /* Auxiliary stack holding literals during construction of QPUP constraint. */
  LitIDStack qpup_constraint_lits;
  QDPLL_INIT_STACK(qpup_constraint_lits);

  /* Explicit emptyness check required for SDCL: might start from the empty
     initial cube. In this case, no resolutions are carried out. This case cannot
     happen in CDCL. */
  if (!QDPLL_EMPTY_STACK(qdpll->qpup_units))
    {
      Var **p, **e;
      for (p = qdpll->qpup_units.top - 1, e = qdpll->qpup_units.start; e <= p; p--)
        {
          Var *unit = *p;
          assert (unit->mode == QDPLL_VARMODE_UNIT);
          assert (unit->scope->type == type);
          assert (unit->antecedent);
          assert (!unit->antecedent->qbcp_qbce_blocked);
          assert (QDPLL_EMPTY_STACK(qpup_constraint_lits));

          /* Compute the QPUP constraint for variable 'unit': check the
             original constraint 'unit->antecedent' which caused 'unit' to be
             assigned as unit literal; resolve over all variables which were
             unit, using the previously computed QPUP constraints of that
             variables. This is possible since we process variables in
             propagation order. */

          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "\nQPUP compute: generating qpup(%d), original antecedent (constr_id=%d): ", unit->id, unit->antecedent->id);
              print_lits (qdpll, unit->antecedent->lits, unit->antecedent->num_lits, 0);
            }

          if (!qdpll->options.bump_vars_once)
            learnt_constraint_mtf (qdpll, unit->antecedent);

          qpup_resolve_and_reduce (qdpll, unit, &qpup_constraint_lits, 
                                   unit->antecedent->lits, unit->antecedent->lits + unit->antecedent->num_lits, unit->antecedent->id, type);

          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "QPUP compute: completed qpup(%d), constr_id=%d, reduced result: ", unit->id, qdpll->cur_constraint_id);
              print_lits (qdpll, qpup_constraint_lits.start, QDPLL_COUNT_STACK(qpup_constraint_lits), 0);
            }

          /* ID of constraint to be constructed was printed already. Must decrease ID-field 
             in struct QDPLL by one since it is incremented again in function 'create_constraint'.  */
          if (qdpll->options.trace)
            {
              assert (qdpll->cur_constraint_id > 0);
              qdpll->cur_constraint_id--;
            }

          /* Allocate QPUP constraint of variable 'unit' and copy literals. */
          assert (!unit->qpup_constraint);
          unit->qpup_constraint = create_constraint (qdpll, QDPLL_COUNT_STACK(qpup_constraint_lits), type == QDPLL_QTYPE_FORALL);
          memcpy (unit->qpup_constraint->lits, qpup_constraint_lits.start, 
                  QDPLL_COUNT_STACK(qpup_constraint_lits) * sizeof (LitID));

          QDPLL_RESET_STACK(qpup_constraint_lits);
          /* Completed QPUP computation for variable 'unit'. */
        }
    }

  /* Finally, compute the QPUP constraint for the empty constraint. */
  assert (QDPLL_EMPTY_STACK(qpup_constraint_lits));

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "\nQPUP compute: generating qpup(0) on empty constraint (constr_id=%d): ", qdpll->res_cons_id);
      print_lits (qdpll, empty_constraint_lits->start, QDPLL_COUNT_STACK(*empty_constraint_lits), 0);
    }

  qpup_resolve_and_reduce (qdpll, 0, &qpup_constraint_lits, 
                           empty_constraint_lits->start, empty_constraint_lits->top, qdpll->res_cons_id, type);

  if (qdpll->options.trace)
    {
      assert (qdpll->cur_constraint_id > 0);
      qdpll->cur_constraint_id--;
    }

  Constraint *qpup_learnt_constraint = create_constraint (qdpll, QDPLL_COUNT_STACK(qpup_constraint_lits), type == QDPLL_QTYPE_FORALL);
  memcpy (qpup_learnt_constraint->lits, qpup_constraint_lits.start, 
          QDPLL_COUNT_STACK(qpup_constraint_lits) * sizeof (LitID));

  QDPLL_DELETE_STACK(qdpll->mm, qpup_constraint_lits);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "QPUP: forward resolutions completed.\n");
      fprintf (stderr, "QPUP: computed final constraint qpup(0): ");
      if (qpup_learnt_constraint->num_lits == 0)
        fprintf (stderr, "empty.\n");
      else
        print_constraint (qdpll, qpup_learnt_constraint);
    }

  return qpup_learnt_constraint;
}

/* Expensive assertion: check that variable marks used for QPUP have all been
   reset, all data cleared. */
static void
assert_qpup_data_cleared (QDPLL *qdpll)
{
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      assert (!p->qpup_mark_pos);
      assert (!p->qpup_mark_neg);
      assert (!p->qpup_constraint);
      assert (!p->qpup_res_mark_pos);
      assert (!p->qpup_res_mark_neg);
      assert (!p->qpup_neg_predict_mark);
      assert (!p->qpup_pos_predict_mark);
      assert (!p->mark_learn0);
      assert (!p->mark_learn1);
      assert (!QDPLL_VAR_POS_MARKED (p));
      assert (!QDPLL_VAR_NEG_MARKED (p));
      assert (!QDPLL_VAR_MARKED (p));
      assert (!p->scope || QDPLL_EMPTY_STACK(p->scope->cover_lits));
    }
  assert (!qdpll->qpup_uip);
  assert (qdpll->qpup_nodes->cnt == 0);
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_vars));
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_units));
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_kept_lits));
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_weak_predict_lits));
}

/* Given the constraint 'qpup_constraint' to be learnt, compute the decision
   level where that constraint is asserting. */
static unsigned int
qpup_compute_asserting_level (QDPLL *qdpll, Var *asserted_var, 
                              Constraint *qpup_constraint, const QDPLLQuantifierType type)
{
  assert (asserted_var);
  assert (qpup_constraint);

  unsigned int asserting_level = QDPLL_INVALID_DECISION_LEVEL, highest = 0;
  QDPLLDepManGeneric *dm = qdpll->dm;

  LitID *p, *e;
  for (p = qpup_constraint->lits, e = p + qpup_constraint->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      unsigned int cur_level = var->decision_level;

      if (type == var->scope->type
          || dm->depends (dm, var->id, asserted_var->id))
        {
          if (cur_level > highest)
            {
              assert (cur_level != QDPLL_INVALID_DECISION_LEVEL);
              asserting_level = highest;
              highest = cur_level;
            }
          else if (cur_level > asserting_level)
            {
              assert (cur_level != QDPLL_INVALID_DECISION_LEVEL);
              asserting_level = cur_level;
            }
        }
    }

  QDPLL_ABORT_QDPLL (asserting_level == QDPLL_INVALID_DECISION_LEVEL, "unexpected asserting level!");
  assert (asserting_level != QDPLL_INVALID_DECISION_LEVEL);
  return asserting_level;
}


/* For assertion checking only. Returns true iff. the literal sets of c1 and
   c2 are equal or if c1 is a subset of c2. */
static int
qpup_is_subseteq (Constraint *c1, Constraint *c2)
{
  assert (c1);
  assert (c2);
  assert (c1->is_cube == c2->is_cube);

  if (c2->num_lits < c1->num_lits)
    return 0;

  LitID *p, *e;
  for (p = c1->lits, e = p + c1->num_lits; p < e; p++)
    {
      /* If the literal in 'c1' pointed to by 'p' does not occur in 'c2' then
         subset property does not hold. */
      if (!qpup_res_find_lit (c2->lits, c2->lits + c2->num_lits, *p))
        return 0;
    }

  return 1;
}


static int
check_invariant_has_dependency (QDPLL *qdpll, Var *var, 
                                LitID *start, LitID *end, Var *ignore_var, 
                                const QDPLLQuantifierType type)
{
  assert (start <= end);
  assert (var->scope->type != type);
  assert (ignore_var->scope->type == type);
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = start, e = end; p < e; p++)
    {
      Var *v = LIT2VARPTR(vars, *p);
      if (v != ignore_var && dm->depends(dm, var->id, v->id))
        return 1;
    }
  return 0;
}

/* Check invariant suggested by AVG. Must ignore the implied literal and all
   reducible literals of a given QPUP constraint. */
static int
check_invariant_qpup_is_subseteq (QDPLL *qdpll, Constraint *c1, Constraint *c2, 
                                  LitID ignore_lit, const QDPLLQuantifierType type)
{
  assert (c1);
  assert (c2);
  assert (c1->is_cube == c2->is_cube);

  LitID *p, *e;
  for (p = c1->lits, e = p + c1->num_lits; p < e; p++)
    {
      /* If the literal in 'c1' pointed to by 'p' does not occur in 'c2' then
         subset property does not hold. */
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (lit != ignore_lit && 
          (var->scope->type == type || 
           check_invariant_has_dependency (qdpll, var, c1->lits, e, 
                                           LIT2VARPTR(qdpll->pcnf.vars, ignore_lit), type)) && 
          !qpup_res_find_lit (c2->lits, c2->lits + c2->num_lits, lit))
        return 0;
    }

  return 1;
}



/* Add the learnt constraint 'qpup_constraint' to list of constraint, set
   literal watchers. */
static void
qpup_import_learnt_constraint (QDPLL *qdpll, Constraint *qpup_constraint, 
                        unsigned int asserting_level, const QDPLLQuantifierType type)
{
  assert (qdpll->qpup_uip);
  assert (qpup_constraint->num_lits > 0);

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "\nImporting QPUP constraint (id=%d): ", qpup_constraint->id);
      print_constraint (qdpll, qpup_constraint);
      fprintf (stderr, "\n");
    }

  assert (!qpup_constraint->learnt);
  qpup_constraint->learnt = 1;

  QDPLLMemMan *mm = qdpll->mm;
  LitID *p, *e;
  for (p = qpup_constraint->lits, 
         e = p + qpup_constraint->num_lits; 
       p < e; 
       p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);

      if (qdpll->options.bump_vars_once)
        increase_var_activity (qdpll, var, var->scope);

      if (qdpll->options.no_spure_literals &&
          !qdpll->options.no_pure_literals)
        {
          BLitsOcc blit = {lit, qpup_constraint};
          /* Add all literals to occurrence stacks. 
             POSSIBLE OPTIMIZATION: could factor out code. */
          if (!qpup_constraint->is_cube)
            {
              if (QDPLL_LIT_NEG (lit))
                QDPLL_PUSH_STACK(mm, var->neg_occ_clauses, blit);
              else
                QDPLL_PUSH_STACK(mm, var->pos_occ_clauses, blit);
            }
          else
            {
              blit.constraint = BLIT_MARK_PTR(blit.constraint);
              if (QDPLL_LIT_NEG (lit))
                QDPLL_PUSH_STACK(mm, var->neg_occ_cubes, blit);
              else
                QDPLL_PUSH_STACK(mm, var->pos_occ_cubes, blit);
            }
        }
    }

  /* Prepend to list of constraints. */
  if (!qpup_constraint->is_cube)
    LINK_FIRST (qdpll->pcnf.learnt_clauses, qpup_constraint, link);
  else
    {
      assert (qpup_constraint->is_cube);
      LINK_FIRST (qdpll->pcnf.learnt_cubes, qpup_constraint, link);
    }

  set_learnt_constraint_lit_watchers (qdpll, qpup_constraint,
                                      asserting_level, qdpll->qpup_uip, type);
}

static void
qpup_cleanup_aux_constraints (QDPLL *qdpll, Constraint *learnt_constraint, 
                              const QDPLLQuantifierType type)
{
  /* Free computed QPUP constraints. */
  Var *v;
  while (!QDPLL_EMPTY_STACK(qdpll->qpup_units))
    {
      v = QDPLL_POP_STACK(qdpll->qpup_units);
      assert (v->qpup_constraint);
      /* Invariant formulated by AVG: literals of QPUP constraints except the
         implied literal and reducible ones occur in QPUP constraint of empty
         constraint. */
      assert (!learnt_constraint || 
              check_invariant_qpup_is_subseteq (qdpll, v->qpup_constraint, 
                                                learnt_constraint, 
                                                type == QDPLL_QTYPE_EXISTS ? 
                                                (v->assignment == QDPLL_ASSIGNMENT_FALSE ? -v->id : v->id) : 
                                                (v->assignment == QDPLL_ASSIGNMENT_FALSE ? v->id : -v->id), type));
      delete_constraint (qdpll, v->qpup_constraint);
      v->qpup_constraint = 0;
    }
}


static int
constraint_has_only_assumption_lits (QDPLL *qdpll, LitID *start, LitID *end)
{
  assert (start <= end);
  /* NEW: traverse literals from right to left. Assumptions are from leftmost
     block, hence their literals appear at the left end in a
     constraint. Non-assumptions appear at the right and the loop will terminate
     early. */
  LitID *p, *e;
  for (p = end - 1, e = start; e <= p; p--)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->mode != QDPLL_VARMODE_ASSUMED)
        return 0;
    }
  return 1;
}


/* Stack 'constraint_lits' stores the literals of the current empty clause /
   initial cube. First, find a suitable UIP node and identify all variables
   'var' for which 'QPUP(var)' has to be computed. For that purpose the
   implication graph is traversed exactly once in reverse propagation
   order. Finally, the QPUP constraints are computed by traversing relevant
   parts of the graph into the other direction, i.e. towards the empty
   clause/cube. */
static Constraint *
qpup_compute_learnt_constraint (QDPLL *qdpll, LitIDStack *empty_constraint_lits, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (type == QDPLL_QTYPE_FORALL || !qdpll->options.trace || qdpll->res_cons_id);
  assert (!qdpll->options.traditional_qcdcl || 
          !qdpll->options.no_qpup_cdcl || !qdpll->options.no_qpup_sdcl);
  assert (!(!qdpll->options.no_lazy_qpup && qdpll->options.trace));
  QDPLL_ABORT_QDPLL(!qdpll->options.no_lazy_qpup && qdpll->options.trace, 
                    "Must combine '--no-lazy-qpup' with tracing to generate resolution steps!");

  Var *vars = qdpll->pcnf.vars;
  /* Reset marks which were set during 'get_initial_reason'. */
  LitID *p, *e;
  for (p = empty_constraint_lits->start, e = empty_constraint_lits->top; p < e; p++)
    {
      LitID lit = *p;
      assert (LEARN_VAR_MARKED(LIT2VARPTR(vars, lit)));
      if (QDPLL_LIT_NEG (lit))
        {
          assert (LEARN_VAR_NEG_MARKED(LIT2VARPTR(vars, lit)));
          LEARN_VAR_NEG_UNMARK(LIT2VARPTR(vars, lit));
        }
      else
        {
          assert (LEARN_VAR_POS_MARKED(LIT2VARPTR(vars, lit)));
          LEARN_VAR_POS_UNMARK(LIT2VARPTR(vars, lit));
        }
    }

#ifndef NDEBUG
  /* Expensive assertion! */
  assert_qpup_data_cleared (qdpll);
#endif

  assert (!qdpll->qpup_uip);
  assert (qdpll->qpup_nodes->cnt == 0);
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_vars));
  assert (QDPLL_EMPTY_STACK(qdpll->qpup_units));
  assert (qdpll->qpup_var_at_max_dec_level == 0);
  assert (qdpll->qpup_cnt_at_max_dec_level == 0);


  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "QPUP: started.\n");

  assert (QDPLL_EMPTY_STACK(qdpll->internal_cover_lits));
  qpup_traverse_implication_graph (qdpll, empty_constraint_lits, type);

  /* Reset incrementally maintained data. */
  qdpll->qpup_var_at_max_dec_level = 0;
  qdpll->qpup_cnt_at_max_dec_level = 0;


  Constraint *qpup_learnt_constraint;

  if (qdpll->options.no_lazy_qpup)
    {
      /* Compute learnt constraint using explicit resolution steps. */
      qpup_learnt_constraint = qpup_do_forward_resolutions (qdpll, empty_constraint_lits, type);
      qpup_cleanup_aux_constraints (qdpll, qpup_learnt_constraint, type);
    }
  else
    {
      /* Build learnt constraint from predicted literals WITHOUT any resolutions. */
      qpup_collect_weak_predict_lits_aux (qdpll, empty_constraint_lits, type);
      /* Exactly ONE application of constraint reduction needed! */
      qpup_res_reduce (qdpll, &qdpll->qpup_weak_predict_lits, 0, type);

      if (qdpll->options.verbosity >= 2)
        {
          fprintf (stderr, "\nPredicted constraint: ");
          LitID *p, *e;
          for (p = qdpll->qpup_weak_predict_lits.start, e = qdpll->qpup_weak_predict_lits.top; p < e; p++)
            fprintf (stderr, "%d ", *p);
          fprintf (stderr, "\n");
        }

      qpup_learnt_constraint = 
        create_constraint (qdpll, QDPLL_COUNT_STACK(qdpll->qpup_weak_predict_lits), 
                           type == QDPLL_QTYPE_FORALL);
      memcpy (qpup_learnt_constraint->lits, qdpll->qpup_weak_predict_lits.start, 
              QDPLL_COUNT_STACK(qdpll->qpup_weak_predict_lits) * sizeof (LitID));
    }

#ifndef NDEBUG
  assert (qdpll->options.long_dist_res || 
          !qpup_is_tautology(qpup_learnt_constraint->lits, 
                             qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits));
  assert (!qpup_has_duplicate_lits(qpup_learnt_constraint->lits, 
                             qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits));
  assert_lits_sorted (qdpll, qpup_learnt_constraint->lits, 
                      qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits);
#endif
  /* Empty constraint derived iff no proper UIP found or if initial cube is already asserting. */
  assert (qdpll->qpup_uip || qpup_learnt_constraint->num_lits == 0 || 
          constraint_has_only_assumption_lits (qdpll, qpup_learnt_constraint->lits, 
                                               qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits));
  assert (!qdpll->qpup_uip || (qpup_learnt_constraint->num_lits != 0 && 
                               !constraint_has_only_assumption_lits (qdpll, qpup_learnt_constraint->lits, 
                                               qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits)));

  /* For solving under assumption: store the final learned constraint which
     contains only the relevant assumption literals, if any. */
  if (!qdpll->qpup_uip && qdpll->state.assumptions_given)
    {
      assert (constraint_has_only_assumption_lits (qdpll, qpup_learnt_constraint->lits, 
                                               qpup_learnt_constraint->lits + qpup_learnt_constraint->num_lits));
      assert (!qdpll->assumption_lits_constraint);
      QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint, "must call 'qdpll_reset' before 'qdpll_sat'!");
      qdpll->assumption_lits_constraint = qpup_learnt_constraint;
    }

  assert (!qdpll->assumption_lits_constraint || (!qdpll->qpup_uip && qdpll->state.assumptions_given));
  assert (qdpll->assumption_lits_constraint || (qdpll->qpup_uip || !qdpll->state.assumptions_given));
  QDPLL_ABORT_QDPLL (qdpll->qpup_nodes->cnt != 0, "Unexpected QPUP nodes remaining.");

  /* NOTE: variables have been unmarked on-the-fly during resolutions already. */
  QDPLL_RESET_STACK(qdpll->qpup_vars);
  QDPLL_RESET_STACK(qdpll->qpup_units);
  QDPLL_RESET_STACK(qdpll->qpup_kept_lits);
  QDPLL_RESET_STACK(qdpll->qpup_weak_predict_lits);
  qdpll->res_cons_id = 0;

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "QPUP: completed.\n");

  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));

  return qpup_learnt_constraint;
}

/* END: QPUP code. */






static unsigned int
generate_and_add_reason (QDPLL * qdpll, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LitIDStack *lit_stack = &(qdpll->add_stack);
  LitIDStack *lit_stack_tmp = &(qdpll->add_stack_tmp);
  LitID *p;

  assert (!qdpll->options.trace || !qdpll->res_cons_id);
  assert (qdpll->cnt_hi_dl_type_lits == 0);
  assert (qdpll->hi_dl_type_var == 0);
  assert (qdpll->hi_type_dl == 0);
  assert (QDPLL_EMPTY_STACK (qdpll->smaller_type_lits));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));
  assert (QDPLL_COUNT_STACK (*lit_stack) == 0);
  assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);
#ifndef NDEBUG
#if QDPLL_ASSERT_LEARN_VARS_UNMARKED
  assert_learn_vars_unmarked (qdpll);
#endif
#endif

  get_initial_reason (qdpll, &lit_stack, &lit_stack_tmp, type);
  /* May happen that the clause learned by trivial falsity is empty after
     universal reduction. */
  assert (qdpll->state.decision_level == 0 || type == QDPLL_QTYPE_FORALL ||
          QDPLL_COUNT_STACK (*lit_stack) != 0 || 
          qdpll->state.unsat_branch_clause);

#ifndef NDEBUG
  if (QDPLL_COUNT_STACK (*lit_stack) > 0 &&  
      !constraint_has_only_assumption_lits (qdpll, (lit_stack)->start, (lit_stack)->top))
      assert_stop_crit_data (qdpll, lit_stack, type);
#endif

  if (qdpll->options.verbosity > 1)
    {
      if (type == QDPLL_QTYPE_EXISTS)
        {
          if (qdpll->result_constraint)
            fprintf (stderr, "CDCL: conflicting clause (%u): ",
                     qdpll->result_constraint->id);
          else
            fprintf (stderr, "CDCL: conflicting clause by trivial falsity: ");
        }
      else
        {
          fprintf (stderr, "SDCL: initial cube");
          if (qdpll->options.trace)
            fprintf (stderr, " (%u)", qdpll->cur_constraint_id);
          fprintf (stderr, ": ");
        }

      print_lits (qdpll, lit_stack->start, QDPLL_COUNT_STACK (*lit_stack),
                  0);
    }

  /* Now lit-stack contains literals of either
     conflicting clause or cover-set/satisfied cube. */


  /* START: compute learnt constraint by QPUP. */

  Constraint *qpup_constraint = 0;

  if (!qdpll->options.traditional_qcdcl || (type == QDPLL_QTYPE_EXISTS && !qdpll->options.no_qpup_cdcl) || 
      (type == QDPLL_QTYPE_FORALL && !qdpll->options.no_qpup_sdcl))
    {
      qpup_constraint = qpup_compute_learnt_constraint (qdpll, lit_stack, type);
      assert (qpup_constraint);

      /* Start: reset data for classical learning. */
      /* Unmark variables marked during computation of initial reason. */
#ifndef NDEBUG
      LitID *p;
      for (p = lit_stack->start; p < lit_stack->top; p++)
        assert(!LEARN_VAR_MARKED (LIT2VARPTR (vars, *p)));
#endif

      QDPLL_RESET_STACK (*lit_stack);
      assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);
      reset_stop_crit_data (qdpll);
      /* END: reset data for classical learning. */

      if (qdpll->qpup_uip)
        {
#if COMPUTE_STATS
          if (type == QDPLL_QTYPE_FORALL)
            {
              qdpll->stats.total_learnt_cubes++;
              qdpll->stats.total_learnt_cubes_size += qpup_constraint->num_lits;
            }
          else
            {
              qdpll->stats.total_learnt_clauses++;
              qdpll->stats.total_learnt_clauses_size += qpup_constraint->num_lits;
            }
#endif
          unsigned int asserting_level = qpup_compute_asserting_level (qdpll, qdpll->qpup_uip, 
                                                                       qpup_constraint, type);
          qpup_import_learnt_constraint (qdpll, qpup_constraint, asserting_level, type);

          assert (qpup_constraint->num_lits > 0);
          /* Set assignment to be forced by learnt constraint. */
          assert (!qdpll->state.forced_assignment.var);
          qdpll->state.forced_assignment.var = qdpll->qpup_uip;
          assert (QDPLL_VAR_ASSIGNED(qdpll->qpup_uip));
          assert (!qdpll->state.forced_assignment.assignment);
          qdpll->state.forced_assignment.assignment = -qdpll->qpup_uip->assignment;
          assert (!qdpll->state.forced_assignment.mode);
          qdpll->state.forced_assignment.mode = QDPLL_VARMODE_UNIT;
          assert (!qdpll->state.forced_assignment.antecedent);
          qdpll->state.forced_assignment.antecedent = qpup_constraint;

          /* Reset QPUP data. */
          qdpll->qpup_uip = 0;

          decay_var_activity (qdpll);

          return 1 + asserting_level;
        }
      else
        {
          assert (qpup_constraint->num_lits == 0 || 
                  constraint_has_only_assumption_lits (qdpll, qpup_constraint->lits, 
                                                       qpup_constraint->lits + qpup_constraint->num_lits));
          if (!qdpll->state.assumptions_given)
            {
              assert (!qdpll->assumption_lits_constraint);
              delete_constraint (qdpll, qpup_constraint);
            }
          else 
            {
              assert (constraint_has_only_assumption_lits (qdpll, qpup_constraint->lits, 
                                                           qpup_constraint->lits + qpup_constraint->num_lits));
              assert (qdpll->assumption_lits_constraint == qpup_constraint);
            }
          /* Reset QPUP data. */
          qdpll->qpup_uip = 0;
          return QDPLL_INVALID_DECISION_LEVEL;
        }
    }

  /* END: compute learnt constraint by QPUP. */

  qdpll->res_cons_id = 0;





#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  int success = generate_reason (qdpll,
                                 qdpll->result_constraint == NULL ?
                                 qdpll->cur_constraint_id : qdpll->
                                 result_constraint->id,
                                 &lit_stack, &lit_stack_tmp, type);
#if COMPUTE_TIMES
  qdpll->time_stats.total_greason_time += (time_stamp () - start);
#endif
  assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);

  unsigned int is_taut = 0;

  /* Unmark variables by traversing lit-stack, i.e. final working
     reason. */
  Var *var;
  LitID lit;
  for (p = lit_stack->start; p < lit_stack->top; p++)
    {
      lit = *p;
      var = LIT2VARPTR (vars, lit);
#if COMPUTE_STATS
      if (LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var))
        is_taut = 1;
#endif
      if (qdpll->options.bump_vars_once)
        increase_var_activity (qdpll, var, var->scope);
      assert (!success || qdpll->options.long_dist_res || 
              !(LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var)));
      LEARN_VAR_UNMARK (var);
    }

  assert (!is_taut || qdpll->options.long_dist_res);

#ifndef NDEBUG
#if QDPLL_ASSERT_LEARN_VARS_UNMARKED
  assert_learn_vars_unmarked (qdpll);
#endif
#endif

  if (success)
    {
#if COMPUTE_STATS
      if (type == QDPLL_QTYPE_FORALL)
        {
          qdpll->stats.total_learnt_cubes++;
          if (is_taut)
            qdpll->stats.total_learnt_taut_cubes++;
          qdpll->stats.total_learnt_cubes_size +=
            QDPLL_COUNT_STACK (*lit_stack);
        }
      else
        {
          qdpll->stats.total_learnt_clauses++;
          if (is_taut)
            qdpll->stats.total_learnt_taut_clauses++;
          qdpll->stats.total_learnt_clauses_size +=
            QDPLL_COUNT_STACK (*lit_stack);
        }
#endif
      /* Import reason. */
      qdpll->cur_constraint_id -= 1;    /* we already printed this one while
                                           resolving */
      Constraint *learnt_constraint = 0;
      learnt_constraint =
        create_constraint (qdpll, QDPLL_COUNT_STACK (*lit_stack),
                           type == QDPLL_QTYPE_FORALL);
#if COMPUTE_STATS
      learnt_constraint->is_taut = is_taut;
#endif
      assert (type == QDPLL_QTYPE_FORALL || !learnt_constraint->is_cube);
      assert (type == QDPLL_QTYPE_EXISTS || learnt_constraint->is_cube);
      assert (!learnt_constraint->learnt);
      assert (QDPLL_COUNT_STACK (*lit_stack) != 0);
      learnt_constraint->learnt = 1;

      /* Computation of asserting level is interleaved with literal copying. */
      unsigned int asserting_level = 0, max_type_level =
        get_highest_type_lit_dec_level (qdpll, lit_stack->start,
                                        lit_stack->top, type);
      assert (count_type_lit_at_dec_level
              (qdpll, lit_stack->start, lit_stack->top, max_type_level,
               type) == 1);
      Var *type_var =
        get_type_var_at_dec_level (qdpll, lit_stack->start, lit_stack->top,
                                   max_type_level, type);
      assert (type == type_var->scope->type);
      const VarID type_var_id = type_var->id;

      unsigned int get_assert_level, get_assert_highest = 0;
      QDPLLDepManGeneric *dm = qdpll->dm;
      unsigned int offset = 0;
      LitID *stack_p, *stack_e;
      p = learnt_constraint->lits;
      for (stack_p = lit_stack->start, stack_e = lit_stack->top;
           stack_p < stack_e; stack_p++)
        {
          assert (p < learnt_constraint->lits + learnt_constraint->num_lits);
          lit = *stack_p;
          assert (lit);

          /* Copy lit from lit-stack to newly allocated constraint. */
          *p++ = lit;

          /* Compute asserting level. */
          var = LIT2VARPTR (vars, lit);
          get_assert_level = var->decision_level;
          if (type == var->scope->type
              || dm->depends (dm, var->id, type_var_id))
            {
              if (get_assert_level > get_assert_highest)
                {
                  assert (get_assert_level != QDPLL_INVALID_DECISION_LEVEL);
                  asserting_level = get_assert_highest;
                  get_assert_highest = get_assert_level;
                }
              else if (get_assert_level > asserting_level)
                {
                  assert (get_assert_level != QDPLL_INVALID_DECISION_LEVEL);
                  asserting_level = get_assert_level;
                }
            }

          if (qdpll->options.no_spure_literals &&
              !qdpll->options.no_pure_literals)
            {
              BLitsOcc blit = { lit, learnt_constraint };
              /* Add all literals to occurrence stacks. 
                 POSSIBLE OPTIMIZATION: could factor out code. */
              if (type == QDPLL_QTYPE_EXISTS)
                {
                  if (QDPLL_LIT_NEG (lit))
                    QDPLL_PUSH_STACK (mm, var->neg_occ_clauses, blit);
                  else
                    QDPLL_PUSH_STACK (mm, var->pos_occ_clauses, blit);
                }
              else
                {
                  blit.constraint = BLIT_MARK_PTR (blit.constraint);
                  if (QDPLL_LIT_NEG (lit))
                    QDPLL_PUSH_STACK (mm, var->neg_occ_cubes, blit);
                  else
                    QDPLL_PUSH_STACK (mm, var->pos_occ_cubes, blit);
                }
            }
        }

      if (type == QDPLL_QTYPE_EXISTS)
        {
          assert (!learnt_constraint->is_cube);
          LINK_FIRST (qdpll->pcnf.learnt_clauses, learnt_constraint, link);
        }
      else
        {
          assert (learnt_constraint->is_cube);
          LINK_FIRST (qdpll->pcnf.learnt_cubes, learnt_constraint, link);
        }

      assert (QDPLL_VAR_ASSIGNED (type_var));
      /* Set forced assignment (by asserting reason) to be enqueued afterwards. */
      assert (type == type_var->scope->type);
      assert (!qdpll->state.forced_assignment.antecedent);
      assert (!qdpll->state.forced_assignment.var);
      assert (!qdpll->state.forced_assignment.assignment);
      assert (!qdpll->state.forced_assignment.mode);
      qdpll->state.forced_assignment.var = type_var;
      qdpll->state.forced_assignment.assignment = -type_var->assignment;
      qdpll->state.forced_assignment.mode = QDPLL_VARMODE_UNIT;

      assert (asserting_level ==
              get_reason_asserting_level (qdpll,
                                          lit_stack->start, lit_stack->top,
                                          type_var, type));

      qdpll->state.forced_assignment.antecedent = learnt_constraint;

      set_learnt_constraint_lit_watchers (qdpll, learnt_constraint,
                                          asserting_level,
                                          qdpll->hi_dl_type_var, type);

      if (qdpll->options.verbosity > 1)
        {
          fprintf (stderr, "%cDCL: Added learnt %s (%u): ",
                   type == QDPLL_QTYPE_EXISTS ? 'C' : 'S',
                   type == QDPLL_QTYPE_EXISTS ? "clause" : "cube",
                   learnt_constraint->id);
          print_constraint (qdpll, learnt_constraint);
        }

      /* As in Minisat, decay variables by increasing 'delta'. */
      decay_var_activity (qdpll);

      QDPLL_RESET_STACK (*lit_stack);
      assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);
      reset_stop_crit_data (qdpll);

      /* Fix: we must keep assignments at asserting level, hence add 1. */
      return 1 + asserting_level;
    }
  else
    {
      assert (QDPLL_EMPTY_STACK(*lit_stack) || 
              (qdpll->state.assumptions_given && 
               constraint_has_only_assumption_lits (qdpll, (*lit_stack).start, (*lit_stack).top)));
      if (qdpll->state.assumptions_given)
        {
          /* Store assumption-lits-constraint, if any. */
          assert (!qdpll->assumption_lits_constraint);
          QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint, "must call 'qdpll_reset' before 'qdpll_sat'!");
          qdpll->assumption_lits_constraint = 
            create_constraint (qdpll, QDPLL_COUNT_STACK(*lit_stack), 
                               type == QDPLL_QTYPE_FORALL);
          memcpy (qdpll->assumption_lits_constraint->lits, (*lit_stack).start, 
                  QDPLL_COUNT_STACK(*lit_stack) * sizeof (LitID));
        }

      QDPLL_RESET_STACK (*lit_stack);
      assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);
      reset_stop_crit_data (qdpll);

      return QDPLL_INVALID_DECISION_LEVEL;
    }
}

/* ---------- END: CDCL ---------- */

static unsigned int
analyze_conflict_no_cdcl (QDPLL * qdpll)
{
  return chron_backtracking (qdpll, QDPLL_QTYPE_EXISTS);
}


/* Perform condflict-driven clause learning. */
static unsigned int
analyze_conflict_cdcl (QDPLL * qdpll)
{
  return generate_and_add_reason (qdpll, QDPLL_QTYPE_EXISTS);
}


static unsigned int
analyze_conflict (QDPLL * qdpll)
{
#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  unsigned int result;
  if (qdpll->options.no_cdcl)
    result = analyze_conflict_no_cdcl (qdpll);
  else
    result = analyze_conflict_cdcl (qdpll);
#if COMPUTE_TIMES
  qdpll->time_stats.total_conf_learn_time += (time_stamp () - start);
#endif
  return result;
}

static unsigned int
analyze_solution_no_sdcl (QDPLL * qdpll)
{
  return chron_backtracking (qdpll, QDPLL_QTYPE_FORALL);
}


static unsigned int
analyze_solution_sdcl (QDPLL * qdpll)
{
  return generate_and_add_reason (qdpll, QDPLL_QTYPE_FORALL);
}

static unsigned int
analyze_solution (QDPLL * qdpll)
{
#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  unsigned int result;
  if (qdpll->options.no_sdcl)
    result = analyze_solution_no_sdcl (qdpll);
  else
    result = analyze_solution_sdcl (qdpll);
#if COMPUTE_TIMES
  qdpll->time_stats.total_sol_learn_time += (time_stamp () - start);
#endif
  return result;
}

/* -------------------- END: LEARNING -------------------- */

static void
qbcp_qbce_backtrack_clear_stack_of_stacks (QDPLL *qdpll, ConstraintPtrStackStack *stack, 
                                           const int called_on_blocked_clauses, 
                                           const unsigned int decision_level)
{
  assert (decision_level != QDPLL_INVALID_DECISION_LEVEL);
  assert (!QDPLL_EMPTY_STACK (*stack));
  assert (!qdpll->state.qbcp_qbce_currently_preprocessing);
  assert (!called_on_blocked_clauses || 
          QDPLL_COUNT_STACK (*stack) == decision_level + 2);
  ConstraintPtrStack cstack = QDPLL_POP_STACK (*stack);
#if COMPUTE_STATS
  if (called_on_blocked_clauses)
    qdpll->stats.qbcp_qbce_current_blocked_clauses -= QDPLL_COUNT_STACK (cstack);
#endif
  if (qdpll->options.verbosity >= 3)
    fprintf (stderr, "During backtrack: starting to clear %d clauses %s at level %d\n", 
             (unsigned int) QDPLL_COUNT_STACK(cstack), called_on_blocked_clauses ? 
             "blocked" : "marked", decision_level);
  Constraint **cp, **ce;
  for (cp = cstack.start, ce = cstack.top; cp < ce; cp++)
    {
      Constraint *c = *cp;
      if (called_on_blocked_clauses)
        {
          assert (c->qbcp_qbce_blocking_lit);
          assert (c->qbcp_qbce_blocked);
          c->qbcp_qbce_blocking_lit = 0;
          c->qbcp_qbce_blocked = 0;
        }
      else
        {
          assert (c->qbcp_qbce_mark);
          c->qbcp_qbce_mark = 0;
        }
      if (qdpll->options.verbosity >= 3)
        {
          fprintf (stderr, "  during backtrack: resetting %s clause pending at level %d: ", 
                   called_on_blocked_clauses ? "blocked" : "marked", decision_level);
          print_constraint (qdpll, c);
        }
    }
  /* Do not delete 'cstack', but only reset to allow for later
     reuse. This avoids malloc/free operations during decision making and
     backtracking. */
  assert (stack->top >= stack->start);
  QDPLL_RESET_STACK (*(stack->top));
}

static void
backtrack_undo_assignment (QDPLL * qdpll, Var * var, const int notify_active)
{
  assert (QDPLL_VAR_ASSIGNED (var));
  assert (var->assignment != QDPLL_ASSIGNMENT_UNDEF);
  assert (var->mode != QDPLL_VARMODE_UNDEF);
  assert (var->decision_level > 0);
  assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
  assert (var->trail_pos != QDPLL_INVALID_TRAIL_POS);
  assert (var->trail_pos <
          (unsigned int) (qdpll->assigned_vars_top - qdpll->assigned_vars));
  assert (qdpll->assigned_vars[var->trail_pos] == var->id);
  QDPLLDepManGeneric *dm = qdpll->dm;

  if (var->mode == QDPLL_VARMODE_LBRANCH
      || var->mode == QDPLL_VARMODE_RBRANCH)
    {
      /* Must remove decision variables from dec-stack. */
      assert (!QDPLL_EMPTY_STACK (qdpll->dec_vars));
      assert (*(qdpll->dec_vars.top - 1) == var->id);
      QDPLL_POP_STACK (qdpll->dec_vars);
      if (!qdpll->options.no_empty_formula_watching)
        {
          assert (var->decision_level == 
                  QDPLL_COUNT_STACK (qdpll->empty_formula_watchers_per_dec_level));
          assert (!QDPLL_EMPTY_STACK (qdpll->empty_formula_watchers_per_dec_level));
          qdpll->empty_formula_watcher = 
            QDPLL_POP_STACK (qdpll->empty_formula_watchers_per_dec_level);
        }
      if (!qdpll->options.no_qbce_dynamic)
        {
          /* Remove stack of clauses blocked at decision level of 'var' and reset
             blocked-flag of clauses. */
          qbcp_qbce_backtrack_clear_stack_of_stacks 
            (qdpll, &qdpll->qbcp_qbce_blocked_clauses, 1, var->decision_level);
          /* Remove stack of clauses marked at decision level of 'var' and reset
             marked-flag of clauses. */
          qbcp_qbce_backtrack_clear_stack_of_stacks 
            (qdpll, &qdpll->qbcp_qbce_marked_clauses, 0, var->decision_level);
        }
    }

  var->mode = QDPLL_VARMODE_UNDEF;
  var->assignment = QDPLL_ASSIGNMENT_UNDEF;
  var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
  var->trail_pos = QDPLL_INVALID_TRAIL_POS;
  if (var->antecedent)
    {
      assert (!var->antecedent->qbcp_qbce_blocked);
      assert (var->antecedent->is_reason);
      var->antecedent->is_reason = 0;
      var->antecedent = 0;
    }

  if (qdpll->options.qbce_inprocessing || !qdpll->options.no_qbce_dynamic)
    {
    }

  /* must put candidate variables back on pqueue. */
  if (dm->is_candidate (dm, var->id)
      && var->priority_pos == QDPLL_INVALID_PQUEUE_POS)
    var_pqueue_insert (qdpll, var->id, var->priority);

  if (QDPLL_VAR_MARKED_PROPAGATED (var))
    {
      QDPLL_VAR_UNMARK_PROPAGATED (var);
      if (notify_active)
        {
          dm->notify_active (dm, var->id);
        }
    }
}

static void
qbcp_qbce_reset_offset_in_working_queue (QDPLL *qdpll, QBCENonBlockedWitness pair)
{
  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "WATCHING: reset queue offset of maybe-blocked pair\n");
    }
  /* Reset offset-in-working-queue of 'pair' on notify list. */
  Constraint *c = pair.blit_occ.constraint;
  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "WATCHING:   non-bl-lit %d, wo-value %d and clause: ", pair.non_blocking_lit, pair.offset.witness_in_witness_list);
      print_constraint (qdpll, c);
    }
  assert (pair.offset.witness_in_witness_list < 
          QDPLL_COUNT_STACK (c->qbcp_qbce_witness_clauses));
  QBCENonBlockedWitness witness_pair = 
    c->qbcp_qbce_witness_clauses.start[pair.offset.witness_in_witness_list];
  assert (witness_pair.non_blocking_lit == pair.non_blocking_lit);
  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "WATCHING:   witness clause with mo-offset %d: ", witness_pair.offset.maybe_blocked_clause_in_notify_list);
      print_constraint (qdpll, witness_pair.blit_occ.constraint);
    }
  unsigned int offset_of_pair_in_notify_list = 
    witness_pair.offset.maybe_blocked_clause_in_notify_list;
  assert (offset_of_pair_in_notify_list != QDPLL_INVALID_WATCHER_POS);
  Constraint *w = witness_pair.blit_occ.constraint;
  assert (offset_of_pair_in_notify_list < 
          QDPLL_COUNT_STACK (w->qbcp_qbce_notify_maybe_blocked_clauses));
  assert (w->qbcp_qbce_notify_maybe_blocked_clauses.start
          [offset_of_pair_in_notify_list].offset_in_working_queue != QDPLL_INVALID_WATCHER_POS);
  w->qbcp_qbce_notify_maybe_blocked_clauses.start
    [offset_of_pair_in_notify_list].offset_in_working_queue = QDPLL_INVALID_WATCHER_POS;
}

/* Undo assignments until 'backtrack_level'. */
static void
backtrack (QDPLL * qdpll, unsigned int backtrack_level)
{
  /* We never backtrack to level 0, this case is handled
     separately. Note that this is due to the semantics of the variable
     'backtrack_level': backtracking to level 0 is indicated by value 1,
     i.e. all assignments up to and including level 1 are deleted. */
  assert (backtrack_level > 0);
  assert (backtrack_level != QDPLL_INVALID_DECISION_LEVEL);
  assert (QDPLL_ASSIGNMENT_TRUE == -QDPLL_ASSIGNMENT_FALSE);
  assert (QDPLL_ASSIGNMENT_FALSE == -QDPLL_ASSIGNMENT_TRUE);
  assert (qdpll->old_bcp_ptr >= qdpll->assigned_vars);
  assert (qdpll->old_bcp_ptr <= qdpll->bcp_ptr);
  qdpll->state.num_backtracks++;

  if (!qdpll->options.no_empty_formula_watching)
    {
      /* Reset marks of variables appearing in the clause currently being watched,
         if any (no clause is watched if we indeed detected the empty
         formula). The watched clause will be updated during backtracking with
         respect to the decision level we backtrack to. */
      update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 0);
    }

  VarID *p, *e, *old_bcp_ptr;
  Var *vars = qdpll->pcnf.vars;
  old_bcp_ptr = qdpll->old_bcp_ptr;

  for (p = qdpll->assigned_vars_top - 1, e = qdpll->assigned_vars; p >= e;
       p--)
    {
      Var *assigned_var = VARID2VARPTR (vars, *p);
      assert (QDPLL_VAR_ASSIGNED (assigned_var));
      assert (assigned_var->assignment != QDPLL_ASSIGNMENT_UNDEF);
      assert (assigned_var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
      assert (assigned_var->mode != QDPLL_VARMODE_UNDEF);
      assert (assigned_var->mode != QDPLL_VARMODE_LBRANCH
              || !assigned_var->antecedent);
      assert (assigned_var->mode != QDPLL_VARMODE_RBRANCH
              || !assigned_var->antecedent);

      unsigned int var_decision_level = assigned_var->decision_level;
      if (var_decision_level >= backtrack_level)
        backtrack_undo_assignment (qdpll, assigned_var, p < old_bcp_ptr);
      else
        {
          assert (var_decision_level < backtrack_level);
          break;
        }
    }

  qdpll->state.decision_level = backtrack_level - 1;
  assert (qdpll->state.decision_level != QDPLL_INVALID_DECISION_LEVEL);
  qdpll->old_bcp_ptr = qdpll->bcp_ptr = qdpll->assigned_vars_top = p + 1;

  if (!qdpll->options.no_empty_formula_watching)
    {
      assert (qdpll->empty_formula_watcher);
      /* Set marks of variables appearing in the clause currently being
         watched. The watched clause was updated during backtracking. */
      update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 1);
      assert (!qdpll->empty_formula_watcher->constraint->qbcp_qbce_blocked);
      assert (!is_clause_satisfied (qdpll, qdpll->empty_formula_watcher->constraint));
      assert (QDPLL_COUNT_STACK 
              (qdpll->empty_formula_watchers_per_dec_level) == 
              qdpll->state.decision_level);
    }

  /* Must reset stack of clauses pending to be checked by QBCE. For each
     decision level, we apply QBCE until saturation under the current
     assignment, unless there is a conflict or empty formula detected
     earlier. */
  /* Reset offsets on working queue. */
  while (!QDPLL_EMPTY_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses))
    {
      QBCENonBlockedWitness pair = 
        QDPLL_POP_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
      if (pair.offset.witness_in_witness_list != QDPLL_INVALID_WATCHER_POS)
        qbcp_qbce_reset_offset_in_working_queue (qdpll, pair);
    }
}

static Var *
select_decision_variable (QDPLL * qdpll)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *decision_var = 0, *candidate_var, *vars = qdpll->pcnf.vars;
  VarID candidate, decision_var_id;

  /* Get candidates from dependency manager. */
  while ((candidate = dm->get_candidate (dm)))
    {
      /* Add candidates to priority queue. */
      assert (candidate > 0);
      candidate_var = VARID2VARPTR (vars, candidate);
      assert (dm->is_candidate (dm, candidate));

      if (!QDPLL_VAR_ASSIGNED (candidate_var) &&
          candidate_var->priority_pos == QDPLL_INVALID_PQUEUE_POS)
        var_pqueue_insert (qdpll, candidate_var->id, candidate_var->priority);
    }

#ifndef NDEBUG
#if QDPLL_ASSERT_CANDIDATES_ON_PQUEUE
  assert_candidates_on_pqueue (qdpll);
#endif
#endif

  do
    {
      decision_var_id = var_pqueue_remove_min (qdpll);
      assert (decision_var_id > 0);
      QDPLL_ABORT_QDPLL (!decision_var_id,
                         "Fatal Error: did not find decision variable!");
      decision_var = VARID2VARPTR (vars, decision_var_id);
      /* Candidates on queue possibly already assigned (unit or pure literals). */
      assert (decision_var->priority_pos == QDPLL_INVALID_PQUEUE_POS);
    }
  while (QDPLL_VAR_ASSIGNED (decision_var)
         || !dm->is_candidate (dm, decision_var_id));

  assert (decision_var->mode == QDPLL_VARMODE_UNDEF);
  assert (!QDPLL_VAR_ASSIGNED (decision_var));
  assert (decision_var->decision_level == QDPLL_INVALID_DECISION_LEVEL);

  return decision_var;
}


static unsigned int
compute_sdcl_score_from_clause (QDPLL * qdpll, Var * var, Constraint * clause)
{
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *v = LIT2VARPTR (vars, lit);
      if (v != var)
        {
          /* Clause is already satisfied by another literal. */
          if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (v)) ||
              (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (v)))
            return 1;
        }
    }
  return 0;
}

static unsigned int
compute_sdcl_score (QDPLL * qdpll, Var * var, LitID lit, BLitsOccStack * occs)
{
  unsigned int sum = 0;
  BLitsOcc *bp, *be;
  for (bp = occs->start, be = occs->top; bp < be; bp++)
    {
      if (bp->constraint->qbcp_qbce_blocked)
        continue;
      assert (!BLIT_MARKED_PTR (bp->constraint));
      sum += compute_sdcl_score_from_clause (qdpll, var, bp->constraint);
    }
  return sum;
}

static QDPLLAssignment
sdcl_friendly_dec_heuristic (QDPLL * qdpll, Var * var)
{
  unsigned int pos_score, neg_score;

  neg_score =
    compute_sdcl_score (qdpll, var, -var->id, &(var->neg_occ_clauses));
  pos_score =
    compute_sdcl_score (qdpll, var, var->id, &(var->pos_occ_clauses));

  if (neg_score < pos_score)
    return QDPLL_ASSIGNMENT_TRUE;
  else
    return QDPLL_ASSIGNMENT_FALSE;
}

static unsigned int
compute_qtype_score (QDPLL * qdpll, Var * var, LitID lit,
                     BLitsOccStack * occs)
{
  unsigned int sum = 0;
  BLitsOcc *bp, *be;
  for (bp = occs->start, be = occs->top; bp < be; bp++)
    {
      assert (!BLIT_MARKED_PTR (bp->constraint));
      assert (!bp->constraint->is_cube);
      if (bp->constraint->qbcp_qbce_blocked)
        continue;
      if (!is_clause_satisfied (qdpll, bp->constraint))
        {
          assert (!is_clause_empty (qdpll, bp->constraint));
          sum++;
        }
    }
  return sum;
}


/* Select decision assignment by quantifier type: for univ./exists
   vars, try to falsify/satisfy clauses. */
static QDPLLAssignment
qtype_dec_heuristic (QDPLL * qdpll, Var * var)
{
  unsigned int pos_score, neg_score;

  neg_score =
    compute_qtype_score (qdpll, var, -var->id, &(var->neg_occ_clauses));
  pos_score =
    compute_qtype_score (qdpll, var, var->id, &(var->pos_occ_clauses));

  /* Assuming only orig. clauses kept in occ-lists, count how many
     occs are unsat for each phase. Then choose assignment wrt. that
     number. */
  if (neg_score < pos_score)
    return var->scope->type == QDPLL_QTYPE_EXISTS ?
      QDPLL_ASSIGNMENT_TRUE : QDPLL_ASSIGNMENT_FALSE;
  else
    return var->scope->type == QDPLL_QTYPE_EXISTS ?
      QDPLL_ASSIGNMENT_FALSE : QDPLL_ASSIGNMENT_TRUE;
}


static QDPLLAssignment
falsify_dec_heuristic (QDPLL *qdpll, Var * var)
{
  unsigned int pos_score, neg_score;
  neg_score =
    compute_qtype_score (qdpll, var, -var->id, &(var->neg_occ_clauses));
  pos_score =
    compute_qtype_score (qdpll, var, var->id, &(var->pos_occ_clauses));

  /* Try to falsify as many unsatisfied original clauses as possible. */

  if (neg_score < pos_score)
    return QDPLL_ASSIGNMENT_FALSE;
  else 
    return QDPLL_ASSIGNMENT_TRUE;
}


static QDPLLAssignment
satisfy_dec_heuristic (QDPLL *qdpll, Var * var)
{
  /* Try to satisfy as many unsatisfied original clauses as possible. */
  return falsify_dec_heuristic (qdpll, var) == QDPLL_ASSIGNMENT_FALSE ? 
    QDPLL_ASSIGNMENT_TRUE : QDPLL_ASSIGNMENT_FALSE;
}


static QDPLLAssignment
select_decision_assignment (QDPLL * qdpll, Var * decision_var)
{
  if (qdpll->options.dh == QDPLL_DH_SIMPLE)
    {
      assert (qdpll->options.no_exists_cache);
      assert (qdpll->options.no_univ_cache);
      return QDPLL_ASSIGNMENT_FALSE;
    }
  else if (qdpll->options.dh == QDPLL_DH_RANDOM)
    {
      /* NOTE: ALWAYS make a random decision, do NOT consider cached
         assignments. This is mainly for testing. */
      return (rand () % 2) ? QDPLL_ASSIGNMENT_TRUE : QDPLL_ASSIGNMENT_FALSE;
    }
  else
    {
      if ((QDPLL_VAR_FORALL (decision_var) && !qdpll->options.no_univ_cache)
          || (QDPLL_VAR_EXISTS (decision_var)
              && !qdpll->options.no_exists_cache))
        {
          assert (QDPLL_ASSIGNMENT_FALSE == -QDPLL_ASSIGNMENT_TRUE);
          /* Return cached assignment if any. */
          QDPLLAssignment a;
          if ((a = decision_var->cached_assignment))
            return a;
        }

      if (qdpll->options.dh == QDPLL_DH_SDCL)
        return sdcl_friendly_dec_heuristic (qdpll, decision_var);
      else if (qdpll->options.dh == QDPLL_DH_QTYPE)
        return qtype_dec_heuristic (qdpll, decision_var);
      else if (qdpll->options.dh == QDPLL_DH_FALSIFY)
        return falsify_dec_heuristic (qdpll, decision_var);
      else
        {
          assert (qdpll->options.dh == QDPLL_DH_SATISFY);
          return satisfy_dec_heuristic (qdpll, decision_var);
        }
    }
}


/* Before literal watchers are updated: check if the blocking literal
   in 'blit' disables the constraint in 'blit'. If so, then need not
   update watchers -> return 0. Otherwise return the stripped pointer
   to the constraint. */
static Constraint *
check_disabling_blocking_lit (QDPLL * qdpll, BLitsOcc blit_occ,
                              const int called_on_pure_lits)
{
#if COMPUTE_STATS
  if (called_on_pure_lits)
    qdpll->stats.blits_pure_tested++;
  else
    qdpll->stats.blits_tested++;
#endif
  assert (blit_occ.blit);
  assert (blit_occ.constraint);
  /* Blocking literal must occur in constraint. If the blocking literal is a
     literal of an internal variable then we must properly rename them if the
     variable is enlarged dynamically. */
  assert (constraint_has_lit (BLIT_STRIP_PTR(blit_occ.constraint), blit_occ.blit));
  Constraint *constraint = blit_occ.constraint;
  LitID lit = blit_occ.blit;
  Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
  const int is_cube = BLIT_MARKED_PTR (constraint);
  if (is_cube)
    {
      if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)) ||
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)))
        {
#if COMPUTE_STATS
          if (called_on_pure_lits)
            qdpll->stats.blits_pure_disabling++;
          else
            qdpll->stats.blits_disabling++;
#endif
          return 0;
        }
    }
  else
    {
      if ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)))
        {
#if COMPUTE_STATS
          if (called_on_pure_lits)
            qdpll->stats.blits_pure_disabling++;
          else
            qdpll->stats.blits_disabling++;
#endif
          return 0;
        }
    }

  /* Blocking literal does not disable constraint, so return stripped pointer. */
  return BLIT_STRIP_PTR (constraint);
}


/* Propagate the effects of setting 'var' to 'true' or 'false'. */
static QDPLLSolverState
propagate_variable_assigned (QDPLL * qdpll, Var * var,
                             LitIDStack * clause_notify_list,
                             BLitsOccStack * lit_notify_list)
{
  assert (var->id);
  assert (QDPLL_VAR_ASSIGNED (var));
  assert (var->mode != QDPLL_VARMODE_UNDEF);
  assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
  assert (!QDPLL_VAR_ASSIGNED_TRUE (var)
          || clause_notify_list == &(var->pos_notify_clause_watchers));
  assert (!QDPLL_VAR_ASSIGNED_TRUE (var)
          || lit_notify_list == &(var->pos_notify_lit_watchers));
  assert (!QDPLL_VAR_ASSIGNED_FALSE (var)
          || clause_notify_list == &(var->neg_notify_clause_watchers));
  assert (!QDPLL_VAR_ASSIGNED_FALSE (var)
          || lit_notify_list == &(var->neg_notify_lit_watchers));
#if COMPUTE_STATS
  qdpll->stats.total_notify_litw_list_size +=
    QDPLL_SIZE_STACK (*lit_notify_list);
  qdpll->stats.total_notify_litw_list_cnt +=
    QDPLL_COUNT_STACK (*lit_notify_list);
  qdpll->stats.total_notify_litw_list_adds++;
  qdpll->stats.total_notify_clausew_list_size +=
    QDPLL_SIZE_STACK (*clause_notify_list);
  qdpll->stats.total_notify_clausew_list_cnt +=
    QDPLL_COUNT_STACK (*clause_notify_list);
  qdpll->stats.total_notify_clausew_list_adds++;
  /* Sum up both occ-lists. */
  qdpll->stats.total_occ_list_cnt += QDPLL_COUNT_STACK (var->neg_occ_clauses);
  qdpll->stats.total_occ_list_cnt += QDPLL_COUNT_STACK (var->pos_occ_clauses);
  qdpll->stats.total_occ_list_adds++;
#endif

  QDPLLDepManGeneric *dm = qdpll->dm;

  QDPLL_VAR_MARK_PROPAGATED (var);

  if (!qdpll->options.no_pure_literals)
    notify_clause_watching_variables (qdpll, clause_notify_list);

  /* Check clauses for units and conflicts. */
  BLitsOcc *p, *e;
  Constraint *c, *sentinel;
  for (p = lit_notify_list->start, e = lit_notify_list->top; p < e; p++)
    {
      if (!(c = check_disabling_blocking_lit (qdpll, *p, 0)))
        continue;
      /* A clause 'c' which appears on this list has one of its two watched
         literals falsified. This clause may also be blocked in the dynamic
         variant of QBCE. Then we simply ignore it. */
      if (c->qbcp_qbce_blocked)
        continue;
      assert (c && !BLIT_MARKED_PTR (c));
      if (!(sentinel = update_literal_watchers (qdpll, var, p)))
        {
          /* Conflict detected either by empty clause or attempted 
             to enqueue complementary assignments. */
          if (!qdpll->options.no_spure_literals)
            {
              if (has_constraint_spurious_pure_lit (qdpll, c))
                {
#if COMPUTE_STATS
                  if (c->is_cube)
                    qdpll->stats.total_splits_ignored_satisfied_cubes++;
                  else
                    qdpll->stats.total_splits_ignored_empty_clauses++;
#endif
                  continue;
                }
            }

          assert (c->is_cube || is_clause_empty (qdpll, c));
          assert (c->is_cube || !is_clause_satisfied (qdpll, c));
          assert (!c->is_cube || !is_cube_empty (qdpll, c));
          assert (!c->is_cube || is_cube_satisfied (qdpll, c));
          assert (!qdpll->result_constraint);

          if (c->learnt)
            {
              if (!qdpll->options.no_res_mtf)
                learnt_constraint_mtf (qdpll, c);
#if COMPUTE_STATS
              assert (!c->derived_by_trivial_truth_or_falsity || 
                      !c->derived_by_dynamic_nenofex);
              if (c->is_cube)
                {
                  qdpll->stats.total_sat_lcubes++;
                  if (c->is_taut)
                    qdpll->stats.total_sat_taut_lcubes++;
                  if (c->derived_by_trivial_truth_or_falsity)
                    qdpll->stats.trivial_truth_satisfied_cubes++;
                  else if (c->derived_by_dynamic_nenofex)
                    qdpll->stats.dyn_nenofex_satisfied_cubes++;;
                }
              else
                {
                  qdpll->stats.total_empty_lclauses++;
                  if (c->is_taut)
                    qdpll->stats.total_empty_taut_lclauses++;
                  if (c->derived_by_trivial_truth_or_falsity)
                    qdpll->stats.trivial_falsity_conflicting_clauses++;
                  else if (c->derived_by_dynamic_nenofex)
                    qdpll->stats.dyn_nenofex_conflicting_clauses++;;
                }
#endif
            }

          qdpll->result_constraint = c;
          if (!c->is_cube)
            return QDPLL_SOLVER_STATE_UNSAT;
          else
            {
#if COMPUTE_STATS
              qdpll->stats.total_sat_cubes++;
#endif
              return QDPLL_SOLVER_STATE_SAT;
            }
        }
      else if (sentinel != c)
        {                       /* Sentinel for entry deletion: old last entry has overwritten current one. */
          /* The clause's position list has been modified already. */
          e--;
          p--;
        }
      /* Othwerwise, entry has not been deleted or last entry was deleted -> exit anyway. */
    }

  /* At this point, state can only be undefined. */
  return QDPLL_SOLVER_STATE_UNDEF;
}

/* Count assignment at top level. 
   NOTE: this could also be maintained incrementally.*/
static unsigned int
sizeof_top_level (QDPLL * qdpll)
{
  unsigned int result = 0;
  Var *vars = qdpll->pcnf.vars;
  VarID *p, *e;
  for (p = qdpll->assigned_vars, e = qdpll->assigned_vars_top; p < e; p++)
    {
      Var *var = VARID2VARPTR (vars, *p);
      assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
      if (var->decision_level == 0)
        result++;
      else
        break;
    }
  return result;
}


/* Check if 'lit' could be reduced by forall-reduction under the
   current partial assignment. Ignore assigned literals. */
static int
is_lit_reducible_in_clause (QDPLL * qdpll, LitID lit, Constraint * c,
                            VarID ignorevar)
{
  assert (!c->is_cube);
  assert (!c->learnt);
  Var *vars = qdpll->pcnf.vars;
  VarID varid = LIT2VARID (lit);
  Var *var = VARID2VARPTR (vars, varid);
  assert (!QDPLL_VAR_ASSIGNED (var));
  if (var->scope->type == QDPLL_QTYPE_EXISTS)
    return 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      assert (*p);
      Var *pvar = LIT2VARPTR (vars, *p);
      if (pvar->id == ignorevar)
        continue;
      /* Any assigned literal must be false. Satisfied clauses should have
         been handled outside this function. */
      assert (!QDPLL_VAR_ASSIGNED (pvar) ||
              (QDPLL_VAR_ASSIGNED_FALSE (pvar) && QDPLL_LIT_POS (*p)) ||
              (QDPLL_VAR_ASSIGNED_TRUE (pvar) && QDPLL_LIT_NEG (*p)));
      if (QDPLL_VAR_ASSIGNED (pvar))
        continue;
      if (qdpll->dm->depends (qdpll->dm, varid, pvar->id))
        return 0;
    }
  return 1;
}


/* For assertion checking only. */
static int
assumptions_given (QDPLL *qdpll)
{
  VarID *p, *e;
  for (p = qdpll->assigned_vars, e = qdpll->assigned_vars_top; p < e; p++)
    {
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, *p);
      if (var->mode == QDPLL_VARMODE_ASSUMED)
        return 1;
    }
  return 0;
}

/* --------------------- START: QBCP-QBCE --------------------- */

/* Returns pointer to item found in list, or zero otherwise. */
static QBCENonBlockedWitness *
qbcp_qbce_find_pair_in_list (QDPLL *qdpll, QBCENonBlockedWitnessStack *list, 
                             QBCENonBlockedWitness pair, 
                             const int find_clause_only, 
                             const int find_lit_only)
{
#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_find_entry_calls++;
#endif
  assert (!find_clause_only || !find_lit_only);
  assert (pair.non_blocking_lit || pair.blit_occ.constraint);
  QBCENonBlockedWitness *p, *e;
  for (p = list->start, e = list->top; p < e; p++)
    {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_find_entries_seen++;
#endif
      QBCENonBlockedWitness w = *p;
      if ((find_clause_only || w.non_blocking_lit == pair.non_blocking_lit) && 
          (find_lit_only || w.blit_occ.constraint == pair.blit_occ.constraint))
        return p;
    }
  return 0;
}

/* Returns pointer to item found in list, or zero otherwise. */
static QBCENonBlockedWitness *
qbcp_qbce_find_clause_in_list (QDPLL *qdpll, QBCENonBlockedWitnessStack *list, 
                            Constraint *c)
{
  /* Only entry 'c' matters in object 'pair', other members filled by dummy values. */
  QBCENonBlockedWitness pair = {0, {0, c}, {QDPLL_INVALID_WATCHER_POS}, 
                                QDPLL_INVALID_WATCHER_POS};
  return qbcp_qbce_find_pair_in_list (qdpll, list, pair, 1, 0);
}

/* Returns pointer to item found in list, or zero otherwise. */
static QBCENonBlockedWitness *
qbcp_qbce_find_lit_in_list (QDPLL *qdpll, QBCENonBlockedWitnessStack *list, 
                            LitID lit)
{
  /* Only entry 'lit' matters in object 'pair', other members filled by dummy values. */
  QBCENonBlockedWitness pair = {lit, {0, 0}, {QDPLL_INVALID_WATCHER_POS}, 
                                QDPLL_INVALID_WATCHER_POS};
  return qbcp_qbce_find_pair_in_list (qdpll, list, pair, 0, 1);
}

/* Delete entry at 'entry_p' from 'list' by overwriting it with last entry,
   assuming that entry actually appears in 'list'. */
static void
qbcp_qbce_delete_list_entry (QDPLL *qdpll, QBCENonBlockedWitnessStack *list, 
                             QBCENonBlockedWitness *entry_p, 
			     const int is_witness_entry)
{
  assert (entry_p);
  assert (entry_p >= list->start);
  assert (entry_p < list->top);
  QBCENonBlockedWitness deleted = *entry_p;
  QBCENonBlockedWitness last = QDPLL_POP_STACK (*list);
  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "WATCHING: deleting list entry, new list size %u\n", QDPLL_COUNT_STACK (*list));
      fprintf (stderr, "WATCHING: deleting %s entry -- last item:\n", is_witness_entry ? "witness" : "maybe-blocked-clause");
      fprintf (stderr, "WATCHING:   clause: ");
      print_constraint (qdpll, last.blit_occ.constraint);
      fprintf (stderr, "WATCHING:   non-bl-lit: %d\n", last.non_blocking_lit);
      fprintf (stderr, "WATCHING:   %s-offset: %d\n", is_witness_entry ? "mo" : "wo", is_witness_entry ? last.offset.maybe_blocked_clause_in_notify_list : last.offset.witness_in_witness_list);
      fprintf (stderr, "WATCHING:   deleting %s entry -- deleted item:\n", is_witness_entry ? "witness" : "maybe-blocked-clause");
      fprintf (stderr, "WATCHING:     clause: ");
      print_constraint (qdpll, entry_p->blit_occ.constraint);
      fprintf (stderr, "WATCHING:     non-bl-lit: %d\n", entry_p->non_blocking_lit);
      fprintf (stderr, "WATCHING:     %s-offset: %d\n", is_witness_entry ? "mo" : "wo", is_witness_entry ? entry_p->offset.maybe_blocked_clause_in_notify_list : entry_p->offset.witness_in_witness_list);
    }
  *entry_p = last;
  unsigned int new_offset = entry_p - list->start;
  if (is_witness_entry)
    {
      /* Update positions only if ordering of elements was changed by deletion. */
      if (last.blit_occ.constraint != deleted.blit_occ.constraint ||  
          last.non_blocking_lit != deleted.non_blocking_lit)
        {
          QBCENonBlockedWitness *maybe_blocked_pair_p = 
            entry_p->blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start + 
            last.offset.maybe_blocked_clause_in_notify_list;
          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "WATCHING:   updating wo-value from %d to %d of clause (due to non-empty list after del.): ", maybe_blocked_pair_p->offset.witness_in_witness_list, new_offset);
              print_constraint (qdpll, maybe_blocked_pair_p->blit_occ.constraint);
            }
          maybe_blocked_pair_p->offset.witness_in_witness_list = new_offset;
          if (maybe_blocked_pair_p->offset_in_working_queue != QDPLL_INVALID_WATCHER_POS)
            {
              assert (maybe_blocked_pair_p->offset_in_working_queue < 
                      QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses));
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "WATCHING:   update wo-values of enqueued item with non-bl-lit %d, wo-value %d, and clause: ", qdpll->qbcp_qbce_maybe_blocked_clauses.start[maybe_blocked_pair_p->offset_in_working_queue].non_blocking_lit, qdpll->qbcp_qbce_maybe_blocked_clauses.start[maybe_blocked_pair_p->offset_in_working_queue].offset.witness_in_witness_list);
                  print_constraint (qdpll, qdpll->qbcp_qbce_maybe_blocked_clauses.start[maybe_blocked_pair_p->offset_in_working_queue].blit_occ.constraint);
                }
              /* Update witness offset for pair in working queue. */
              qdpll->qbcp_qbce_maybe_blocked_clauses.start
                [maybe_blocked_pair_p->offset_in_working_queue].
                offset.witness_in_witness_list = new_offset;
            }
        }
    }
  else
    {
      /* Update positions only if ordering of elements was changed by deletion. */
      if (last.blit_occ.constraint != deleted.blit_occ.constraint ||  
          last.non_blocking_lit != deleted.non_blocking_lit)
        {
          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "WATCHING:   NOTE: updating mo-value from %d to %d of clause: ", entry_p->blit_occ.constraint->qbcp_qbce_witness_clauses.start
                       [last.offset.witness_in_witness_list].
                       offset.maybe_blocked_clause_in_notify_list, new_offset);
              print_constraint (qdpll, entry_p->blit_occ.constraint->qbcp_qbce_witness_clauses.start
                                [last.offset.witness_in_witness_list].blit_occ.constraint);
            }
          entry_p->blit_occ.constraint->qbcp_qbce_witness_clauses.start
            [last.offset.witness_in_witness_list].
            offset.maybe_blocked_clause_in_notify_list = new_offset;
        }
    }
}

/* Returns position of 'witness' in list 'watched_occs', or zero otherwise. */
static Constraint **
qbcp_qbce_find_watched_occ (QDPLL *qdpll, ConstraintPtrStack *watched_occs, 
                            Constraint *witness)
{
#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_watched_occ_find_entry_calls++;
#endif
  Constraint **p, **e;
  for (p = watched_occs->start, e = watched_occs->top; p < e; p++)
    {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_watched_occ_find_entries_seen++;
#endif
      if (*p == witness)
        return p;
    }
  return 0;
}

/* Store 'witness' in lists of watched pos/neg occurrences. This is necessary
   to trigger QBCE from clauses which are satisfied by new assignments. */
static void
qbcp_qbce_store_watched_occ (QDPLL *qdpll, Constraint *witness)
{
#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_calls++;
#endif
  /* If 'witness' has currently no clauses to be notified, then the first
     clause will be inserted in 'qbcp_qbce_store_witness' later. In this case
     'witness' has not been used as a witness before and hence it must be
     inserted into the lists of watched occurrences of variables. Otherwise,
     'witness' already appears in the watched occurrences and no work is done
     here. */
  if (QDPLL_EMPTY_STACK (witness->qbcp_qbce_notify_maybe_blocked_clauses))
    {
      LitID * const start = witness->lits;
      LitID *p, *e;
      for (p = start, e = p + witness->num_lits; p < e; p++)
        {
#if COMPUTE_STATS
          qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_lits_seen++;
#endif
          LitID lit = *p;
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          if (QDPLL_LIT_NEG (lit))
            {
              assert (!qbcp_qbce_find_watched_occ 
                      (qdpll, &var->qbcp_qbce_watched_neg_occ_clauses, witness));
              assert (QDPLL_COUNT_STACK (var->qbcp_qbce_watched_neg_occ_clauses) == 
                      QDPLL_COUNT_STACK (var->qbcp_qbce_offset_of_neg_lit_in_watched_occ));
              QDPLL_PUSH_STACK (qdpll->mm, witness->qbcp_qbce_offset_of_witness_in_watched_occs, 
                                QDPLL_COUNT_STACK (var->qbcp_qbce_watched_neg_occ_clauses));
              QDPLL_PUSH_STACK 
                (qdpll->mm, var->qbcp_qbce_watched_neg_occ_clauses, witness);
              assert (start <= p);
              QDPLL_PUSH_STACK 
                (qdpll->mm, var->qbcp_qbce_offset_of_neg_lit_in_watched_occ, (unsigned int)(p - start));
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              assert (!qbcp_qbce_find_watched_occ 
                      (qdpll, &var->qbcp_qbce_watched_pos_occ_clauses, witness));
              assert (QDPLL_COUNT_STACK (var->qbcp_qbce_watched_pos_occ_clauses) == 
                      QDPLL_COUNT_STACK (var->qbcp_qbce_offset_of_pos_lit_in_watched_occ));
              QDPLL_PUSH_STACK (qdpll->mm, witness->qbcp_qbce_offset_of_witness_in_watched_occs, 
                                QDPLL_COUNT_STACK (var->qbcp_qbce_watched_pos_occ_clauses));
              QDPLL_PUSH_STACK 
                (qdpll->mm, var->qbcp_qbce_watched_pos_occ_clauses, witness);
              assert (start <= p);
              QDPLL_PUSH_STACK 
                (qdpll->mm, var->qbcp_qbce_offset_of_pos_lit_in_watched_occ, (unsigned int)(p - start));
            } 
        }
    }
}

static void
qbcp_qbce_delete_watched_occ_entry (ConstraintPtrStack *occ_list, 
                                    VarIDStack *offset_list, 
                                    unsigned int entry_offset)
{
  Constraint ** clause_entry_p = occ_list->start + entry_offset;
  assert (clause_entry_p >= occ_list->start);
  assert (clause_entry_p < occ_list->top);
  Constraint *del_clause = *clause_entry_p;
  unsigned int * offset_entry_p = offset_list->start + entry_offset;
  assert (offset_entry_p >= offset_list->start);
  assert (offset_entry_p < offset_list->top);
  unsigned int del_offset = *offset_entry_p;
  /* Get last elements in lists to overwrite deleted ones. */
  assert (QDPLL_COUNT_STACK (*occ_list) == 
          QDPLL_COUNT_STACK (*offset_list));
  Constraint * clause_last = QDPLL_POP_STACK (*occ_list);
  unsigned int offset_last = QDPLL_POP_STACK (*offset_list);
  /* Delete entries. */
  *clause_entry_p = clause_last;
  *offset_entry_p = offset_last;
  /* If necessary, update offset entry in witness clause. */
  if (del_clause != clause_last)
    {
      assert (clause_last->
        qbcp_qbce_offset_of_witness_in_watched_occs.start
              [offset_last] == QDPLL_COUNT_STACK (*occ_list));
      clause_last->
        qbcp_qbce_offset_of_witness_in_watched_occs.start
        [offset_last] = entry_offset;
    }
}

/* Remove 'witness' from lists of watched pos/neg occurrences. See also
   'qbcp_qbce_store_watched_occ'. */
static void
qbcp_qbce_remove_watched_occ (QDPLL *qdpll, Constraint *old_witness)
{
#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_calls++;
#endif
  /* If 'old_witness' is no longer used as a witness for any clause being
     non-blocked, then remove 'old_witness' from the lists of watched occurrences
     of variables. */
  if (QDPLL_EMPTY_STACK (old_witness->qbcp_qbce_notify_maybe_blocked_clauses))
    {
      LitID * const start = old_witness->lits;
      LitID *p, *e;
      for (p = start, e = p + old_witness->num_lits; p < e; p++)
        {
#if COMPUTE_STATS
          qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_lits_seen++;
#endif
          LitID lit = *p;
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          assert ((unsigned int)(p - start) < QDPLL_COUNT_STACK 
                  (old_witness->qbcp_qbce_offset_of_witness_in_watched_occs));
          unsigned int offset = old_witness->
            qbcp_qbce_offset_of_witness_in_watched_occs.start[p - start];
          if (QDPLL_LIT_NEG (lit))
            {
              assert (qbcp_qbce_find_watched_occ 
                      (qdpll, &var->qbcp_qbce_watched_neg_occ_clauses, old_witness) == 
                      var->qbcp_qbce_watched_neg_occ_clauses.start + offset);
              qbcp_qbce_delete_watched_occ_entry 
                (&var->qbcp_qbce_watched_neg_occ_clauses, 
                 &var->qbcp_qbce_offset_of_neg_lit_in_watched_occ, offset);
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              assert (qbcp_qbce_find_watched_occ 
                      (qdpll, &var->qbcp_qbce_watched_pos_occ_clauses, old_witness) == 
                      var->qbcp_qbce_watched_pos_occ_clauses.start + offset);
              qbcp_qbce_delete_watched_occ_entry 
                (&var->qbcp_qbce_watched_pos_occ_clauses, 
                 &var->qbcp_qbce_offset_of_pos_lit_in_watched_occ, offset);
            } 
        }
      QDPLL_RESET_STACK (old_witness->qbcp_qbce_offset_of_witness_in_watched_occs);
    }
}

/* Store the pair <c,lit> in the notify-list of the clause 'witness'. If
   'witness' becomes blocked, then the clauses on its notify-list may be
   blocked. */
static void
qbcp_qbce_store_witness (QDPLL *qdpll, QBCENonBlockedWitness pair, 
                         Constraint *witness)
{
  Constraint *non_blocked_clause = pair.blit_occ.constraint;
  LitID non_blocking_lit = pair.non_blocking_lit;
  assert (QDPLL_VAR_EXISTS (LIT2VARPTR (qdpll->pcnf.vars, non_blocking_lit)));
  assert (constraint_has_lit (non_blocked_clause, non_blocking_lit));
  assert (constraint_has_lit (witness, -non_blocking_lit));
  assert (!non_blocked_clause->is_cube);
  assert (!non_blocked_clause->qbcp_qbce_blocked);
  assert (!is_clause_satisfied (qdpll, non_blocked_clause));
  assert (!witness->is_cube);
  assert (!witness->qbcp_qbce_blocked);
  assert (!is_clause_satisfied (qdpll, witness));

  /* Remove old witness of 'non_blocking_lit' from list of witnesses of
     'non_blocked_clause'. Every non-blocked clause has exactly one witness for
     every non-blocking literal. */
  QBCENonBlockedWitness *old_witness_pair_p = 
    pair.offset.witness_in_witness_list != QDPLL_INVALID_WATCHER_POS ? 
    non_blocked_clause->qbcp_qbce_witness_clauses.start + 
    pair.offset.witness_in_witness_list : 0;
  assert (old_witness_pair_p == qbcp_qbce_find_lit_in_list 
	  (qdpll, &(non_blocked_clause->qbcp_qbce_witness_clauses), non_blocking_lit));
  if (old_witness_pair_p)
    {
      /* We will always find an old witness, except during initialization. */
      QBCENonBlockedWitness old_witness_pair = *old_witness_pair_p;
      assert (old_witness_pair.non_blocking_lit);
      assert (old_witness_pair.blit_occ.constraint);

      if (witness == old_witness_pair.blit_occ.constraint)
        return;

      assert (old_witness_pair.non_blocking_lit == non_blocking_lit);
      /* Delete entry of old witness from witness list of 'non_blocked_clause'. */
      qbcp_qbce_delete_list_entry 
        (qdpll, &(non_blocked_clause->qbcp_qbce_witness_clauses), old_witness_pair_p, 1);
      assert (!qbcp_qbce_find_lit_in_list 
              (qdpll, &(non_blocked_clause->qbcp_qbce_witness_clauses), non_blocking_lit));
      /* Delete entry of 'non_blocked_clause' from notify-list of old witness. */
      QBCENonBlockedWitness *non_blocked_clause_entry_p = 
	old_witness_pair.offset.maybe_blocked_clause_in_notify_list != 
	QDPLL_INVALID_WATCHER_POS ? 
	old_witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start + 
	old_witness_pair.offset.maybe_blocked_clause_in_notify_list : 0;
      assert (non_blocked_clause_entry_p == qbcp_qbce_find_clause_in_list 
	      (qdpll, &(old_witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses), 
	       non_blocked_clause));
      assert (non_blocked_clause_entry_p);
      QBCENonBlockedWitness non_blocked_clause_entry = *non_blocked_clause_entry_p;
      assert (non_blocked_clause_entry.non_blocking_lit);
      assert (non_blocked_clause_entry.blit_occ.constraint);
      assert (non_blocked_clause_entry.non_blocking_lit == non_blocking_lit);
      assert (non_blocked_clause_entry.blit_occ.constraint == non_blocked_clause);
      qbcp_qbce_delete_list_entry 
        (qdpll, &(old_witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses), 
         non_blocked_clause_entry_p, 0);
      assert (!qbcp_qbce_find_clause_in_list 
              (qdpll, &(old_witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses), 
               non_blocked_clause));
      /* Remove 'old_witness_pair.clause' from lists of watched pos/neg occurrences
         IF AND ONLY IF it is no longer used as a witness. */
      qbcp_qbce_remove_watched_occ (qdpll, old_witness_pair.blit_occ.constraint);
    }

  /* Store 'witness' in list of watched pos/neg occurrences. This is necessary
     to trigger QBCE from clauses which are satisfied by new assignments. */
  qbcp_qbce_store_watched_occ (qdpll, witness);

  /* Store pair of witness and non-blocking literal in witness list of clause
     'non_blocked_clause', remove old entries first. */
  assert (witness->num_lits > 0);
  assert (witness->lits[0]);
  QBCENonBlockedWitness witness_pair = {non_blocking_lit, 
					{witness->lits[0], witness}, 
					{QDPLL_INVALID_WATCHER_POS}, 
                                        QDPLL_INVALID_WATCHER_POS};
  /* Store offset of maybe-blocked clause in list
     'witness->qbcp_qbce_notify_maybe_blocked_clauses' of clauses to
     be notified, where maybe-blocked clause is added to below in
     terms of 'pair'. */
  unsigned int offset_of_maybe_blocked_clause_in_notify_list = 
    QDPLL_COUNT_STACK (witness->qbcp_qbce_notify_maybe_blocked_clauses);
  witness_pair.offset.maybe_blocked_clause_in_notify_list = offset_of_maybe_blocked_clause_in_notify_list;

  /* Store 'non_blocking_clause' in notify list of 'witness'. */
  assert (!qbcp_qbce_find_pair_in_list 
          (qdpll, &(witness->qbcp_qbce_notify_maybe_blocked_clauses), pair, 0, 0));
  assert (!qbcp_qbce_find_clause_in_list 
          (qdpll, &(witness->qbcp_qbce_notify_maybe_blocked_clauses), non_blocked_clause));
  /* Store offset of witness clause in list
     'non_blocked_clause->qbcp_qbce_witness_clauses' of witness clauses, where
     witness clause is added to below in terms of 'witness_pair'. */
  unsigned int offset_of_witness_in_witness_list = 
    QDPLL_COUNT_STACK (non_blocked_clause->qbcp_qbce_witness_clauses);
  pair.offset.witness_in_witness_list = offset_of_witness_in_witness_list;
  QDPLL_PUSH_STACK 
    (qdpll->mm, witness->qbcp_qbce_notify_maybe_blocked_clauses, pair);
  /* Store 'witness' in witness list of 'non_blocking_clause'. */
  assert (!qbcp_qbce_find_pair_in_list 
          (qdpll, &(non_blocked_clause->qbcp_qbce_witness_clauses), witness_pair, 0, 0));
  assert (!qbcp_qbce_find_lit_in_list 
          (qdpll, &(non_blocked_clause->qbcp_qbce_witness_clauses), non_blocking_lit));
  QDPLL_PUSH_STACK 
    (qdpll->mm, non_blocked_clause->qbcp_qbce_witness_clauses, witness_pair);
  assert (QDPLL_COUNT_STACK (non_blocked_clause->qbcp_qbce_witness_clauses) <= 
          non_blocked_clause->num_lits);

  assert (witness_pair.offset.maybe_blocked_clause_in_notify_list < QDPLL_COUNT_STACK (witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses));
  assert (witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start[witness_pair.offset.maybe_blocked_clause_in_notify_list].blit_occ.constraint == non_blocked_clause);
  assert (pair.offset.witness_in_witness_list < QDPLL_COUNT_STACK (pair.blit_occ.constraint->qbcp_qbce_witness_clauses));
  assert (pair.blit_occ.constraint->qbcp_qbce_witness_clauses.start[pair.offset.witness_in_witness_list].blit_occ.constraint == witness);

  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "WATCHING: stored pairs for non-blocking lit %d and non-blocked clause ", non_blocking_lit);
      print_constraint (qdpll, non_blocked_clause);
      fprintf (stderr, "WATCHING:  witness clause ");
      print_constraint (qdpll, witness);
      fprintf (stderr, "WATCHING:  witness pair.mo = %d\n", witness_pair.offset.maybe_blocked_clause_in_notify_list);
      fprintf (stderr, "WATCHING:  maybe-blocked pair.wo = %d\n", pair.offset.witness_in_witness_list);
    }
}

/* Return zero if the clause 'c' is blocked with the blocking literal 'lit' in
   'c'. Otherwise, return a pointer to a clause which is a witness that 'c' is
   NOT blocked on the literal 'lit'. That is, resolving that clause and 'c' on
   the pivot 'lit' does NOT result in a tautology over a variable from a block
   smaller than the block of 'lit'. */
static Constraint *
qbcp_qbce_find_non_blocking_literal_witness (QDPLL *qdpll, LitID lit, Constraint *c)
{
  Constraint *witness = 0;
  assert (constraint_has_lit (c, lit));
  assert (!c->is_cube);
  assert (!c->qbcp_qbce_blocked);
  assert (!is_clause_satisfied (qdpll, c));
  Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
  assert (!QDPLL_VAR_ASSIGNED (var));
  /* Only existential literals can be blocking literals. */
  assert (QDPLL_SCOPE_EXISTS (var->scope));
  const Nesting nesting = var->scope->nesting;
  BLitsOccStack *occs = QDPLL_LIT_NEG(lit) ? &var->pos_occ_clauses : &var->neg_occ_clauses; 

  /* Traverse clauses containing '-lit' and check if resolving 'c' with any of
     these clauses would result in a tautology over a variable from a block
     smaller than or equal to the block of 'lit'. */
  BLitsOcc *bop, *boe;
  for (bop = occs->start, boe = occs->top; !witness && bop < boe; bop++)
    {
      assert (!BLIT_MARKED_PTR(bop->constraint));
      assert (!bop->constraint->is_cube);
      assert (constraint_has_lit (bop->constraint, -lit));
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_clauses_seen++;
      qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses++;
#endif

      /* Check if potential witness is satisfied by cached literal. The cached
         literals are stored on the occurrence lists and are updated during
         literal and pure watcher updates. */
      Constraint *o = check_disabling_blocking_lit (qdpll, *bop, 0);
      if (!o)
        {
#if COMPUTE_STATS
          qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_hits++;
#endif
          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "    skipping already satisfied potential witness of literal %d: ", lit);
              print_constraint (qdpll, bop->constraint);
            }
          continue;
        }
      else
        {
          if (o->qbcp_qbce_blocked)
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_blocked++;
#endif
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "    skipping already blocked potential witness of literal %d: ", lit);
                  print_constraint (qdpll, o);
                }
              continue;
            }
          LitID satisfying_lit;
          if ((satisfying_lit = is_constraint_empty_watcher (qdpll, o)))
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_sat++;
#endif
              update_blocking_literal (qdpll, qdpll->pcnf.vars, bop,
                                       o, satisfying_lit, 
                                       LIT2VARPTR (qdpll->pcnf.vars, satisfying_lit),
                                       o->is_cube);
              assert (bop->blit == satisfying_lit);             
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "    skipping already satisfied potential witness of literal %d: ", lit);
                  print_constraint (qdpll, o);
                }
              continue;
            }              
        }

      if (qdpll->options.verbosity >= 3)
        {
          fprintf (stderr, "    checking potential non-blocking witness of literal %d: ", lit);
          print_constraint (qdpll, o);
        }

      LitID *p, *e;
      for (p = o->lits, e = p + o->num_lits; p < e; p++)
        {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_literals_seen++;
#endif
          LitID olit = *p;
          Var *ovar = LIT2VARPTR(qdpll->pcnf.vars, olit);
          /* Ignore assigned variables. These assignment can never satisfy
             the clause, because satisfied clauses are ignored. */
          assert (!QDPLL_VAR_ASSIGNED (ovar) || 
                  (QDPLL_LIT_NEG (olit) && QDPLL_VAR_ASSIGNED_TRUE (ovar)) || 
                  (QDPLL_LIT_POS (olit) && QDPLL_VAR_ASSIGNED_FALSE (ovar)));
          if (QDPLL_VAR_ASSIGNED (ovar))
            continue;
          if (ovar->scope->nesting > nesting)
            {
              witness = o;
              break;
            }
          /* Check if resolving 'c' and 'o' would result in a tautology over a
             variable from a block smaller than or equal to the block of
             'lit'. */
          if (ovar != var && 
              ((QDPLL_LIT_NEG(olit) && QDPLL_VAR_POS_MARKED (ovar)) || 
              (QDPLL_LIT_POS(olit) && QDPLL_VAR_NEG_MARKED (ovar))))
            break;
        }
      if (p == e)
        witness = o;

      /* Move witness to second position of list so that it is found faster
         next time (may occur also when checking other clauses). We cannot
         move it to the first position because the first clause on the list is
         watched for pure literal detection. */
      if (qdpll->options.qbcp_qbce_watcher_list_mtf && 
          witness && QDPLL_SIZE_STACK (*occs) >= 2 && bop != occs->start)
        {
          BLitsOcc tmp = occs->start[1];
          occs->start[1] = *bop;
          *bop = tmp;
        }
    }

  return witness;
}

/* If 'var' is assigned, then potentially new clauses may be blocked. This way
   of pushing potentially blocked clauses is done only if we do not have
   watched data structures. */
static void
qbcp_qbce_push_maybe_blocked_clauses_by_assignment (QDPLL *qdpll, Var *assigned_var)
{
  assert (qdpll->options.qbce_inprocessing || !qdpll->options.no_qbce_dynamic);
  assert (!qdpll->options.qbce_inprocessing || qdpll->options.no_qbce_dynamic);
  /* When using QBCE as inprocessing, then this function must be called at the
     top-level only. */
  assert (!qdpll->options.qbce_inprocessing || qdpll->state.decision_level == 0);
  assert (QDPLL_VAR_ASSIGNED (assigned_var));
  assert (!qdpll->options.qbce_inprocessing || assigned_var->decision_level == 0);

  if (qdpll->options.verbosity >= 3)
    fprintf (stderr, "pushing clauses based on assigned var %d to be checked in QBCE\n", 
             assigned_var->id);

  /* Check all clauses which are witnesses and satisfied by the current
     assignment. Push all clauses having their witnesses satisfied to be
     checked again for QBCE. */
  ConstraintPtrStack *occs = QDPLL_VAR_ASSIGNED_TRUE (assigned_var) ? 
    &(assigned_var->qbcp_qbce_watched_pos_occ_clauses) : 
    &(assigned_var->qbcp_qbce_watched_neg_occ_clauses);

  Constraint **p, **e;
  for (p = occs->start, e = occs->top; p < e; p++)
    {
      Constraint *c = *p;

      if (qdpll->options.verbosity >= 3)
        {
          fprintf (stderr, "var %d has %s watched occ: ", assigned_var->id, 
                   c->qbcp_qbce_mark ? "marked" : "unmarked");
          print_constraint (qdpll, c);
          fprintf (stderr, "...which has notify-list length of %d\n", 
                   (unsigned int) QDPLL_COUNT_STACK (c->qbcp_qbce_notify_maybe_blocked_clauses));
        }

      /* We may see an occurrence multiple times if it is satsified by several
         literals. Must avoid pushing maybe-blocked clauses multiple times. */
      if (c->qbcp_qbce_mark)
        continue;
      c->qbcp_qbce_mark = 1;

      /* Collect clauses marked at each decision level, which will be unmarked
         during backtracking. */
      assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 
              qdpll->state.decision_level + 1);
      QDPLL_PUSH_STACK 
        (qdpll->mm, qdpll->qbcp_qbce_marked_clauses.start[qdpll->state.decision_level], c);

      /* Clause 'c' is now satisfied. Push all clauses for which 'c' is a
         witness. */
      QBCENonBlockedWitness *qp, *qe;
      for (qp = c->qbcp_qbce_notify_maybe_blocked_clauses.start, 
             qe = c->qbcp_qbce_notify_maybe_blocked_clauses.top; qp < qe; qp++)
        {
          QBCENonBlockedWitness maybe_blocked_pair = *qp;
          Constraint *maybe_blocked_clause = 
            check_disabling_blocking_lit (qdpll, maybe_blocked_pair.blit_occ, 0);
          /* Check if clause is satisfied by cached literal. */
          if (!maybe_blocked_clause)
            continue;
          else
            {
              if (QDPLL_VAR_ASSIGNED 
                  (LIT2VARPTR (qdpll->pcnf.vars, 
                               maybe_blocked_pair.non_blocking_lit)) || 
                  maybe_blocked_clause->qbcp_qbce_blocked)
                continue;
              LitID satisfying_lit;
            }

          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "  pushing potential blocking literal %d and clause:", 
                       maybe_blocked_pair.non_blocking_lit);
              print_constraint (qdpll, maybe_blocked_pair.blit_occ.constraint);
            }
          /* Set offset-on-working-queue of pair to be enqueued. */
          assert (qp->offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
          assert (maybe_blocked_pair.offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
          qp->offset_in_working_queue = maybe_blocked_pair.offset_in_working_queue = 
            QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
          QDPLL_PUSH_STACK(qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, 
                           maybe_blocked_pair);
        }
    }
}

static void
assert_qbcp_qbce_check_clause_is_blocked (QDPLL *qdpll, Constraint *blocked_clause)
{
  assert (blocked_clause->qbcp_qbce_blocked);
  assert (blocked_clause->qbcp_qbce_blocking_lit);
  LitID blocking_lit = blocked_clause->qbcp_qbce_blocking_lit;
  assert (constraint_has_lit (blocked_clause, blocking_lit));
  Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);
  BLitsOccStack *occs = QDPLL_LIT_NEG (blocking_lit) ? 
    &(blocking_var->pos_occ_clauses) : &(blocking_var->neg_occ_clauses);
  BLitsOcc *p, *e;
  for (p = occs->start, e = occs->top; p < e; p++)
    {
      Constraint *occ = p->constraint;
      if (occ->qbcp_qbce_blocked || is_clause_satisfied (qdpll, occ))
        continue;
      assert (constraint_has_lit (occ, -blocking_lit));
      unsigned int is_taut = 0;
      LitID *litp, *lite;
      for (litp = blocked_clause->lits, 
             lite = litp + blocked_clause->num_lits; !is_taut && litp < lite; litp++)
        {
          LitID lit = *litp;
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          if (lit != blocking_lit && 
              var->scope->nesting <= blocking_var->scope->nesting && 
              constraint_has_lit (occ, -lit))
            is_taut = 1;
        }
      assert (is_taut);
    }
}

static int
qbcp_qbce_find_in_blocked_clauses (ConstraintPtrStack *stack, Constraint *c)
{
  Constraint **p, **e;
  for (p = stack->start, e = stack->top; p < e; p++)
    if (*p == c)
      return 1;
  return 0;
}

static void
assert_qbcp_qbce_blocked_clauses_integrity (QDPLL *qdpll)
{
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) >= 1);
  ConstraintPtrStack *sp, *se;
  for (sp = qdpll->qbcp_qbce_blocked_clauses.start, 
         se = qdpll->qbcp_qbce_blocked_clauses.top; sp < se; sp++)
    {
      ConstraintPtrStack stack = *sp;
      Constraint **p, **e;
      for (p = stack.start, e = stack.top; p < e; p++)
        {
          Constraint *blocked_clause = *p;
          assert (blocked_clause->qbcp_qbce_blocked);
          assert (blocked_clause->qbcp_qbce_blocking_lit);
          assert_qbcp_qbce_check_clause_is_blocked (qdpll, blocked_clause);
          Var *blocking_var = LIT2VARPTR 
            (qdpll->pcnf.vars, blocked_clause->qbcp_qbce_blocking_lit);
          if (sp == qdpll->qbcp_qbce_blocked_clauses.start)
            {
              /* Clause blocked by preprocessing must appear on occurrence
                 lists of blocked clauses. */
              if (QDPLL_LIT_NEG (blocked_clause->qbcp_qbce_blocking_lit))
                assert (qbcp_qbce_find_in_blocked_clauses 
                        (&blocking_var->qbcp_qbce_prepro_neg_blocking_lit_clauses, blocked_clause));
              else
                assert (qbcp_qbce_find_in_blocked_clauses
                        (&blocking_var->qbcp_qbce_prepro_pos_blocking_lit_clauses, blocked_clause));
            }
        }
    }

  /* Clauses on occ-lists of clauses blocked by preprocessing must appear on
     stack of blocked clauses. */
  Var *vp, *ve;
  for (vp = qdpll->pcnf.vars, ve = vp + qdpll->pcnf.size_vars; vp < ve; vp++)
    {
      if (vp->id)
        {
          Constraint **p, **e;
          for (p = vp->qbcp_qbce_prepro_neg_blocking_lit_clauses.start, 
                 e = vp->qbcp_qbce_prepro_neg_blocking_lit_clauses.top; p < e; p++)
            {
              Constraint *c = *p;
              assert (c->qbcp_qbce_blocked);
              assert (c->qbcp_qbce_blocking_lit);
              assert (qbcp_qbce_find_in_blocked_clauses 
                      (&(qdpll->qbcp_qbce_blocked_clauses.start[0]), c));
            }
          for (p = vp->qbcp_qbce_prepro_pos_blocking_lit_clauses.start, 
                 e = vp->qbcp_qbce_prepro_pos_blocking_lit_clauses.top; p < e; p++)
            {
              Constraint *c = *p;
              assert (c->qbcp_qbce_blocked);
              assert (c->qbcp_qbce_blocking_lit);
              assert (qbcp_qbce_find_in_blocked_clauses 
                      (&(qdpll->qbcp_qbce_blocked_clauses.start[0]), c));
            }
        }
    }
}

static void
assert_qbcp_qbce_witness_resolvent_no_taut 
(QDPLL *qdpll, Constraint *c, LitID non_blocking_lit, Constraint * witness)
{
  assert (constraint_has_lit (c, non_blocking_lit));
  assert (constraint_has_lit (witness, -non_blocking_lit));
  assert (!witness->qbcp_qbce_blocked);
  Var *non_blocking_var = LIT2VARPTR (qdpll->pcnf.vars, 
                                      non_blocking_lit);
  assert (!is_clause_satisfied (qdpll, witness) || 
          ((QDPLL_VAR_ASSIGNED_TRUE (non_blocking_var) && QDPLL_LIT_POS (-non_blocking_lit)) || 
           (QDPLL_VAR_ASSIGNED_FALSE (non_blocking_var) && QDPLL_LIT_NEG (-non_blocking_lit))));
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Resolvent must not be tautological with respect to a variable from a
         block smaller or equal than 'non_blocking_var'. */
      if (lit != non_blocking_lit && 
          var->scope->nesting <= non_blocking_var->scope->nesting)
        assert (!constraint_has_lit (witness, -lit));
    }
}

static void
assert_qbcp_qbce_non_blocked_witness_integrity (QDPLL *qdpll)
{
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      if (c->qbcp_qbce_blocked || is_clause_satisfied (qdpll, c))
        {
        }
      else
        {
          if (qdpll->options.qbcp_qbce_max_clause_size && 
              c->num_lits > qdpll->options.qbcp_qbce_max_clause_size)
            continue;

          /* Check that 'c' has a witness for every existential literal. */
          unsigned int cnt_exists_lits = 0;
          LitID *lp, *le;
          for (lp = c->lits, le = lp + c->num_lits; lp < le; lp++)
            {
              LitID lit = *lp;
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              if (qdpll->options.qbcp_qbce_find_witness_max_occs)
                {
                  BLitsOccStack *occs = QDPLL_LIT_NEG (lit) ? 
                    &var->pos_occ_clauses : &var->neg_occ_clauses;
                  if (QDPLL_COUNT_STACK (*occs) > 
                      qdpll->options.qbcp_qbce_find_witness_max_occs)
                    continue;
                }
              if (qdpll->options.qbcp_qbce_max_clause_size)
                {
                  if ((QDPLL_LIT_NEG (lit) && var->longest_pos_occ_size > 
                       qdpll->options.qbcp_qbce_max_clause_size) || 
                      (QDPLL_LIT_POS (lit) && var->longest_neg_occ_size > 
                       qdpll->options.qbcp_qbce_max_clause_size))
                    continue;
                }
              if (QDPLL_VAR_EXISTS (var) && !var->is_internal)
                {
                  /* An existential literal perhaps does not have a witness if
                     that existential was assigned as a user-given
                     assumption. Without assumptions, QBCE is run as
                     preprocessing before any assignments are made and hence
                     every existential literal will have a witness. */
                  if (!(QDPLL_VAR_ASSIGNED (var) && var->mode == QDPLL_VARMODE_ASSUMED))
                    {
                      cnt_exists_lits++;
                      assert (qbcp_qbce_find_lit_in_list 
                              (qdpll, &(c->qbcp_qbce_witness_clauses), lit));
                    }
                }
            }
          assert (QDPLL_COUNT_STACK (c->qbcp_qbce_witness_clauses) == 
                  cnt_exists_lits);
          QBCENonBlockedWitness *p, *e;
          /* Check clauses which are witnesses that this clause 'c' is not
             blocked. */
          for (p = c->qbcp_qbce_witness_clauses.start, 
                 e = c->qbcp_qbce_witness_clauses.top; p < e; p++)
            {
              QBCENonBlockedWitness witness_pair = *p;
              assert (witness_pair.offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
              assert (witness_pair.non_blocking_lit);
              assert (witness_pair.blit_occ.constraint);
              assert (!witness_pair.blit_occ.constraint->qbcp_qbce_blocked);
              assert_qbcp_qbce_witness_resolvent_no_taut 
                (qdpll, c, witness_pair.non_blocking_lit, witness_pair.blit_occ.constraint);

              Var *non_blocking_var = 
                LIT2VARPTR (qdpll->pcnf.vars, witness_pair.non_blocking_lit);
              assert (!QDPLL_VAR_ASSIGNED (non_blocking_var) || 
                      is_clause_satisfied (qdpll, witness_pair.blit_occ.constraint));
              assert (QDPLL_VAR_EXISTS (non_blocking_var));
              /* Witness may be satisfied only if it is satisfied by the
                 blocking literal of the witness. In this case, the blocking
                 literal is falsified in 'c'. The clause 'c' does not need
                 another witness for that literal since it has in fact
                 disappeared from 'c'. */
              assert (!is_clause_satisfied (qdpll, witness_pair.blit_occ.constraint) || 
                      (QDPLL_VAR_ASSIGNED_TRUE (non_blocking_var) && 
                       QDPLL_LIT_POS (-witness_pair.non_blocking_lit)) || 
                      (QDPLL_VAR_ASSIGNED_FALSE (non_blocking_var) && 
                       QDPLL_LIT_NEG (-witness_pair.non_blocking_lit)));
              assert (constraint_has_lit (witness_pair.blit_occ.constraint, 
                                          -witness_pair.non_blocking_lit));
              assert (constraint_has_lit (c, witness_pair.non_blocking_lit));

              /* We must not find this entry a second time in this list. Even
                 more, there must not be multiple entries having the same clause
                 or same non-blocking literal. */
              QBCENonBlockedWitness *check_p;
              for (check_p = p + 1; check_p < e; check_p++)
                {
                  QBCENonBlockedWitness check_pair = *check_p;
                  assert (check_pair.blit_occ.constraint != witness_pair.blit_occ.constraint);
                  assert (check_pair.non_blocking_lit != witness_pair.non_blocking_lit);
                }
              assert (c->num_lits > 0);
              assert (c->lits[0]);
              QBCENonBlockedWitness check_pair = {witness_pair.non_blocking_lit, {c->lits[0], c}, 
                                                  {QDPLL_INVALID_WATCHER_POS}, QDPLL_INVALID_WATCHER_POS};
              qbcp_qbce_find_pair_in_list 
                (qdpll, &(witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses), 
                 check_pair, 0, 0);
              /* Check offset stored in 'witness_pair'. */
              assert (witness_pair.offset.maybe_blocked_clause_in_notify_list < 
                      QDPLL_COUNT_STACK (witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses));
              assert (witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start
                      [witness_pair.offset.maybe_blocked_clause_in_notify_list].blit_occ.constraint == c);
              assert (witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start
                      [witness_pair.offset.maybe_blocked_clause_in_notify_list].offset.witness_in_witness_list == 
                      (unsigned int)(p - c->qbcp_qbce_witness_clauses.start));
            }
          /* Check clauses for which this clause 'c' is a witness. */
          for (p = c->qbcp_qbce_notify_maybe_blocked_clauses.start, 
                 e = c->qbcp_qbce_notify_maybe_blocked_clauses.top; p < e; p++)
            {
              QBCENonBlockedWitness maybe_blocked_pair = *p;
              assert (maybe_blocked_pair.offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
              assert (maybe_blocked_pair.non_blocking_lit);
              assert (maybe_blocked_pair.blit_occ.constraint);
              assert (constraint_has_lit (maybe_blocked_pair.blit_occ.constraint, 
                                          maybe_blocked_pair.non_blocking_lit));
              assert (constraint_has_lit (c, -maybe_blocked_pair.non_blocking_lit));
              /* We must not find this entry a second time in this
                 list. However, this clause may notify different clauses to be
                 checked again for the same blocking literal. */
              QBCENonBlockedWitness *check_p;
              for (check_p = p + 1; check_p < e; check_p++)
                {
                  QBCENonBlockedWitness check_pair = *check_p;
                  assert (check_pair.blit_occ.constraint != maybe_blocked_pair.blit_occ.constraint);
                }
              assert (c->num_lits > 0);
              assert (c->lits[0]);
              QBCENonBlockedWitness check_pair = {maybe_blocked_pair.non_blocking_lit, {c->lits[0], c}, 
                                                  {QDPLL_INVALID_WATCHER_POS}, QDPLL_INVALID_WATCHER_POS};
              assert (qbcp_qbce_find_pair_in_list 
                (qdpll, &(maybe_blocked_pair.blit_occ.constraint->qbcp_qbce_witness_clauses), 
                 check_pair, 0, 0));
              /* Check offset stored in 'maybe_blocked_pair'. */
              assert (maybe_blocked_pair.offset.witness_in_witness_list < 
                      QDPLL_COUNT_STACK (maybe_blocked_pair.blit_occ.constraint->qbcp_qbce_witness_clauses));
              assert (maybe_blocked_pair.blit_occ.constraint->qbcp_qbce_witness_clauses.start
                      [maybe_blocked_pair.offset.witness_in_witness_list].blit_occ.constraint == c);
              assert (maybe_blocked_pair.blit_occ.constraint->qbcp_qbce_witness_clauses.start
                      [maybe_blocked_pair.offset.witness_in_witness_list].offset.maybe_blocked_clause_in_notify_list == 
                      (unsigned int)(p - c->qbcp_qbce_notify_maybe_blocked_clauses.start));
            }
        }
    }
}

/* Add 'blocked_clause' to occurrence list
   'var->qbcp_qbce_prepro_neg/pos_blocking_lit_clauses' of variable of the
   blocking literal. This information is necessary to check whether blocked
   clauses may become non-blocked if the user adds new input clauses. */
static void
qbcp_qbce_prepro_add_blocking_lit_occ (QDPLL *qdpll, Constraint *blocked_clause)
{
  assert (qdpll->state.qbcp_qbce_currently_preprocessing);
  assert (blocked_clause->qbcp_qbce_blocked);
  assert (blocked_clause->qbcp_qbce_blocking_lit);
  LitID blocking_lit = blocked_clause->qbcp_qbce_blocking_lit;
  Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);
  if (QDPLL_LIT_NEG (blocking_lit))
    {
      QDPLL_PUSH_STACK (qdpll->mm, blocking_var->
                        qbcp_qbce_prepro_neg_blocking_lit_clauses, 
                        blocked_clause);
    }
  else
    {
      assert (QDPLL_LIT_POS (blocking_lit));
      QDPLL_PUSH_STACK (qdpll->mm, blocking_var->
                        qbcp_qbce_prepro_pos_blocking_lit_clauses, 
                        blocked_clause);
    }
}

/* Returns non-zero if and only if new blocked clauses have been found. */
static unsigned int
qbcp_qbce_find_blocked_clauses (QDPLL *qdpll)
{
#ifndef NDEBUG
  Var *dp, *de;
  for (dp = qdpll->pcnf.vars, de = dp + qdpll->pcnf.size_vars; dp < de; dp++)
    {
      assert (!QDPLL_VAR_MARKED(dp));
    }
#endif

  assert (qdpll->options.qbce_preprocessing || qdpll->options.qbce_inprocessing || 
          !qdpll->options.no_qbce_dynamic); 
  assert ((!qdpll->options.qbce_preprocessing && !qdpll->options.qbce_inprocessing) || 
          qdpll->state.decision_level == 0);

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "Start of QBCE call\n");

  unsigned int found_new_blocked_clauses = 0; 

  /* Stack of clauses found blocked in the current round. */
  ConstraintPtrStack blocked_clauses;
  QDPLL_INIT_STACK (blocked_clauses);
  /* Stack of literals of a given clause which maybe blocking and hence are
     inspected. This stack is relevant only to handle the very first call of this
     function and all fortcoming incremental calls in a unifrom way. */
  LitIDStack maybe_blocking_literals;
  QDPLL_INIT_STACK (maybe_blocking_literals);
  /* Stack of signed variable IDs which must be checked for update of their
     clause watcher, which was found blocked. */
  LitIDStack maybe_pure_literals;
  QDPLL_INIT_STACK (maybe_pure_literals);

  do 
    {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_rounds++;
      if (qdpll->state.decision_level == 0 && 
          !qdpll->state.qbcp_qbce_currently_preprocessing)
        qdpll->stats.qbcp_qbce_inprocessing_rounds++;
#endif

      if (qdpll->options.verbosity >= 2)
        {
          fprintf (stderr, "New round of QBCE, %d potentially blocked clauses to be checked.\n", 
                   (unsigned int) QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses));
#if COMPUTE_STATS
          fprintf (stderr, "QBCE completed rounds: %llu\n", qdpll->stats.qbcp_qbce_rounds);
          fprintf (stderr, "QBCE blocked clauses: %llu ( %f of CNF size, including satisfied ones)\n", (long long unsigned int)qdpll->stats.qbcp_qbce_current_blocked_clauses, (long long unsigned int)qdpll->stats.qbcp_qbce_current_blocked_clauses ? ((long long unsigned int)qdpll->stats.qbcp_qbce_current_blocked_clauses / (float)qdpll->pcnf.clauses.cnt) : 0);
          fprintf (stderr, "QBCE clauses seen: %llu ( %f of CNF size)\n", qdpll->stats.qbcp_qbce_clauses_seen, qdpll->stats.qbcp_qbce_clauses_seen ? (qdpll->stats.qbcp_qbce_clauses_seen / (float)qdpll->pcnf.clauses.cnt) : 0);
          fprintf (stderr, "QBCE literals seen: %llu\n", qdpll->stats.qbcp_qbce_literals_seen);
          fprintf (stderr, "QBCE seen literals per clause: %f\n", qdpll->stats.qbcp_qbce_clauses_seen ? (qdpll->stats.qbcp_qbce_literals_seen / (float)qdpll->stats.qbcp_qbce_clauses_seen) : 0);
          fprintf (stderr, "QBCE find-entry calls: %llu\n", qdpll->stats.qbcp_qbce_find_entry_calls);
          fprintf (stderr, "QBCE find entries seen: %llu ( %f per call)\n", qdpll->stats.qbcp_qbce_find_entries_seen, qdpll->stats.qbcp_qbce_find_entry_calls ? (qdpll->stats.qbcp_qbce_find_entries_seen / (float)qdpll->stats.qbcp_qbce_find_entry_calls) : 0);
#endif      
        }
      QDPLL_RESET_STACK (blocked_clauses);
      assert (QDPLL_EMPTY_STACK (maybe_blocking_literals));

      while (!QDPLL_EMPTY_STACK(qdpll->qbcp_qbce_maybe_blocked_clauses))
        {
          QBCENonBlockedWitness pair = 
            QDPLL_POP_STACK(qdpll->qbcp_qbce_maybe_blocked_clauses);
          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "De-queued pair with lit %d, wo-value %d and clause: ", 
                       pair.non_blocking_lit, pair.offset.witness_in_witness_list);
              print_constraint (qdpll, pair.blit_occ.constraint);
            }
#ifndef NDEBUG
          do {
            /* Must not push the same pair to be checked again multiple
               time. This cannot happen by construction. */
            QBCENonBlockedWitness *check_p, *check_e;
            for (check_p = qdpll->qbcp_qbce_maybe_blocked_clauses.start, 
                   check_e = qdpll->qbcp_qbce_maybe_blocked_clauses.top; 
                 check_p < check_e; check_p++)
              {
                QBCENonBlockedWitness check_pair = *check_p;
                assert (check_pair.blit_occ.constraint != pair.blit_occ.constraint || 
                        check_pair.non_blocking_lit != pair.non_blocking_lit);
              }
          } while (0);
#endif
          if (pair.offset.witness_in_witness_list != QDPLL_INVALID_WATCHER_POS)
            qbcp_qbce_reset_offset_in_working_queue (qdpll, pair);
          LitID non_blocking_lit = pair.non_blocking_lit;
          assert (!non_blocking_lit || constraint_has_lit (pair.blit_occ.constraint, 
                                                           non_blocking_lit));
          assert (non_blocking_lit || 
                  pair.offset.witness_in_witness_list == QDPLL_INVALID_WATCHER_POS);
          assert (!pair.blit_occ.blit || constraint_has_lit (pair.blit_occ.constraint, 
                                                             pair.blit_occ.blit));
#if COMPUTE_STATS
          qdpll->stats.qbcp_qbce_clauses_seen++;
#endif
          if (non_blocking_lit)
            {
              Var *non_blocking_var = LIT2VARPTR (qdpll->pcnf.vars, non_blocking_lit);
              /* Selector variables must not be used as blocking literals. */
              assert (!non_blocking_var->is_internal);
              if (QDPLL_VAR_ASSIGNED (non_blocking_var))
                {
                  /* This case may happen in dynamic QBCE when we push a
                     clause to be checked but later assign a variable
                     (i.e. the one of the blocking literal) at top-level. */
                  if (qdpll->options.verbosity >= 3)
                    {
                      fprintf (stderr, "Skipping assigned blocking literal %d in clause: ", 
                               non_blocking_lit);
                      print_constraint (qdpll, pair.blit_occ.constraint);
                    }
                  continue;
                }
            }

#if COMPUTE_STATS
          qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses++;
#endif
          /* Check if clause is satisfied by cached literal. */
          Constraint *c = pair.blit_occ.blit ? check_disabling_blocking_lit 
            (qdpll, pair.blit_occ, 0) : pair.blit_occ.constraint;
          if (!c)
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_is_clause_sat_cache_hits++;
#endif
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "Skipping already satisfied clause: ");
                  print_constraint (qdpll, pair.blit_occ.constraint);
                  fprintf (stderr, " and potential blocking literal %d\n", non_blocking_lit);
                }
              continue;
            }
          else
            {
              if (c->qbcp_qbce_blocked)
                {
#if COMPUTE_STATS
                  qdpll->stats.qbcp_qbce_is_clause_sat_found_blocked++;
#endif
                  if (qdpll->options.verbosity >= 3)
                    {
                      fprintf (stderr, "Skipping already blocked clause: ");
                      print_constraint (qdpll, c);
                      fprintf (stderr, " and potential blocking literal %d\n", non_blocking_lit);
                    }
                  continue;
                }
            }

          /* Mark pos/neg literals in 'c' by pos/neg marks. At the same time,
             check if clause is satisfied. Interleaved marking of variables and
             sat-check is faster on clauses which are not satisfied. There, we
             save the full traversal over the clause's literals done by
             'is-clause-satisfied'. It seems that the vast majority of clauses
             seen here are NOT satisfied after the blit-cache check. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_literals_seen++;
#endif
              LitID clit = *p;
              Var *cvar = LIT2VARPTR (qdpll->pcnf.vars, clit);
              /* Ignore literals currently assigned false. */
              if ((QDPLL_LIT_NEG (clit) && QDPLL_VAR_ASSIGNED_TRUE (cvar)) || 
                  (QDPLL_LIT_POS (clit) && QDPLL_VAR_ASSIGNED_FALSE (cvar)))
                continue;
              else if ((QDPLL_LIT_NEG (clit) && QDPLL_VAR_ASSIGNED_FALSE (cvar)) || 
                       (QDPLL_LIT_POS (clit) && QDPLL_VAR_ASSIGNED_TRUE (cvar)))
                {
                  /* Found satisfying literal. */
#if COMPUTE_STATS
                  qdpll->stats.qbcp_qbce_is_clause_sat_found_sat++;
#endif
                  update_blocking_literal (qdpll, qdpll->pcnf.vars, &(pair.blit_occ),
                                           c, clit, 
                                           LIT2VARPTR (qdpll->pcnf.vars, clit),
                                           c->is_cube);
                  assert (pair.blit_occ.blit == clit);
                  /* Update blocking literal in maybe-blocked-pair on
                     notify-list. This is necessary because otherwise caching
                     does not work as it is never updated! */
                  unsigned int witness_offset = pair.offset.witness_in_witness_list;
                  if (witness_offset != QDPLL_INVALID_WATCHER_POS)
                    {
                      assert (witness_offset < QDPLL_COUNT_STACK (c->qbcp_qbce_witness_clauses));
                      QBCENonBlockedWitness witness_pair = 
                        c->qbcp_qbce_witness_clauses.start[witness_offset];
                      unsigned int maybe_blocked_pair_offset = 
                        witness_pair.offset.maybe_blocked_clause_in_notify_list;
                      assert (maybe_blocked_pair_offset < QDPLL_COUNT_STACK 
                              (witness_pair.blit_occ.constraint->
                               qbcp_qbce_notify_maybe_blocked_clauses));
                      QBCENonBlockedWitness *maybe_blocked_pair_p = 
                        witness_pair.blit_occ.constraint->
                        qbcp_qbce_notify_maybe_blocked_clauses.start + 
                        maybe_blocked_pair_offset;
                      assert (c == maybe_blocked_pair_p->blit_occ.constraint);
                      assert (non_blocking_lit == maybe_blocked_pair_p->non_blocking_lit);
                      maybe_blocked_pair_p->blit_occ.blit = pair.blit_occ.blit;
                    }
                  break;         
                }
              assert (!QDPLL_VAR_MARKED(cvar));
              if (QDPLL_LIT_NEG (clit))
                QDPLL_VAR_NEG_MARK (cvar);
              else
                QDPLL_VAR_POS_MARK (cvar);
            }
          assert (e == c->lits + c->num_lits);
          assert (p >= c->lits && p <= e);
          if (p != e)
            {
              /* Clause 'c' is satisfied and will be ignored. Unmark the
                 variables which have been marked already in the above loop. */
              for (p--, e = c->lits; e <= p; p--)
                {
                  LitID clit = *p;
                  Var *cvar = LIT2VARPTR (qdpll->pcnf.vars, clit);
                  if ((QDPLL_LIT_NEG (clit) && QDPLL_VAR_ASSIGNED_TRUE (cvar)) || 
                      (QDPLL_LIT_POS (clit) && QDPLL_VAR_ASSIGNED_FALSE (cvar)))
                    {
                      assert (!QDPLL_VAR_MARKED (cvar));
                      continue;
                    }
                  assert (QDPLL_VAR_MARKED (cvar));
                  QDPLL_VAR_UNMARK (cvar);
                }
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "Skipping already satisfied clause: ");
                  print_constraint (qdpll, c);
                  fprintf (stderr, " and potential blocking literal %d\n", non_blocking_lit);
                }
              continue;
            }

          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "Checking clause: ");
              print_constraint (qdpll, c);
              fprintf (stderr, " and %s potential blocking literal (%d)\n", 
                       non_blocking_lit ? "single" : "all", non_blocking_lit);
            }

          assert (QDPLL_EMPTY_STACK (maybe_blocking_literals));
          if (!non_blocking_lit)
            {
              /* Collect all existential literals in the current clause to be
                 checked. This is relevant only if we call this function for
                 the first time after initialization. */
              LitID *p, *e;
              for (p = c->lits, e = p + c->num_lits; p < e; p++)
                {
#if COMPUTE_STATS
                  qdpll->stats.qbcp_qbce_literals_seen++;
#endif
                  LitID lit = *p;
                  Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
                  /* Pushed clauses must not be satisfied. */
                  assert (!QDPLL_VAR_ASSIGNED (var) || 
                          (QDPLL_VAR_ASSIGNED_TRUE (var) && QDPLL_LIT_NEG (lit)) || 
                          (QDPLL_VAR_ASSIGNED_FALSE (var) && QDPLL_LIT_POS (lit)));
                  if (QDPLL_VAR_ASSIGNED (var))
                    continue;
                  if (QDPLL_SCOPE_EXISTS (var->scope) && !var->is_internal)
                    {
#if COMPUTE_STATS
                      qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen++;
#endif 
                      if (qdpll->options.qbcp_qbce_find_witness_max_occs)
                        {
                          /* Ignore checking literals for being
                             blocking which have more than
                             'qdpll->options.qbcp_qbce_find_witness_max_occs'
                             occurrences. No maybe-blocked pairs
                             containing such literals will be inserted in
                             the watched data structures. NOTE: this
                             code is executed only once during
                             initialization. Further calls of
                             'find-blocked-clauses' are triggered by
                             watched data structures, and hence no
                             explicit checking for number of
                             occurrences is needed. */
                          BLitsOccStack *occs = QDPLL_LIT_NEG (lit) ? 
                            &var->pos_occ_clauses : &var->neg_occ_clauses;
                          if (QDPLL_COUNT_STACK (*occs) > 
                              qdpll->options.qbcp_qbce_find_witness_max_occs)
                            {
#if COMPUTE_STATS
                              qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_occ_limit++;
#endif
                              if (qdpll->options.verbosity >= 3)
                                fprintf (stderr, "QBCE: skipping maybe blocking literal %d -- %soccs-cnt %u > limit %u\n", 
                                         lit, QDPLL_LIT_NEG (lit) ? "pos-" : "neg-", 
                                         QDPLL_COUNT_STACK (*occs), qdpll->options.qbcp_qbce_find_witness_max_occs);
                              continue;
                            }
                        }
                      if (qdpll->options.qbcp_qbce_max_clause_size)
                        {
                          if ((QDPLL_LIT_NEG (lit) && var->longest_pos_occ_size > 
                               qdpll->options.qbcp_qbce_max_clause_size) || 
                              (QDPLL_LIT_POS (lit) && var->longest_neg_occ_size > 
                               qdpll->options.qbcp_qbce_max_clause_size))
                            {
#if COMPUTE_STATS
                              qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_size_limit++;
#endif
                              if (qdpll->options.verbosity >= 3)
                                fprintf (stderr, "QBCE: skipping maybe blocking literal %d -- longest %socc-size %d > limit %d\n", 
                                         lit, QDPLL_LIT_NEG (lit) ? "pos-" : "neg-", 
                                         QDPLL_LIT_NEG (lit) ? var->longest_pos_occ_size : var->longest_neg_occ_size,   
                                         qdpll->options.qbcp_qbce_max_clause_size);
                              continue;
                            }
                        }
                      QDPLL_PUSH_STACK (qdpll->mm, maybe_blocking_literals, lit);
                    }
                }
            }
          else
            QDPLL_PUSH_STACK (qdpll->mm, maybe_blocking_literals, non_blocking_lit);
          assert (!non_blocking_lit || QDPLL_COUNT_STACK (maybe_blocking_literals) == 1);

          /* Check all potentially blocking literals in the current clause 'c'. */
          Constraint *witness;
          while (!QDPLL_EMPTY_STACK (maybe_blocking_literals))
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_literals_seen++;
#endif
              LitID lit = QDPLL_POP_STACK (maybe_blocking_literals);
              Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
              assert (QDPLL_SCOPE_EXISTS (var->scope));
              /* Selector variables must not be used as blocking literals. */
              assert (!var->is_internal);
              assert (!QDPLL_VAR_ASSIGNED (var));

              if (qdpll->options.verbosity >= 3)
                fprintf (stderr, "  checking potential blocking literal %d\n", lit);
              
              if (!(witness = qbcp_qbce_find_non_blocking_literal_witness (qdpll, lit, c)))
                {
                  if (qdpll->options.verbosity >= 3)
                    fprintf (stderr, "  blocked by literal: %d\n", lit);
                  /* Function returns non-zero if new blocked clauses are found. */
                  found_new_blocked_clauses = 1;
                  /* Set mark bit and blocking literal. */
                  assert (!c->qbcp_qbce_blocked);
                  c->qbcp_qbce_blocked = 1;
                  assert (!c->qbcp_qbce_blocking_lit);
                  c->qbcp_qbce_blocking_lit = lit;
                  /* When currently preprocessing: store occurrence of blocking lit. */
                  if (qdpll->state.qbcp_qbce_currently_preprocessing)
                    qbcp_qbce_prepro_add_blocking_lit_occ (qdpll, c);
                  if (c->is_watched)
                    {
                      /* NOTE: this branch cannot be taken in the very first
                         call of this function, which happens before watcher
                         initialization, since the field 'is_watched' is set during
                         watcher initialization. */
                      if (qdpll->options.verbosity >= 3)
                        {
                          fprintf (stderr, "Clause watched for pures is blocked:");
                          print_constraint (qdpll, c);
                        }
                      LitID *lp, *le;
                      for (lp = c->lits, le = lp + c->num_lits; lp < le; lp++)
                        {
                          LitID lit = *lp;
                          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
                          if (QDPLL_VAR_FORALL (var) && !QDPLL_VAR_ASSIGNED (var))
                            {
                              /* Check if universal variable must update it's clause watcher. */
                              if (!LEARN_VAR_POS_MARKED (var) && 
                                  ((QDPLL_LIT_NEG (lit) && c == var->neg_occ_clauses.start[0].constraint) || 
                                   (QDPLL_LIT_POS (lit) && c == var->pos_occ_clauses.start[0].constraint)))
                                {
                                  /* Mark and collect variable. */
                                  assert (!LEARN_VAR_NEG_MARKED (var));
                                  LEARN_VAR_POS_MARK (var);
                                  QDPLL_PUSH_STACK (qdpll->mm, maybe_pure_literals, lit);
                                  if (qdpll->options.verbosity >= 3)
                                    fprintf (stderr, "...univ var %d needs watcher update\n", var->id);
                                }
                            }
                        }
                    }
                  if (!qdpll->options.no_empty_formula_watching)
                    {
                      /* If the blocked clause is currently watched for empty
                         formula detection, then we must schedule a watcher
                         update. */
                      if (qdpll->empty_formula_watcher && c == qdpll->empty_formula_watcher->constraint)
                        qdpll->state.empty_formula_watcher_scheduled_update = 1;
                    }
                  /* Push blocked clause on local and global stack of blocked
                     clauses. The global stack
                     'qdpll->qbcp_qbce_blocked_clauses' is needed for solution
                     reconstruction. */
                  QDPLL_PUSH_STACK(qdpll->mm, blocked_clauses, c);
                  assert (!qdpll->state.qbcp_qbce_currently_preprocessing || 
                          qdpll->state.decision_level == 0);
                  assert (!qdpll->state.qbcp_qbce_currently_preprocessing || 
                          QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) <= 2);
                  assert (qdpll->state.qbcp_qbce_currently_preprocessing || 
                          QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 
                          qdpll->state.decision_level + 2);
                  QDPLL_PUSH_STACK 
                    (qdpll->mm, qdpll->qbcp_qbce_blocked_clauses.start
                     [qdpll->state.qbcp_qbce_currently_preprocessing ? 
                      0 : qdpll->state.decision_level + 1], c);
                  if (qdpll->options.verbosity >= 3)
                    fprintf (stderr, "  currently %d blocked clauses found in this round\n", 
                             (unsigned int) QDPLL_COUNT_STACK(blocked_clauses));
#if COMPUTE_STATS
                  qdpll->stats.qbcp_qbce_clauses_blocked++;
                  qdpll->stats.qbcp_qbce_current_blocked_clauses++;
                  assert (qdpll->stats.qbcp_qbce_current_blocked_clauses <= 
                          qdpll->pcnf.clauses.cnt);
#endif
                  break;
                }
              else
                {
                  if (qdpll->options.verbosity >= 3)
                    {
                      fprintf (stderr, "  literal %d has non-blocking witness: ", lit);
                      print_constraint (qdpll, witness);
                    }
                  assert (!witness->qbcp_qbce_blocked);
                  assert (!is_clause_satisfied (qdpll, witness));
                  assert (c == pair.blit_occ.constraint);
                  assert (!non_blocking_lit || 
                          (lit == pair.non_blocking_lit && 
                           non_blocking_lit == pair.non_blocking_lit));
                  assert (c->num_lits > 0);
                  assert (c->lits[0]);
                  assert (!pair.blit_occ.blit || constraint_has_lit (pair.blit_occ.constraint, 
                                                                     pair.blit_occ.blit));
                  QBCENonBlockedWitness non_blocked_pair = {lit, {pair.blit_occ.blit, c}, 
                                                            {pair.offset.witness_in_witness_list}, 
                                                            QDPLL_INVALID_WATCHER_POS};
                  /* Store clause 'c' and non-blocking literal 'lit' in
                     notify-list of the witness. */
                  qbcp_qbce_store_witness (qdpll, non_blocked_pair, witness);
                }
            }

          QDPLL_RESET_STACK (maybe_blocking_literals);

          /* Unmark literals in clause 'c'. */
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_literals_seen++;
#endif
              LitID clit = *p;
              Var *cvar = LIT2VARPTR (qdpll->pcnf.vars, clit);
              /* Ignore assigned variables. These assignment can never satisfy
                 the clause, because satisfied clauses are ignored. */
              if (QDPLL_VAR_ASSIGNED (cvar))
                continue;
              assert (QDPLL_VAR_MARKED(cvar));
              QDPLL_VAR_UNMARK (cvar);
            }
        }

      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "pushing clauses to be checked again based on %d blocked clauses:\n", 
                 (unsigned int) QDPLL_COUNT_STACK(blocked_clauses));

      /* Fill set 'maybe-blocked-clauses' based on current blocked-clauses. */
      Constraint **cp, **ce;
      for (cp = blocked_clauses.start, ce = blocked_clauses.top; cp < ce; cp++)
        {
#if COMPUTE_STATS
      qdpll->stats.qbcp_qbce_clauses_seen++;
#endif
          Constraint *c = *cp;
          assert (c->qbcp_qbce_blocked);
          assert (!is_clause_satisfied (qdpll, c));
          if (qdpll->options.verbosity >= 3)
            {
              fprintf (stderr, "  blocked clause: ");
              print_constraint (qdpll, c);
              fprintf (stderr, "    notifies notifies %d pairs to be checked again.\n", 
                       (unsigned int) QDPLL_COUNT_STACK(c->qbcp_qbce_notify_maybe_blocked_clauses));
            }
          /* Push all clauses in the notify-lists of blocked clauses on
             'maybe_blocked_clauses'. */
          QBCENonBlockedWitness *qp, *qe;
          for (qp = c->qbcp_qbce_notify_maybe_blocked_clauses.start, 
                 qe = c->qbcp_qbce_notify_maybe_blocked_clauses.top; qp < qe; qp++)
            {
              assert (qp->offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
#if COMPUTE_STATS
              qdpll->stats.qbcp_qbce_clauses_seen++;
#endif
              QBCENonBlockedWitness pair = *qp;
              assert (pair.non_blocking_lit);
              
              /* Check if clause is satisfied by cached literal. */
              if (!check_disabling_blocking_lit (qdpll, pair.blit_occ, 0))
                continue;
              else
                {
                  if (pair.blit_occ.constraint->qbcp_qbce_blocked)
                    {
                      if (qdpll->options.verbosity >= 3)
                        {
                          fprintf (stderr, "      skipping %s notified clause: ", 
                                   pair.blit_occ.constraint->qbcp_qbce_blocked ? "blocked" : "satisfied");
                          print_constraint (qdpll, pair.blit_occ.constraint);
                        }
                      continue;
                    }
                }
              if (qdpll->options.verbosity >= 3)
                {
                  fprintf (stderr, "      notifying for potential blocking literal %d to be checked in clause: ", 
                           pair.non_blocking_lit);
                  print_constraint (qdpll, pair.blit_occ.constraint);
                }
              /* Set offset-on-working-queue of pair to be enqueued. */
              assert (pair.offset_in_working_queue == QDPLL_INVALID_WATCHER_POS);
              qp->offset_in_working_queue = pair.offset_in_working_queue = 
                QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
              QDPLL_PUSH_STACK
                (qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, pair);
            }
        }
    } while (!QDPLL_EMPTY_STACK (blocked_clauses));

  /* Notify variables which must update their clause watcher which became
     blocked in this round. */
  LitID *p, *e;
  for (p = maybe_pure_literals.start, e = maybe_pure_literals.top; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      assert (QDPLL_VAR_FORALL (var));
      assert (LEARN_VAR_POS_MARKED (var));
      assert (!LEARN_VAR_NEG_MARKED (var));
      LEARN_VAR_POS_UNMARK (var);
      if (!QDPLL_VAR_ASSIGNED (var))
        notify_clause_watching_variables_aux (qdpll, lit, var);
    }

  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "End of QBCE call, returns value %d\n", found_new_blocked_clauses);

  QDPLL_DELETE_STACK (qdpll->mm, blocked_clauses);
  QDPLL_DELETE_STACK (qdpll->mm, maybe_blocking_literals);
  QDPLL_DELETE_STACK (qdpll->mm, maybe_pure_literals);

#ifndef NDEBUG
  assert_qbcp_qbce_non_blocked_witness_integrity (qdpll);
  assert_qbcp_qbce_blocked_clauses_integrity (qdpll);
#endif

  return found_new_blocked_clauses;
}


/* --------------------- END: QBCP-QBCE --------------------- */

/* Function for propagating unit/pure literals and also 
   for assigning decision variables. */
static QDPLLSolverState
bcp (QDPLL * qdpll)
{
#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  Var *vars = qdpll->pcnf.vars;
  VarID *bcp_ptr;
  QDPLLSolverState state = QDPLL_SOLVER_STATE_UNDEF;

  const unsigned int qbce_inprocessing = qdpll->options.qbce_inprocessing;
  const unsigned int qbce_dynamic = !qdpll->options.no_qbce_dynamic;
  assert (!qbce_dynamic || !qbce_inprocessing);
  const unsigned int empty_formula_watching = !qdpll->options.no_empty_formula_watching;

  /* QBCE as inprocessing: the outer do-while loop is executed as long as the
     solver is at level zero, the formula is undecided, and new blocked
     clauses have been identified. The inner while-loop is executed as long as
     there are assignments to be propagated and the formula is still
     undecided. */

  /* Flag to indicate if some assignment was propagated. This is to avoid
     running QBCE again if the top-level assignment has not changed since
     the previous run. */
  unsigned int propagated = 0;
  do 
    { 
      propagated = 0;

      /* Loop breaks as soon as conflict or empty formula detected. */
      while (state == QDPLL_SOLVER_STATE_UNDEF &&
             (bcp_ptr = qdpll->bcp_ptr) < qdpll->assigned_vars_top)
        {
          propagated = 1;

          VarID var_id = *bcp_ptr;
          Var *var = VARID2VARPTR (vars, var_id);

          /* For QBCE as inprocessing on top-level: push clauses which may be blocked
             after assigning a variable at top level. Can ignore universal pure
             literals since they never satisfy clauses. */
          if ((qbce_dynamic || (qbce_inprocessing && qdpll->state.decision_level == 0)) && 
              !(var->mode == QDPLL_VARMODE_PURE && QDPLL_SCOPE_FORALL (var->scope)))
            qbcp_qbce_push_maybe_blocked_clauses_by_assignment (qdpll, var);

#if COMPUTE_STATS
          qdpll->stats.propagations++;
          qdpll->stats.total_prop_dlevels += var->decision_level;
#endif
          assert (var->mode != QDPLL_VARMODE_UNDEF);
          assert (QDPLL_VAR_ASSIGNED (var));
          assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
          assert (!QDPLL_VAR_MARKED_PROPAGATED (var));

          if (QDPLL_VAR_ASSIGNED_TRUE (var))
            state = propagate_variable_assigned 
              (qdpll, var, &(var->pos_notify_clause_watchers), 
               &(var->pos_notify_lit_watchers));
          else
            {
              assert (QDPLL_VAR_ASSIGNED_FALSE (var));
              state = propagate_variable_assigned 
                (qdpll, var, &(var->neg_notify_clause_watchers), 
                 &(var->neg_notify_lit_watchers));
            }

          qdpll->bcp_ptr++;

          if (!empty_formula_watching)
            {
              /* If all variables are propagated and no conflict was found, we can
                 be sure that the formula is SAT. We set the state explicitly here
                 since this is has not been done yet. */
              assert (!qdpll->options.no_sdcl || state != QDPLL_SOLVER_STATE_SAT);
              if (state == QDPLL_SOLVER_STATE_UNDEF &&
                  qdpll->bcp_ptr == qdpll->assigned_vars_top &&
                  qdpll->pcnf.used_vars ==
                  (unsigned int) (qdpll->assigned_vars_top - qdpll->assigned_vars))
                state = QDPLL_SOLVER_STATE_SAT;
            }
        }

      if (empty_formula_watching)
        {
          if (state == QDPLL_SOLVER_STATE_UNDEF &&
              !update_empty_formula_watcher (qdpll))
            state = QDPLL_SOLVER_STATE_SAT;
        }

    } while ((qbce_dynamic || (qbce_inprocessing && qdpll->state.decision_level == 0)) && 
             propagated &&  
             state == QDPLL_SOLVER_STATE_UNDEF && 
             qbcp_qbce_find_blocked_clauses (qdpll));

#ifndef NDEBUG
  assert (!qdpll->state.assumptions_given || assumptions_given (qdpll));
  assert (qdpll->state.assumptions_given || !assumptions_given (qdpll));
#if QDPLL_ASSERT_BCP_WATCHERS_INTEGRITY
  if (state == QDPLL_SOLVER_STATE_UNDEF)
    {
      assert_all_unit_literals_and_literal_watchers_integrity (qdpll);
      if (!qbce_dynamic && !qbce_inprocessing)
        assert_all_pure_literals_and_clause_watchers_integrity (qdpll);
      assert_incremental_selector_vars (qdpll);
    }
#endif
#endif
#if COMPUTE_TIMES
  qdpll->time_stats.total_bcp_time += (time_stamp () - start);
#endif

  return state;
}


static void
notify_inactive_at_decision_point (QDPLL * qdpll)
{
  assert (qdpll->bcp_ptr == qdpll->assigned_vars_top);
  Var *vars = qdpll->pcnf.vars;
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (qdpll->bcp_ptr == qdpll->assigned_vars_top);
  assert (qdpll->old_bcp_ptr >= qdpll->assigned_vars);
  assert (qdpll->old_bcp_ptr <= qdpll->bcp_ptr);

  VarID *p, *e;
  for (p = qdpll->old_bcp_ptr, e = qdpll->assigned_vars_top; p < e; p++)
    {
      Var *var = VARID2VARPTR (vars, *p);
      dm->notify_inactive (dm, var->id);
    }

  qdpll->old_bcp_ptr = qdpll->assigned_vars_top;
}


static void
push_forced_assignment (QDPLL * qdpll)
{
  assert (qdpll->state.forced_assignment.var);
  assert (qdpll->state.forced_assignment.assignment);
  assert (qdpll->state.forced_assignment.mode);

  /* Setting antecedent is only relevant for learning. */
  qdpll->state.forced_assignment.var->antecedent =
    qdpll->state.forced_assignment.antecedent;
  if (qdpll->state.forced_assignment.antecedent)
    {
      assert (!qdpll->state.forced_assignment.antecedent->qbcp_qbce_blocked);
      assert (!qdpll->state.forced_assignment.antecedent->is_reason);
      qdpll->state.forced_assignment.antecedent->is_reason = 1;
    }

#ifndef NDEBUG
#if QDPLL_ASSERT_CDCL_FORCED_ANTECEDENT
  Constraint *antecedent;
  if ((antecedent = qdpll->state.forced_assignment.antecedent)
      && !antecedent->is_cube)
    {
      /* It can happen that conflict clause is satisfied by a true
         universal literal which was assigned after being
         forall-reduced. */
      assert (!is_clause_satisfied (qdpll, antecedent) ||
              assert_is_clause_satisfied_by_univ_lit (qdpll,
                                                      qdpll->state.
                                                      forced_assignment.
                                                      assignment ==
                                                      QDPLL_ASSIGNMENT_TRUE ?
                                                      qdpll->state.
                                                      forced_assignment.var->
                                                      id : -qdpll->state.
                                                      forced_assignment.var->
                                                      id, antecedent));
      assert (!is_clause_empty (qdpll, antecedent));
      Var *vars = qdpll->pcnf.vars, *var, *implied_var;
      LitID *p, *e, lit;
      for (p = antecedent->lits, e = p + antecedent->num_lits; p < e; p++)
        {
          /* Check that exactly one existential 
             literal is unassigned (i.e. implied). */
          lit = *p;
          var = LIT2VARPTR (vars, lit);

          if (QDPLL_SCOPE_EXISTS (var->scope) && !QDPLL_VAR_ASSIGNED (var))
            {
              implied_var = var;
              assert (implied_var == qdpll->state.forced_assignment.var);
              for (p = p + 1; p < e; p++)
                {
                  lit = *p;
                  var = LIT2VARPTR (vars, lit);
                  assert (!QDPLL_SCOPE_EXISTS (var->scope)
                          || QDPLL_VAR_ASSIGNED (var));
                }
              break;
            }
        }
    }
#endif
#endif

  push_assigned_variable (qdpll, qdpll->state.forced_assignment.var,
                          qdpll->state.forced_assignment.assignment,
                          qdpll->state.forced_assignment.mode);

  qdpll->state.forced_assignment.antecedent = 0;
  qdpll->state.forced_assignment.var = 0;
  qdpll->state.forced_assignment.assignment =
    qdpll->state.forced_assignment.mode = 0;
}


/* Remove marked occs by explicit search. */
static void
cleanup_constraint_sweep_occs (QDPLL * qdpll, BLitsOccStack * occs)
{
  BLitsOcc *p, *e;
  for (p = occs->start, e = occs->top; p < e; p++)
    {
      assert (BLIT_STRIP_PTR (p->constraint)->is_cube ||
              !BLIT_MARKED_PTR (p->constraint));
      assert (!BLIT_STRIP_PTR (p->constraint)->is_cube ||
              BLIT_MARKED_PTR (p->constraint));
      if (BLIT_STRIP_PTR (p->constraint)->deleted)
        {
          /* Overwrite with last element. */
          *p = QDPLL_POP_STACK (*occs);
          /* Must check copied element in next iteration. */
          p--;
          e--;
        }
    }
}


/* Unlink contraint from all lists and release memory. */
static void
unlink_and_delete_constraint (QDPLL * qdpll, Constraint * c)
{
  assert (qdpll->result_constraint != c);
  assert (c->learnt);
  assert (!c->is_reason);
  assert (!c->is_watched);
  const int is_cube = c->is_cube;
  /* Unlink constraint from learnt-clause/cube list. */
  if (is_cube)
    UNLINK (qdpll->pcnf.learnt_cubes, c, link);
  else
    UNLINK (qdpll->pcnf.learnt_clauses, c, link);

  assert ((c->lwatcher_pos == c->rwatcher_pos &&
           c->lwatcher_pos == QDPLL_INVALID_WATCHER_POS) ||
          (c->lwatcher_pos < c->rwatcher_pos && c->lwatcher_pos < c->num_lits
           && c->rwatcher_pos < c->num_lits));
  if (c->lwatcher_pos != QDPLL_INVALID_WATCHER_POS)
    {
      assert (c->rwatcher_pos != QDPLL_INVALID_WATCHER_POS);
      /* Delete constraint from lit-watcher notify list. */
      remove_clause_from_notify_list (qdpll, is_cube, 0,
                                      c->lits[c->lwatcher_pos], c);
      remove_clause_from_notify_list (qdpll, is_cube, 1,
                                      c->lits[c->rwatcher_pos], c);
    }

  delete_constraint (qdpll, c);
}


/* Delete all marked constraints, clean up occ-lists. */
static void
cleanup_constraint_sweep (QDPLL * qdpll, unsigned int del,
                          const QDPLLQuantifierType type)
{
  assert (qdpll->options.no_spure_literals);
  assert (type == QDPLL_QTYPE_EXISTS || type == QDPLL_QTYPE_FORALL);
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          if (type == QDPLL_QTYPE_EXISTS)
            {
              cleanup_constraint_sweep_occs (qdpll, &(p->neg_occ_clauses));
              cleanup_constraint_sweep_occs (qdpll, &(p->pos_occ_clauses));
            }
          else
            {
              cleanup_constraint_sweep_occs (qdpll, &(p->neg_occ_cubes));
              cleanup_constraint_sweep_occs (qdpll, &(p->pos_occ_cubes));
            }
        }
    }

  ConstraintList *constraints;
  if (type == QDPLL_QTYPE_EXISTS)
    constraints = &(qdpll->pcnf.learnt_clauses);
  else
    constraints = &(qdpll->pcnf.learnt_cubes);
  unsigned int check_del = 0;
  Constraint *c, *next;
  for (c = constraints->first; c; c = next)
    {
      assert (c->learnt);
      next = c->link.next;
      if (c->deleted)
        {
#ifndef NDEBUG
          check_del++;
#endif
          unlink_and_delete_constraint (qdpll, c);
        }
    }
  assert (del == check_del);
}


static unsigned int
check_resize_learnt_constraints_aux (QDPLL * qdpll, ConstraintList *constraints, 
                                     unsigned int try_delete, const QDPLLQuantifierType type)
{
  /* Parameter 'try_delete == UINT_MAX' if this function is called to discard
     all learned cubes in incremental solving. */
  unsigned int del = 0;
  Constraint *c;
  assert (del < try_delete);
  const int no_spure_literals = qdpll->options.no_spure_literals;
  Constraint *prev, *result_constraint = qdpll->result_constraint;
  for (c = constraints->last; c && (del < try_delete); c = prev)
    {
      assert (c->is_cube || c->learnt);
      prev = c->link.prev;

      if (!c->is_reason && !c->is_watched && 
          c != result_constraint && !(c->is_cube && !c->learnt))
        {
#if COMPUTE_STATS
          assert (!c->derived_by_trivial_truth_or_falsity || 
                  !c->derived_by_dynamic_nenofex);
          if (c->derived_by_trivial_truth_or_falsity)
            {
              if (c->is_cube)
                qdpll->stats.trivial_truth_deleted_cubes++;
              else
                qdpll->stats.trivial_falsity_deleted_clauses++;;
            }
          else if (c->derived_by_dynamic_nenofex)
            {
              if (c->is_cube)
                qdpll->stats.dyn_nenofex_deleted_cubes++;
              else
                qdpll->stats.dyn_nenofex_deleted_clauses++;
            }
#endif
          if (!no_spure_literals)
            unlink_and_delete_constraint (qdpll, c);
          else
            {
              /* Allowing: spurious pure lits: only mark as deleted,
                 then clean up formula, including occ-lists, in one
                 sweep. This should be faster than cleaning
                 (i.e. searching) all occ-stacks in one pass. */
              assert (!c->deleted);
              c->deleted = 1;
            }
          del++;
        }
    }

  if (no_spure_literals)
    cleanup_constraint_sweep (qdpll, del, type);

  assert (try_delete == UINT_MAX || type != QDPLL_QTYPE_EXISTS ||
          qdpll->state.lclauses_size == qdpll->pcnf.learnt_clauses.cnt + del);
  assert (try_delete == UINT_MAX || type != QDPLL_QTYPE_FORALL ||
          qdpll->state.lcubes_size == qdpll->pcnf.learnt_cubes.cnt + del);

  return del;
}


static void
check_resize_learnt_constraints (QDPLL * qdpll, const QDPLLQuantifierType type)
{
  QDPLL_ABORT_QDPLL (qdpll->state.lclauses_size == 0, "Size of learned clauses must be greater than zero!");
  QDPLL_ABORT_QDPLL (qdpll->state.lcubes_size == 0, "Size of learned cubes must be greater than zero!");

  /* Increase constraint sets only if we do not exceed soft space limit. */
  const size_t cur_allocated = qdpll_cur_allocated (qdpll->mm);
  const int cur_exceeded_soft_max_space =
    qdpll->options.soft_max_space &&
    (qdpll->options.soft_max_space * 1024 * 1024 < cur_allocated);
  qdpll->state.exceeded_soft_max_space = qdpll->state.exceeded_soft_max_space
    || cur_exceeded_soft_max_space;

  ConstraintList *constraints;
  Constraint *c;
  if (type == QDPLL_QTYPE_EXISTS)
    {
      if (!cur_exceeded_soft_max_space
          && qdpll->pcnf.learnt_clauses.cnt < qdpll->state.lclauses_size)
        return;
      constraints = &(qdpll->pcnf.learnt_clauses);
    }
  else
    {
      if (!cur_exceeded_soft_max_space
          && qdpll->pcnf.learnt_cubes.cnt < qdpll->state.lcubes_size)
        return;
      constraints = &(qdpll->pcnf.learnt_cubes);
    }

  if (type == QDPLL_QTYPE_EXISTS)
    qdpll->state.clause_resizes++;
  else
    qdpll->state.cube_resizes++;

  if (qdpll->options.verbosity > 0)
    fprintf (stderr, "Reduce: %s, cur. size %u, cur cnt %u\n",
             type == QDPLL_QTYPE_EXISTS ? "clauses" : "cubes",
             type == QDPLL_QTYPE_EXISTS ? qdpll->state.lclauses_size :
             qdpll->state.lcubes_size,
             type ==
             QDPLL_QTYPE_EXISTS ? qdpll->pcnf.learnt_clauses.
             cnt : qdpll->pcnf.learnt_cubes.cnt);

  assert (cur_exceeded_soft_max_space || (type == QDPLL_QTYPE_EXISTS &&
                                          qdpll->pcnf.learnt_clauses.cnt ==
                                          qdpll->state.lclauses_size)
          || (type == QDPLL_QTYPE_FORALL
              && qdpll->pcnf.learnt_cubes.cnt == qdpll->state.lcubes_size));

  /* Try to delete half of learnt constraints, starting from back of
     lists which is supposed to contain 'less important' constraints. */
  unsigned int try_delete = type == QDPLL_QTYPE_EXISTS ?
    qdpll->pcnf.learnt_clauses.cnt * qdpll->options.lclauses_delfactor :
    qdpll->pcnf.learnt_cubes.cnt * qdpll->options.lcubes_delfactor;

  unsigned int del = 
    check_resize_learnt_constraints_aux (qdpll, constraints, try_delete, type);

#if COMPUTE_STATS
  qdpll->stats.total_constraint_dels += del;
  if (type == QDPLL_QTYPE_EXISTS)
    qdpll->stats.total_clause_dels += del;
  else
    qdpll->stats.total_cube_dels += del;
#endif

  if (!qdpll->state.exceeded_soft_max_space)
    {
      if (type == QDPLL_QTYPE_EXISTS)
        {
          if (qdpll->options.no_lin_lclauses_inc)
            qdpll->state.lclauses_size +=
              (qdpll->state.clause_resizes *
               qdpll->options.lclauses_resize_value);
          else
            qdpll->state.lclauses_size +=
              qdpll->options.lclauses_resize_value;
        }
      else
        {
          if (qdpll->options.no_lin_lcubes_inc)
            qdpll->state.lcubes_size +=
              (qdpll->state.cube_resizes *
               qdpll->options.lcubes_resize_value);
          else
            qdpll->state.lcubes_size += qdpll->options.lcubes_resize_value;
        }
      if (qdpll->options.verbosity > 0)
        fprintf (stderr, "Reduce: del. %d %s, new size %u, new cnt: %u\n",
                 del, type == QDPLL_QTYPE_EXISTS ? "clauses" : "cubes",
                 type ==
                 QDPLL_QTYPE_EXISTS ? qdpll->state.
                 lclauses_size : qdpll->state.lcubes_size,
                 type ==
                 QDPLL_QTYPE_EXISTS ? qdpll->pcnf.learnt_clauses.
                 cnt : qdpll->pcnf.learnt_cubes.cnt);
    }
  else
    {
      if (qdpll->options.verbosity > 0)
        fprintf (stderr,
                 "Reduce: del. %d %s, cur size %u, cur cnt %u, soft limit %u MB reached (alloc.: %f MB)\n",
                 del, type == QDPLL_QTYPE_EXISTS ? "clauses" : "cubes",
                 type ==
                 QDPLL_QTYPE_EXISTS ? qdpll->state.
                 lclauses_size : qdpll->state.lcubes_size,
                 type ==
                 QDPLL_QTYPE_EXISTS ? qdpll->pcnf.learnt_clauses.
                 cnt : qdpll->pcnf.learnt_cubes.cnt,
                 qdpll->options.soft_max_space,
                 cur_allocated / 1024 / (float) 1024);
    }

  QDPLL_ABORT_QDPLL (qdpll->pcnf.learnt_clauses.cnt > qdpll->state.lclauses_size, 
                     "Invalid number of learned clauses!");
  QDPLL_ABORT_QDPLL (qdpll->pcnf.learnt_cubes.cnt > qdpll->state.lcubes_size, 
                     "Invalid number of learned cubes!");
}


static void
print_config (QDPLL * qdpll)
{
  fprintf (stderr, "\n---------- CONFIG ----------\n");
  if (qdpll->options.no_pure_literals)
    fprintf (stderr, "--no-pure-literals=1\n");
  else
    fprintf (stderr, "--no-pure-literals=0\n");
  if (qdpll->options.no_spure_literals)
    fprintf (stderr, "--no-spure-literals=1\n");
  else
    fprintf (stderr, "--no-spure-literals=0\n");
  if (qdpll->options.no_cdcl)
    fprintf (stderr, "--no-cdcl=1\n");
  else
    fprintf (stderr, "--no-cdcl=0\n");
  if (qdpll->options.no_sdcl)
    fprintf (stderr, "--no-sdcl=1\n");
  else
    fprintf (stderr, "--no-sdcl=0\n");
  if (qdpll->options.no_univ_cache)
    fprintf (stderr, "--no-univ-cache=1\n");
  else
    fprintf (stderr, "--no-univ-cache=0\n");
  if (qdpll->options.no_exists_cache)
    fprintf (stderr, "--no-exists-cache=1\n");
  else
    fprintf (stderr, "--no-exists-cache=0\n");

  fprintf (stderr, "--var-act-bias=%d\n", qdpll->options.var_act_bias);

  if (qdpll->options.no_unit_mtf)
    fprintf (stderr, "--no-unit-mtf=1\n");
  else
    fprintf (stderr, "--no-unit-mtf=0\n");
  if (qdpll->options.no_res_mtf)
    fprintf (stderr, "--no-res-mtf=1\n");
  else
    fprintf (stderr, "--no-res-mtf=0\n");
  if (qdpll->options.dh == QDPLL_DH_SIMPLE)
    fprintf (stderr, "--dec-heur=simple\n");
  else if (qdpll->options.dh == QDPLL_DH_SDCL)
    fprintf (stderr, "--dec-heur=sdcl\n");
  else if (qdpll->options.dh == QDPLL_DH_QTYPE)
    fprintf (stderr, "--dec-heur=qtype\n");
  else if (qdpll->options.dh == QDPLL_DH_RANDOM)
    fprintf (stderr, "--dec-heur=rand\n");
  else if (qdpll->options.dh == QDPLL_DH_FALSIFY)
    fprintf (stderr, "--dec-heur=falsify\n");
  else if (qdpll->options.dh == QDPLL_DH_SATISFY)
    fprintf (stderr, "--dec-heur=satisfy\n");
  else
    assert (0);

  fprintf (stderr, "--seed=%d\n", qdpll->options.seed);

  if (qdpll->options.depman_simple)
    fprintf (stderr, "--dep-man=simple\n");
  if (qdpll->options.depman_qdag)
    fprintf (stderr, "--dep-man=qdag\n");
  fprintf (stderr, "--max-dec=%d\n", qdpll->options.max_dec);
  fprintf (stderr, "--max-secs=%d\n", qdpll->options.max_secs);
  fprintf (stderr, "--max-btracks=%d\n", qdpll->options.max_btracks);
  fprintf (stderr, "--max-space=%d\n", qdpll->options.max_space);
  fprintf (stderr, "--soft-max-space=%d\n", qdpll->options.soft_max_space);
  fprintf (stderr, "--lclauses-resize-value=%f\n",
           qdpll->options.lclauses_resize_value);
  fprintf (stderr, "--lcubes-resize-value=%f\n",
           qdpll->options.lcubes_resize_value);
  fprintf (stderr, "--lclauses-init-size=%f\n",
           qdpll->options.lclauses_init_size);
  fprintf (stderr, "--lcubes-init-size=%f\n",
           qdpll->options.lcubes_init_size);

  fprintf (stderr, "--lclauses-min-init-size=%d\n",
           qdpll->options.lclauses_min_init_size);
  fprintf (stderr, "--lclauses-max-init-size=%d\n",
           qdpll->options.lclauses_max_init_size);
  fprintf (stderr, "--lcubes-min-init-size=%d\n",
           qdpll->options.lcubes_min_init_size);
  fprintf (stderr, "--lcubes-max-init-size=%d\n",
           qdpll->options.lcubes_max_init_size);

  fprintf (stderr, "--lclauses-delfactor=%f\n",
           qdpll->options.lclauses_delfactor);
  fprintf (stderr, "--lcubes-delfactor=%f\n",
           qdpll->options.lcubes_delfactor);
  fprintf (stderr, "--var-act-inc=%f\n", qdpll->options.var_act_inc);
  fprintf (stderr, "--var-act-dec-ifactor=%f\n",
           qdpll->options.var_act_decay_ifactor);
  fprintf (stderr, "--irestart-dist-init=%u\n",
           qdpll->options.irestart_dist_init);
  fprintf (stderr, "--irestart-dist-inc=%u\n",
           qdpll->options.irestart_dist_inc);
  fprintf (stderr, "--orestart-dist-init=%u\n",
           qdpll->options.orestart_dist_init);
  fprintf (stderr, "--orestart-dist-inc=%u\n",
           qdpll->options.orestart_dist_inc);

  if (qdpll->options.no_lin_irestart_inc)
    fprintf (stderr, "--no-lin-irestart-inc=1\n");
  else
    fprintf (stderr, "--no-lin-irestart-inc=0\n");
  if (qdpll->options.no_lin_orestart_inc)
    fprintf (stderr, "--no-lin-orestart-inc=1\n");
  else
    fprintf (stderr, "--no-lin-orestart-inc=0\n");

  if (qdpll->options.no_lin_lcubes_inc)
    fprintf (stderr, "--no-lin-lcubes-inc=1\n");
  else
    fprintf (stderr, "--no-lin-lcubes-inc=0\n");
  if (qdpll->options.no_lin_lclauses_inc)
    fprintf (stderr, "--no-lin-lclauses-inc=1\n");
  else
    fprintf (stderr, "--no-lin-lclauses-inc=0\n");

  if (qdpll->options.trace)
    {
      fprintf (stderr, "--trace=%s\n",
               qdpll->options.trace == TRACE_QRP ? "qrp" : "bqrp");
    }
  else
    fprintf (stderr, "--trace=0\n");

  if (qdpll->options.no_qpup_cdcl)
    fprintf (stderr, "--no-qpup-cdcl=1\n");
  else
    fprintf (stderr, "--no-qpup-cdcl=0\n");

  if (qdpll->options.no_qpup_sdcl)
    fprintf (stderr, "--no-qpup-sdcl=1\n");
  else
    fprintf (stderr, "--no-qpup-sdcl=0\n");

  if (qdpll->options.traditional_qcdcl)
    fprintf (stderr, "--traditional-qcdcl=1\n");
  else
    fprintf (stderr, "--traditional-qcdcl=0\n");
  if (qdpll->options.no_lazy_qpup)
    fprintf (stderr, "--no-lazy-qpup=1\n");
  else
    fprintf (stderr, "--no-lazy-qpup=0\n");
  if (qdpll->options.bump_vars_once)
    fprintf (stderr, "--bump-vars-once=1\n");
  else
    fprintf (stderr, "--bump-vars-once=0\n");

  if (qdpll->options.long_dist_res)
    fprintf (stderr, "--long-dist-res=1\n");
  else
    fprintf (stderr, "--long-dist-res=0\n");

  if (qdpll->options.incremental_use)
    fprintf (stderr, "--incremental-use=1\n");
  else
    fprintf (stderr, "--incremental-use=0\n");

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  if (qdpll->options.elim_univ_dynamic_switch)
    fprintf (stderr, "--elim-univ-dynamic-switch=1\n");
  else 
    fprintf (stderr, "--elim-univ-dynamic-switch=0\n");

  fprintf (stderr, "--elim-univ-dynamic-switch-delay=%d\n", 
           qdpll->options.elim_univ_dynamic_switch_delay);


  fprintf (stderr, "--elim-univ-dynamic-success-threshold=%d\n", 
           qdpll->options.elim_univ_dynamic_success_threshold);
#endif

  if (qdpll->options.qbcp_qbce_watcher_list_mtf)
    fprintf (stderr, "--qbcp-qbce-watcher-list-mtf=1\n");
  else
    fprintf (stderr, "--qbcp-qbce-watcher-list-mtf=0\n");

  fprintf (stderr, "--qbce-witness-max-occs=%d\n", 
           qdpll->options.qbcp_qbce_find_witness_max_occs);

  fprintf (stderr, "--qbce-max-clause-size=%d\n", 
           qdpll->options.qbcp_qbce_max_clause_size);

  fprintf (stderr, "--qbce-preprocessing=%d\n", qdpll->options.qbce_preprocessing);
  fprintf (stderr, "--qbce-inprocessing=%d\n", qdpll->options.qbce_inprocessing);
  fprintf (stderr, "--no-qbce-dynamic=%d\n", qdpll->options.no_qbce_dynamic);

  fprintf (stderr, "--no-empty-formula-watching=%d\n", qdpll->options.no_empty_formula_watching);

  fprintf (stderr, "--no-trivial-falsity=%d\n", qdpll->options.no_trivial_falsity);
  fprintf (stderr, "--trivial-falsity-pow2-call-interval=%d\n", qdpll->options.trivial_falsity_pow2_call_interval);
  fprintf (stderr, "--trivial-falsity-decision-limit=%d\n", qdpll->options.trivial_falsity_decision_limit);
  fprintf (stderr, "--trivial-falsity-disable-calls-threshold=%d\n", qdpll->options.trivial_falsity_disable_calls_threshold);
  fprintf (stderr, "--trivial-falsity-disable-time-threshold=%f\n", qdpll->options.trivial_falsity_disable_time_threshold);
  fprintf (stderr, "--trivial-falsity-disable-cnf-threshold=%d\n", qdpll->options.trivial_falsity_disable_cnf_threshold);
  fprintf (stderr, "--trivial-falsity-partial-mus-assumptions=%d\n", qdpll->options.trivial_falsity_partial_mus_assumptions);

  fprintf (stderr, "--no-trivial-truth=%d\n", qdpll->options.no_trivial_truth);
  fprintf (stderr, "--trivial-truth-pow2-call-interval=%d\n", qdpll->options.trivial_truth_pow2_call_interval);
  fprintf (stderr, "--trivial-truth-disable-calls-threshold=%d\n", qdpll->options.trivial_truth_disable_calls_threshold);
  fprintf (stderr, "--trivial-truth-disable-time-threshold=%f\n", qdpll->options.trivial_truth_disable_time_threshold);
  fprintf (stderr, "--trivial-truth-decision-limit=%d\n", qdpll->options.trivial_truth_decision_limit);
  fprintf (stderr, "--trivial-truth-disable-cnf-threshold=%d\n", qdpll->options.trivial_truth_disable_cnf_threshold);

  fprintf (stderr, "--no-dynamic-nenofex=%d\n", qdpll->options.no_dynamic_nenofex);
  fprintf (stderr, "--dyn-nenofex-ignore-sat=%d\n", qdpll->options.dyn_nenofex_ignore_sat);
  fprintf (stderr, "--dyn-nenofex-ignore-unsat=%d\n", qdpll->options.dyn_nenofex_ignore_unsat);
  fprintf (stderr, "--dyn-nenofex-pow2-call-interval=%d\n", qdpll->options.dyn_nenofex_pow2_call_interval);
  fprintf (stderr, "--dyn-nenofex-disable-calls-threshold=%d\n", qdpll->options.dyn_nenofex_disable_calls_threshold);
  fprintf (stderr, "--dyn-nenofex-disable-time-threshold=%f\n", qdpll->options.dyn_nenofex_disable_time_threshold);
  fprintf (stderr, "--dyn-nenofex-disable-cnf-threshold=%d\n", qdpll->options.dyn_nenofex_disable_cnf_threshold);

  fprintf (stderr, "----------------------------\n\n");
}


static unsigned int
get_highest_univ_dec_level (QDPLL * qdpll)
{
  Var *var = 0, *vars = qdpll->pcnf.vars;
  VarID *p, *e;
  for (p = qdpll->assigned_vars_top - 1, e = qdpll->assigned_vars; e <= p;
       p--)
    {
      var = VARID2VARPTR (vars, *p);
      /* When using SDCL, then will never have right branches on
         decisions due to asserting clauses. */
      if ((var->mode == QDPLL_VARMODE_LBRANCH ||
           var->mode == QDPLL_VARMODE_RBRANCH)
          && QDPLL_SCOPE_FORALL (var->scope))
        break;
    }
  /* Must handle pure existential formula. */
  if (!var || var->decision_level == 0)
    return 1;
  else
    return var->decision_level;
}


static int
check_and_restart (QDPLL * qdpll, unsigned int backtrack_level)
{
  if (backtrack_level > 1 && qdpll->state.irestart_dist &&
      (qdpll->state.num_backtracks -
       qdpll->state.last_backtracks) >= qdpll->state.irestart_dist)
    {
      if (qdpll->options.no_lin_irestart_inc)
        qdpll->state.irestart_dist +=
          ((1 +
            qdpll->state.num_inner_restarts) *
           qdpll->options.irestart_dist_inc);
      else
        qdpll->state.irestart_dist += qdpll->options.irestart_dist_inc;
      qdpll->state.num_restarts++;
      qdpll->state.last_backtracks = qdpll->state.num_backtracks;
      qdpll->state.num_inner_restarts++;
      unsigned int highest_univ = get_highest_univ_dec_level (qdpll);
      unsigned int btlevel = 1;
      btlevel =
        backtrack_level < highest_univ ? backtrack_level : highest_univ;
#if COMPUTE_STATS
      qdpll->stats.total_restart_dlevels += qdpll->state.decision_level;
      qdpll->stats.total_restart_at_dlevels += btlevel - 1;
      qdpll->stats.total_restart_at_dist +=
        (qdpll->state.decision_level - btlevel) + 1;
#endif
      backtrack (qdpll, btlevel);
      if (btlevel == backtrack_level)
        push_forced_assignment (qdpll);
      else
        {
          assert (!qdpll->state.restarting);
          qdpll->state.restarting = 1;
          memset (&(qdpll->state.forced_assignment), 0,
                  sizeof (qdpll->state.forced_assignment));
        }
      if (qdpll->options.verbosity > 0)
        fprintf (stderr, "Restart %d, bt %d, inc %d, next dist %d\n",
                 qdpll->state.num_inner_restarts, qdpll->state.num_backtracks,
                 qdpll->options.irestart_dist_inc,
                 qdpll->state.irestart_dist);

      /* Check outer limits. */
      if (qdpll->state.orestart_dist &&
          qdpll->state.num_inner_restarts >= qdpll->state.orestart_dist)
        {
          if (qdpll->options.no_lin_orestart_inc)
            qdpll->state.orestart_dist +=
              ((1 +
                qdpll->state.num_restart_resets) *
               qdpll->options.orestart_dist_inc);
          else
            qdpll->state.orestart_dist += qdpll->options.orestart_dist_inc;
          qdpll->state.irestart_dist = qdpll->options.irestart_dist_init;
          qdpll->state.num_inner_restarts = 0;
          qdpll->state.num_restart_resets++;
          if (qdpll->options.verbosity > 0)
            fprintf (stderr, "Reset restarts, o-inc %d, next reset %d\n",
                     qdpll->options.orestart_dist_inc,
                     qdpll->state.orestart_dist);
        }
      return 1;
    }
  return 0;
}


static void
reset_occ_lists (QDPLL * qdpll)
{
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        {
          QDPLL_RESET_STACK (p->pos_occ_clauses);
          QDPLL_RESET_STACK (p->neg_occ_clauses);
          QDPLL_RESET_STACK (p->pos_occ_cubes);
          QDPLL_RESET_STACK (p->neg_occ_cubes);
        }
    }
}


static void
setup_occ_lists_aux (QDPLL * qdpll, Constraint * c)
{
  const int is_cube = c->is_cube;
  Var *vars = qdpll->pcnf.vars;
  QDPLLMemMan *mm = qdpll->mm;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      BLitsOcc blit = { lit, c };
      if (!is_cube)
        {
          if (QDPLL_LIT_NEG (lit))
            QDPLL_PUSH_STACK (mm, var->neg_occ_clauses, blit);
          else
            QDPLL_PUSH_STACK (mm, var->pos_occ_clauses, blit);
        }
      else
        {
          blit.constraint = BLIT_MARK_PTR (blit.constraint);
          if (QDPLL_LIT_NEG (lit))
            QDPLL_PUSH_STACK (mm, var->neg_occ_cubes, blit);
          else
            QDPLL_PUSH_STACK (mm, var->pos_occ_cubes, blit);
        }
    }
}


static void
setup_occ_lists (QDPLL * qdpll)
{
#ifndef NDEBUG
  /* All occ-lists must be properly reset. */
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    assert (!p->id || (QDPLL_EMPTY_STACK (p->neg_occ_clauses) &&
                       QDPLL_EMPTY_STACK (p->pos_occ_clauses) &&
                       QDPLL_EMPTY_STACK (p->neg_occ_cubes) &&
                       QDPLL_EMPTY_STACK (p->pos_occ_cubes)));
#endif
  Constraint *c;
  ConstraintList constraints = qdpll->pcnf.clauses;
  for (c = constraints.first; c; c = c->link.next)
    setup_occ_lists_aux (qdpll, c);

  if (qdpll->options.no_spure_literals && !qdpll->options.no_pure_literals)
    {
      constraints = qdpll->pcnf.learnt_clauses;
      for (c = constraints.first; c; c = c->link.next)
        setup_occ_lists_aux (qdpll, c);

      constraints = qdpll->pcnf.learnt_cubes;
      for (c = constraints.first; c; c = c->link.next)
        setup_occ_lists_aux (qdpll, c);
    }
}


static int
check_limits_and_abort(QDPLL *qdpll)
{
  assert (!qdpll->options.limit_set || (qdpll->options.max_dec || qdpll->options.max_secs || qdpll->options.max_btracks));
  assert (!(qdpll->options.max_dec || qdpll->options.max_secs || qdpll->options.max_btracks) || qdpll->options.limit_set);

  if (!qdpll->options.limit_set)
    return 0;
  else
    {
      if ((qdpll->options.max_dec && qdpll->state.num_decisions > qdpll->options.max_dec) || 
          (qdpll->options.max_btracks && qdpll->state.num_backtracks > qdpll->options.max_btracks) || 
          (qdpll->options.max_secs && 
           (time_stamp() - qdpll->state.solving_start_time) > qdpll->options.max_secs))
        return 1;
      else 
        return 0;
    }
}


static void
assume_aux (QDPLL *qdpll, LitID id)
{
  QDPLL_ABORT_QDPLL(qdpll->state.decision_level != 0, 
                    "Expecting decision-level == 0!");
  QDPLL_ABORT_QDPLL(id == 0, 
                    "Expecting non-zero variable ID!");
  QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint, 
                    "Assumption subset not cleaned up properly!");
  Var *var = LIT2VARPTR(qdpll->pcnf.vars, id);
  QDPLLAssignment assignment = id < 0 ? 
    QDPLL_ASSIGNMENT_FALSE : QDPLL_ASSIGNMENT_TRUE;
  QDPLLVarMode mode = QDPLL_VARMODE_ASSUMED;
  qdpll->state.assumptions_given = 1;
  push_assigned_variable (qdpll, var, assignment, mode);
}


static int
clause_has_popped_off_var (QDPLL *qdpll, Constraint *c);


static void
assign_frame_selector_vars_aux (QDPLL *qdpll, VarIDStack *stack, 
                                const int cur_used_internal_vars)
{
  assert (stack == &qdpll->state.cur_used_internal_vars || 
          stack == &qdpll->state.popped_off_internal_vars);
  assert (!cur_used_internal_vars || stack == &qdpll->state.cur_used_internal_vars);
  assert (cur_used_internal_vars || stack != &qdpll->state.cur_used_internal_vars);
  VarID *p, *e;
  for (p = stack->start, e = stack->top; p < e; p++)
    {
      VarID id = *p;
      if (id)
        {
          assert (id >= qdpll->pcnf.size_user_vars);
          assert (id < qdpll->pcnf.size_vars);
          Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
          if (var->id)
            {
              assert (var->is_internal);
              /* Stack 'qdpll->state.popped_off_internal_vars' must not
                 contain selector variables of deactivated groups. */
              assert (cur_used_internal_vars || !var->is_cur_inactive_group_selector);
              assert (!cur_used_internal_vars || var->clause_group_id == 
                      (unsigned int)(p - qdpll->state.cur_used_internal_vars.start + 1));
              /* Set internal variable to 'false' ('true') to enable (disable)
                 clauses where that variable occurs. */
              if (cur_used_internal_vars && !var->is_cur_inactive_group_selector)
                assume_aux (qdpll, -id);
              else
                assume_aux (qdpll, id);
            }
        }
    }
}


/* Depending on currently and previously used internal IDs, set the respective
   variables so that clauses associated to popped off frames are satisfied and
   hence are actually disabled. All internal variables always appear positively
   in clauses, hence we set them to true to disable the clauses. */
static void
assign_frame_selector_variables (QDPLL *qdpll)
{
  assign_frame_selector_vars_aux (qdpll, &qdpll->state.cur_used_internal_vars, 1);
  assign_frame_selector_vars_aux (qdpll, &qdpll->state.popped_off_internal_vars, 0);
}


static void
check_and_import_cover_sets (QDPLL *qdpll)
{
  if (qdpll->options.verbosity >= 1)
    fprintf (stderr, "Start: check and import %d cover sets, %d newly added clauses.\n", 
             qdpll->cover_sets.cnt, qdpll->state.clauses_added_since_cube_check);

  QDPLL_ABORT_QDPLL (qdpll->cover_sets.cnt > qdpll->state.lcubes_size, 
                     "Unexpected number of cover sets.");

  unsigned int original_cnt = qdpll->cover_sets.cnt;
  unsigned int imported = 0;

  const unsigned int table_size = qdpll->pcnf.size_vars + 1;
  char * assignment_by_cover_set = (char *) qdpll_malloc (qdpll->mm, table_size * sizeof(char));

  /* Check all collected cover sets. */
  Constraint *c, *n;
  for (c = qdpll->cover_sets.first; c; c = n)
    {
      n = c->link.next;
      /* Store assignment represented by cover set in auxiliary assignment table. */

      if (qdpll->options.verbosity >= 2)
        {
          fprintf (stderr, "Checking cover set: ");
          print_constraint (qdpll, c);
        }

      memset (assignment_by_cover_set, 0, table_size * sizeof(char));

      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        {
          LitID lit = *p;
          Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
          assert (QDPLL_VAR_HAS_OCCS(var));
          if (QDPLL_LIT_POS(lit))
            assignment_by_cover_set[var->id] = QDPLL_ASSIGNMENT_TRUE;
          else
            assignment_by_cover_set[var->id] = QDPLL_ASSIGNMENT_FALSE;
        }

      /* Check if cube assignment satisfies each newly added clause in the
         current CNF. */
      unsigned int cnt = qdpll->state.clauses_added_since_cube_check; 
      QDPLL_ABORT_QDPLL ((cnt == 0 || cnt > qdpll->pcnf.clauses.cnt), 
                         "Unexpected value of 'clauses_added_since_cube_check'.");

      Constraint *cl;
      for (cl = qdpll->pcnf.clauses.last; cnt; cnt--, cl = cl->link.prev)
        {
          assert (cl);
          /* Since we start at end of clause list and new clauses are added at
             the end, we cannot see satisfied clauses (at this point clauses
             could be satisfied only by selector variables of popped off
             frames.) */
          assert (!is_clause_satisfied (qdpll, cl));
          LitID *p, *e;
          for (p = cl->lits, e = p + cl->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
              if ((QDPLL_LIT_POS(lit) && assignment_by_cover_set[var->id] == QDPLL_ASSIGNMENT_TRUE) || 
                  (QDPLL_LIT_NEG(lit) && assignment_by_cover_set[var->id] == QDPLL_ASSIGNMENT_FALSE))
                break;
            }
          /* Here, 'p != e' iff the clause is satisfied by the cover set. If
             'p == e' then the clause is not satisfied and hence the cover set
             must not be imported. */
          if (p == e)
            break;
        }
      assert (!cnt || cl);

      UNLINK (qdpll->cover_sets, c, link);

      if (cnt)
        {
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "Cover set does not cover clause: ");
              print_constraint (qdpll, cl);
            }
          delete_constraint (qdpll, c);
        }
      else
        {
          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "Cover set covers all clauses: ");
              print_constraint (qdpll, c);
            }

          /* Keep copy of cover set in list for upcoming. */
          Constraint *cover_set_copy = create_constraint (qdpll, c->num_lits, 1);
          memcpy (cover_set_copy->lits, c->lits, c->num_lits * sizeof (LitID));
          assert (cover_set_copy->is_cube);
          cover_set_copy->learnt = 1;
          /* If the list of cover sets is full then delete the least-recently added cover set.*/
          if (qdpll->cover_sets.cnt == COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size)
            store_cover_set_aux (qdpll);
          LINK_FIRST (qdpll->cover_sets, cover_set_copy, link);
          assert (qdpll->cover_sets.cnt <= COLLECT_FULL_COVER_SETS_MULT_LIMIT * qdpll->state.lcubes_size);

          /* Import cover set only if limit of learned cubes has not been
             exceeded. */
          if (qdpll->pcnf.learnt_cubes.cnt < qdpll->state.lcubes_size)
            {
              if (qdpll->options.verbosity >= 2)
                fprintf (stderr, "Importing cover set.\n");
              assert (c->is_cube);
              assert (c->learnt);
#ifndef NDEBUG
              assert_lits_sorted (qdpll, c->lits, c->lits + c->num_lits);
#endif
              top_level_reduce_constraint_simple (qdpll, c, QDPLL_QTYPE_FORALL);
              LINK_FIRST (qdpll->pcnf.learnt_cubes, c, link);
              imported++;
            }
          else
            {
              if (qdpll->options.verbosity >= 2)
                fprintf (stderr, "Discarding cover set, cube limit reached.\n");
              delete_constraint (qdpll, c);
            }
        }
    }

  qdpll_free (qdpll->mm, assignment_by_cover_set, table_size * sizeof(char));

  if (qdpll->options.verbosity >= 1)
    fprintf (stderr, "End: check and import cover sets, %d cover sets remaining, imported %d of original %d ( %f ).\n", 
             qdpll->cover_sets.cnt, imported, original_cnt, original_cnt ? (imported / (float)original_cnt) : 0);
}


static void
discard_all_learned_cubes (QDPLL *qdpll)
{
  if (qdpll->options.verbosity >= 1)
    fprintf (stderr, "Incremental solving cube check: discarding all %d learned cubes.\n", 
             qdpll->pcnf.learnt_cubes.cnt);
  /* Discard all learned cubes. */
  check_resize_learnt_constraints_aux (qdpll, &qdpll->pcnf.learnt_cubes, 
                                       UINT_MAX, QDPLL_QTYPE_FORALL);
}


static void
discard_all_collected_cover_sets (QDPLL *qdpll)
{
  if (qdpll->options.verbosity >= 1)
    fprintf (stderr, "Incremental solving cube check: discarding all %d collected cover sets.\n", 
             qdpll->cover_sets.cnt);

  Constraint *c, *n;
  for (c = qdpll->cover_sets.first; c; c = n)
    {
      n = c->link.next;
      UNLINK (qdpll->cover_sets, c, link);
      delete_constraint (qdpll, c);
    }
}


static void
check_and_delete_cubes_incremental (QDPLL *qdpll)
{
  discard_all_learned_cubes (qdpll);

  QDPLL_ABORT_QDPLL (!qdpll->state.pending_cubes_check, 
                     "Unexpected call of cube checking.");
  QDPLL_ABORT_QDPLL (qdpll->state.clauses_added_since_cube_check == 0, 
                     "Unexpected call of cube checking.");

  if (qdpll->state.collect_full_cover_sets)
    check_and_import_cover_sets (qdpll);

  /* The flag 'qdpll->state.pending_cubes_check' is set to true 
     each time a new clause is added. */
  qdpll->state.pending_cubes_check = 0;
  qdpll->state.clauses_added_since_cube_check = 0;
}


static LitID
find_selector_literal (QDPLL *qdpll, Constraint *c)
{
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->is_internal)
        return lit;
    }
  return 0;
}


static unsigned int
count_selector_literals (QDPLL *qdpll, Constraint *c)
{
  unsigned int result = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->is_internal)
        result++;
    }
  return result;
}


/* Delete clauses containing popped off variables. These clauses are always
   satisfied by the popped off variables. */
static void
cleanup_popped_off_clauses (QDPLL *qdpll, ConstraintList *clauses, const int orig_clauses)
{
  ConstraintPtrStack clauses_to_be_deleted;
  QDPLL_INIT_STACK(clauses_to_be_deleted);
  VarPtrStack occ_list_sweep_vars;
  QDPLL_INIT_STACK(occ_list_sweep_vars);

  Constraint *c, *n;
  for (c = clauses->first; c; c = n)
    {
      n = c->link.next;
#ifndef NDEBUG
      assert_lits_sorted (qdpll, c->lits, c->lits + c->num_lits);
#endif
      assert (!c->is_cube);
      assert (!orig_clauses || !c->learnt);
      assert (orig_clauses || c->learnt);
      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        {
          LitID lit = *p;
          Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
          if (var->mark0)
            {
              if (qdpll->options.verbosity >= 2)
                {
                  fprintf (stderr, "Deleting popped off clause:");
                  print_constraint (qdpll, c);
                }

              assert (var->is_internal);
              if (orig_clauses)
                {
                  assert (!c->deleted);
                  c->deleted = 1;
                  QDPLL_PUSH_STACK(qdpll->mm, clauses_to_be_deleted, c);
                }
              else
                {
                  UNLINK (*clauses, c, link);
                  delete_constraint (qdpll, c);
                }
              break;
            }
        }
    }

  if (orig_clauses)
    {
      while (!QDPLL_EMPTY_STACK(clauses_to_be_deleted))
        {
          c = QDPLL_POP_STACK(clauses_to_be_deleted);
          assert (c->deleted);
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
              /* Remove pointer to 'c' from occ-lists. */
              if (var->is_internal)
                {
                  assert (var->mark0);
                  assert (!QDPLL_VAR_HAS_NEG_OCCS(var));
                  cleanup_constraint_sweep_occs (qdpll, &(var->pos_occ_clauses));
                }
              else if (QDPLL_LIT_NEG(lit))
                {
                  if (!var->mark0)
                    {
                      /* Mark negative sweep done. */
                      cleanup_constraint_sweep_occs (qdpll, &(var->neg_occ_clauses));
                      var->mark0 = 1;
                      if (!var->mark1)
                        QDPLL_PUSH_STACK(qdpll->mm, occ_list_sweep_vars, var);
                    }
                }
              else
                {
                  assert (QDPLL_LIT_POS(lit));
                  if (!var->mark1)
                    {
                      /* Mark positive sweep done. */
                      cleanup_constraint_sweep_occs (qdpll, &(var->pos_occ_clauses));
                      var->mark1 = 1;
                      if (!var->mark0)
                        QDPLL_PUSH_STACK(qdpll->mm, occ_list_sweep_vars, var);
                    }
                }
            }
          UNLINK (*clauses, c, link);
          delete_constraint (qdpll, c);
        }

      /* Unmark swept variables. */
      while (!QDPLL_EMPTY_STACK(occ_list_sweep_vars))
        {
          Var *var = QDPLL_POP_STACK(occ_list_sweep_vars);
          assert (var->mark0 || var->mark1);
          var->mark0 = var->mark1 = 0;
        }
    }

  QDPLL_DELETE_STACK(qdpll->mm, occ_list_sweep_vars);
  QDPLL_DELETE_STACK(qdpll->mm, clauses_to_be_deleted);
}


static void
cleanup_popped_off_cubes_aux (QDPLL *qdpll, Constraint *cube, 
                              LitIDStack *remaining_lits_sorted)
{
  assert (QDPLL_EMPTY_STACK (*remaining_lits_sorted));

  LitID *p, *e;
  for (p = cube->lits, e = p + cube->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      /* If a cube was learned under deactivation of clause groups: a cube may
         contain internal literals which either have been popped off or which are
         still on stack 'qdpll->state.cur_used_internal_vars'. However, only
         variables which were popped off must be deleted from cubes since these
         variables are actually deleted. Variables on stack
         'qdpll->state.cur_used_internal_vars' must be kept in the cube.  */
      assert (!var->mark0 || var->is_internal);
      assert (!var->mark0 || !var->is_cur_used_internal_var);
      assert ((var->mark0 || !var->is_internal) || var->is_cur_used_internal_var);
      /* Collect the literals which remain in the cube after cleanup,
         i.e. literals of variables which have not been marked to be deleted. */
      if (!var->mark0 && QDPLL_VAR_HAS_OCCS(var))
        QDPLL_PUSH_STACK(qdpll->mm, *remaining_lits_sorted, lit);
    }

  /* Avoid needless work if no literal was deleted. */
  if (QDPLL_COUNT_STACK(*remaining_lits_sorted) < cube->num_lits)
    {
      /* Store remaining literals in 'c', in sorted order as they were collected. */
      LitID *dest = cube->lits;
      for (p = remaining_lits_sorted->start, e = remaining_lits_sorted->top; p < e; p++)
        {
          assert (dest < cube->lits + cube->num_lits);
          assert (QDPLL_VAR_HAS_OCCS(LIT2VARPTR(qdpll->pcnf.vars, *p)));
          *dest++ = *p;
        }
      cube->num_lits = QDPLL_COUNT_STACK(*remaining_lits_sorted);
    }
}


/* Delete literals of popped off variables from cubes. This is sound because
   we also delete clauses containing such literals. These clauses are always
   satisfied by the popped off variables. 
   The last parameter indicates whether we do existential reduction or not. We do
   it for learned cubes but NOT for collected cover sets. Otherwise, these
   reduced cover sets will likely never satisfy the whole CNF any more. */
static void
cleanup_popped_off_cubes (QDPLL *qdpll, ConstraintList *cubes, const int do_exist_red)
{
  LitIDStack remaining_lits_sorted;
  QDPLL_INIT_STACK (remaining_lits_sorted);

  Constraint *c;
  for (c = cubes->first; c; c = c->link.next)
    {
      assert (c->is_cube);
      QDPLL_RESET_STACK(remaining_lits_sorted);
      cleanup_popped_off_cubes_aux (qdpll, c, &remaining_lits_sorted);
      /* We might have deleted a universal variable from 'c', hence must carry
         out existential reduction. */
      if (do_exist_red)
        top_level_reduce_constraint_simple (qdpll, c, QDPLL_QTYPE_FORALL);
    }

  QDPLL_DELETE_STACK (qdpll->mm, remaining_lits_sorted);
}


static void
cleanup_popped_off_vars_from_default_scope (QDPLL *qdpll)
{
  VarID *p, *e;
  for (p = qdpll->pcnf.scopes.first->vars.start, 
         e = qdpll->pcnf.scopes.first->vars.top; p < e; p++)
    {
      VarID id = *p;
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      if (var->mark0)
        {
          *p = QDPLL_POP_STACK(qdpll->pcnf.scopes.first->vars);
          p--;
          e--;
        }
    }
}


static void
cleanup_popped_off_vars (QDPLL *qdpll)
{
#ifndef NDEBUG
  do {
    Var *p, *e;
    for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
      {
        assert (!p->mark0);
        assert (!p->mark1);
      }
  } while (0);
#endif

  /* Mark popped off variables for later cleanup of learned
     constraints. */
  VarID *p, *e;
  for (p = qdpll->state.popped_off_internal_vars.start, 
         e = qdpll->state.popped_off_internal_vars.top; p < e; p++)
    {
      VarID id = *p;
      assert (id);
      assert (id >= qdpll->pcnf.size_user_vars);
      assert (id < qdpll->pcnf.size_vars);
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      /* NOTE: we also mark no-occ variables with 'var->id == 0' (can be due
         to empty frames added by the user.) */
      assert (!var->id || var->is_internal);
      assert (!var->id || !var->is_cur_used_internal_var);
      assert (!var->id || !var->is_cur_inactive_group_selector);
      assert (!var->mark0);
      var->mark0 = 1;
    }

  /* Clean up clauses with occurrences of popped off variables. */
  cleanup_popped_off_clauses (qdpll, &qdpll->pcnf.clauses, 1);
  if (!qdpll->options.no_empty_formula_watching)
    {
      /* Update BLitsOccs for empty formula watching. Original clauses may have
         been deleted. */
      update_empty_formula_watcher_toggle_var_marks (qdpll, qdpll->empty_formula_watcher, 0);
      qdpll->empty_formula_watcher = 0;
      qdpll->state.empty_formula_watcher_scheduled_update = 1;
      QDPLL_RESET_STACK (qdpll->empty_formula_watching_blit_occs);
      Constraint *c;
      for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
        {
          assert (c->num_lits > 0);
          assert (c->lits[0]);
          BLitsOcc occ = {c->lits[0], c};
          QDPLL_PUSH_STACK (qdpll->mm, qdpll->empty_formula_watching_blit_occs, occ);
        }
      assert (qdpll->pcnf.clauses.cnt == 
              (unsigned int) QDPLL_COUNT_STACK (qdpll->empty_formula_watching_blit_occs));
    }
  cleanup_popped_off_clauses (qdpll, &qdpll->pcnf.learnt_clauses, 0);

  /* Clean up cubes with occurrences of popped off variables. */
  cleanup_popped_off_cubes (qdpll, &qdpll->pcnf.learnt_cubes, 1);
  cleanup_popped_off_cubes (qdpll, &qdpll->cover_sets, 0);

  /* Remove popped off variable from default scope. */
  cleanup_popped_off_vars_from_default_scope (qdpll);

  /* Clean up popped off variables on priority queue. */
  for (p = qdpll->state.popped_off_internal_vars.start, 
         e = qdpll->state.popped_off_internal_vars.top; p < e; p++)
    {
      VarID id = *p;
      assert (id);
      assert (id >= qdpll->pcnf.size_user_vars);
      assert (id < qdpll->pcnf.size_vars);
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      QDPLL_RESET_STACK(var->neg_occ_clauses); 
      QDPLL_RESET_STACK(var->pos_occ_clauses); 
      assert (var->mark0);
      if (var->id)
        {
          assert (var->is_internal);
          if (var->priority_pos != QDPLL_INVALID_PQUEUE_POS)
            var_pqueue_remove_elem (qdpll, var->priority_pos);
          reset_variable (qdpll, var);
        }
      var->mark0 = 0;
    }

  QDPLL_RESET_STACK(qdpll->state.popped_off_internal_vars);

  qdpll->state.popped_off_orig_clause_cnt = 0;

#ifndef NDEBUG
  do {
    Var *p, *e;
    for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
      {
        assert (!p->mark0);
        assert (!p->mark1);
      }
  } while (0);
#endif
}

static void
qbcp_qbce_reset_data_structures (QDPLL *qdpll);

static void
qbcp_qbce_init_data_structures (QDPLL *qdpll);


static void
qdpll_gc_aux (QDPLL *qdpll, const int called_by_user)
{
  QDPLL_ABORT_QDPLL (!qdpll->state.assumptions_given && count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  if (qdpll->options.verbosity >= 1 && qdpll->state.popped_off_orig_clause_cnt > 0)
    fprintf (stderr, "Cleanup %d popped off clauses, %d original clauses.\n", 
             qdpll->state.popped_off_orig_clause_cnt, qdpll->pcnf.clauses.cnt);

  /* With incremental mode and QBCE variants, must reset and
     re-init QBCE data structures. */
  unsigned int qbce_reset = 0;
  if (qdpll->options.incremental_use && 
      (qdpll->options.qbce_preprocessing || 
       qdpll->options.qbce_inprocessing || 
       !qdpll->options.no_qbce_dynamic))
    {
      /* Avoid resetting if there is nothing to be cleaned up in
         'cleanup_popped_off_vars'. */
      if (QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0)
        {
          qbcp_qbce_reset_data_structures (qdpll);
          qbce_reset = 1;
        }
    }

  cleanup_popped_off_vars (qdpll);

  /* Fix: must import user-given variables (if necessary), because otherwise
     they will not be deleted. The deletion function for no-occ-vars in
     'clean_up_formula' goes over INTERNAL scopes only. Hence variables will not
     be deleted if they do not appear on internal scope. */
  if (called_by_user)
    import_user_scopes (qdpll);

  /* Deleting popped variables and clauses. Further, cleanup user variables
     which have NO occurrences and remove empty user scopes. */
  clean_up_formula (qdpll, called_by_user);
  assert (qdpll->state.popped_off_orig_clause_cnt == 0);
  assert (QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) == 0);

  if (qdpll->options.incremental_use && 
      (qdpll->options.qbce_preprocessing || 
       qdpll->options.qbce_inprocessing || 
       !qdpll->options.no_qbce_dynamic))
    {
      /* Avoid initializing if there is nothing to be cleaned up in
         'cleanup_popped_off_vars'. */
      if (qbce_reset)
        qbcp_qbce_init_data_structures (qdpll);
    }
}

static void
assign_user_given_assumptions (QDPLL *qdpll)
{
  LitID *p, *e;
  for (p = qdpll->user_given_assumptions.start, 
         e = qdpll->user_given_assumptions.top;
       p < e; p++)
    {
      LitID assumption = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, assumption);
      QDPLL_ABORT_QDPLL(QDPLL_VAR_ASSIGNED(var), "must not assume variable multiple times!");
      /* Assign a variable as assumption only if it does occur in clauses. */
      if (QDPLL_VAR_HAS_OCCS (var))
        assume_aux (qdpll, assumption);
    }

  QDPLL_RESET_STACK(qdpll->user_given_assumptions); 
}

/* Check existential literals in 'blocked_clause' and reschedule pairs of
   'blocked_clause' and existential literal for QBCE if these existential
   currently do not have a witness set. This is necessary since a clause may be
   blocked by QBCE preprocessing, after which QBCE aborts and witnesses for the
   remaining existentials in the clause are not computed. */
static void
qbcp_qbce_reschedule_for_missing_witnesses (QDPLL *qdpll, 
                                                 Constraint *blocked_clause, 
                                                 LitID blocking_lit)
{
  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, " rescheduling for missing witnesses\n");
  /* Mark literals which have a witness set for 'blocking_clause'. */
  QBCENonBlockedWitness *wp, *we;
  for (wp = blocked_clause->qbcp_qbce_witness_clauses.start, 
         we = blocked_clause->qbcp_qbce_witness_clauses.top; 
       wp < we; wp++)
    {
      QBCENonBlockedWitness witness_pair = *wp;
      assert (witness_pair.non_blocking_lit);
      Var *blocking_var = LIT2VARPTR 
        (qdpll->pcnf.vars, witness_pair.non_blocking_lit);
      assert (!QDPLL_VAR_MARKED (blocking_var));
      QDPLL_VAR_POS_MARK (blocking_var);
    }

  LitID *p, *e;
  for (p = blocked_clause->lits, e = p + blocked_clause->num_lits; 
       p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      /* Check all existential literals in 'blocked_clause' but ignore
         'blocking_literal'. */
      if (lit != blocking_lit && !var->is_internal && QDPLL_VAR_EXISTS (var))
        {
          /* If 'lit' does not have a witness then reschedule. Otherwise
             unmark variable on the fly. */
          if (!QDPLL_VAR_POS_MARKED (var))
            {
              QBCENonBlockedWitness pair = {lit, 
                                            {blocked_clause->num_lits > 0 ? 
                                             blocked_clause->lits[0] : 0, blocked_clause}, 
                                            {QDPLL_INVALID_WATCHER_POS}, 
                                            QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses)};
              /* Reschedule pair. Note that we push directly to
                 'qdpll->qbcp_qbce_maybe_blocked_clauses' to avoid pusing pairs
                 containing the same clause on the auxiliary stack used to track
                 depending blocked clauses. */
              QDPLL_PUSH_STACK(qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, pair);
              if (qdpll->options.verbosity >= 2)
                {
                  fprintf (stderr, "  rescheduled blocking lit %d and clause: ", lit);
                  print_constraint (qdpll, blocked_clause);
                }
            }
          else
            {
              /* 'lit' has a witness then reschedule if witness is blocked. */
              QBCENonBlockedWitness *old_witness_pair_p = qbcp_qbce_find_lit_in_list 
                (qdpll, &(blocked_clause->qbcp_qbce_witness_clauses), lit);
              assert (old_witness_pair_p);
              unsigned int witness_offset = old_witness_pair_p - 
                blocked_clause->qbcp_qbce_witness_clauses.start;
              QBCENonBlockedWitness witness_pair = 
                blocked_clause->qbcp_qbce_witness_clauses.start[witness_offset];
              if (witness_pair.blit_occ.constraint->qbcp_qbce_blocked)
                {
                  /* Must set 'offset_in_working_queue' also for entry of clause in notify list. */
                  witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start
                    [witness_pair.offset.maybe_blocked_clause_in_notify_list].offset_in_working_queue = 
                    QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
                  QBCENonBlockedWitness pair = {lit, 
                                                {blocked_clause->num_lits > 0 ? 
                                                 blocked_clause->lits[0] : 0, blocked_clause}, 
                                                {witness_offset}, 
                                                QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses)};
                  QDPLL_PUSH_STACK(qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, pair);
                  if (qdpll->options.verbosity >= 2)
                    {
                      fprintf (stderr, "  blocked witness -- rescheduled blocking lit %d and clause: ", lit);
                      print_constraint (qdpll, blocked_clause);
                    }
                }
            }
        }
      QDPLL_VAR_POS_UNMARK (var);
    }

#ifndef NDEBUG
  /* Check that variables have been properly unmarked. */
  for (wp = blocked_clause->qbcp_qbce_witness_clauses.start, 
         we = blocked_clause->qbcp_qbce_witness_clauses.top; 
       wp < we; wp++)
    {
      QBCENonBlockedWitness witness_pair = *wp;
      assert (witness_pair.non_blocking_lit);
      Var *blocking_var = LIT2VARPTR 
        (qdpll->pcnf.vars, witness_pair.non_blocking_lit);
      assert (!QDPLL_VAR_MARKED (blocking_var));
    }
#endif
}

static void
qbcp_qbce_collect_clauses_to_be_rescheduled (QDPLL *qdpll, 
                                             ConstraintPtrStack *clauses, 
                                             QBCENonBlockedWitnessStack *stack)
{
  Constraint **cp, **ce;
  for (cp = clauses->start, ce = clauses->top; cp < ce; cp++)
    {
      Constraint *blocked_clause = *cp;
      /* Use 'qbcp_qbce_blocked' mark of clauses to prevent double pushing. */
      if (blocked_clause->qbcp_qbce_blocked)
        {
          assert (blocked_clause->qbcp_qbce_blocking_lit);

          if (qdpll->options.verbosity >= 2)
            {
              fprintf (stderr, "Collecting to reschedule blocking lit %d and clause: ", 
                       blocked_clause->qbcp_qbce_blocking_lit);
              print_constraint (qdpll, blocked_clause);
            }
          /* Must make sure that previously stored witness is removed later. A
             witness may be stored even if the clause was found blocked because
             we do not remove stored witnesses if a clause later becomes
             blocked. */
          QBCENonBlockedWitness *old_witness_pair_p = qbcp_qbce_find_lit_in_list 
            (qdpll, &(blocked_clause->qbcp_qbce_witness_clauses), blocked_clause->qbcp_qbce_blocking_lit);
          unsigned int witness_offset = QDPLL_INVALID_WATCHER_POS;
          if (old_witness_pair_p)
            { 
              witness_offset = old_witness_pair_p - blocked_clause->qbcp_qbce_witness_clauses.start;
              QBCENonBlockedWitness witness_pair = blocked_clause->qbcp_qbce_witness_clauses.start[witness_offset];
              /* Must set 'offset_in_working_queue' also for entry of clause in notify list. */
              witness_pair.blit_occ.constraint->qbcp_qbce_notify_maybe_blocked_clauses.start
                [witness_pair.offset.maybe_blocked_clause_in_notify_list].offset_in_working_queue = 
                QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
            }
          QBCENonBlockedWitness pair = {blocked_clause->qbcp_qbce_blocking_lit, 
                                        {blocked_clause->num_lits > 0 ? 
                                         blocked_clause->lits[0] : 0, blocked_clause}, 
                                        {witness_offset}, 
                                        QDPLL_COUNT_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses)};
          QDPLL_PUSH_STACK (qdpll->mm, *stack, pair);
          qbcp_qbce_reschedule_for_missing_witnesses (qdpll, blocked_clause, 
                                                      blocked_clause->qbcp_qbce_blocking_lit);
          blocked_clause->qbcp_qbce_blocked = 0;
          blocked_clause->qbcp_qbce_blocking_lit = 0;
        }
      else
        assert (!blocked_clause->qbcp_qbce_blocking_lit);
    }
}

static void
qbcp_qbce_check_blocked_clauses_after_clause_addition (QDPLL *qdpll)
{
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 1);
  assert (qdpll->state.decision_level == 0);

  QBCENonBlockedWitnessStack clauses_to_be_rescheduled;
  QDPLL_INIT_STACK (clauses_to_be_rescheduled);

  /* Collect clauses to be rescheduled based on all variables which appear in
     newly added input clauses AND which have occurrences containing blocking literals. */
  VarID *vp, *ve;
  for (vp = qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses.start, 
         ve = qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses.top; vp < ve; vp++)
    {
      VarID vid = *vp;
      Var *var_in_input_clause = VARID2VARPTR (qdpll->pcnf.vars, vid);
      assert (var_in_input_clause->neg_lit_in_new_input_clause || 
              var_in_input_clause->pos_lit_in_new_input_clause);
      assert (QDPLL_COUNT_STACK (var_in_input_clause->
                                 qbcp_qbce_prepro_neg_blocking_lit_clauses) != 0 ||
              QDPLL_COUNT_STACK (var_in_input_clause->
                                 qbcp_qbce_prepro_pos_blocking_lit_clauses) != 0);
      ConstraintPtrStack *blocked_occs;
      if (var_in_input_clause->neg_lit_in_new_input_clause)
        {
          qbcp_qbce_collect_clauses_to_be_rescheduled 
            (qdpll, &var_in_input_clause->qbcp_qbce_prepro_pos_blocking_lit_clauses, 
             &clauses_to_be_rescheduled);
          QDPLL_RESET_STACK (var_in_input_clause->qbcp_qbce_prepro_pos_blocking_lit_clauses);
        }
      if (var_in_input_clause->pos_lit_in_new_input_clause)
        {
          qbcp_qbce_collect_clauses_to_be_rescheduled 
            (qdpll, &var_in_input_clause->qbcp_qbce_prepro_neg_blocking_lit_clauses, 
             &clauses_to_be_rescheduled);
          QDPLL_RESET_STACK (var_in_input_clause->qbcp_qbce_prepro_neg_blocking_lit_clauses);
        }
      var_in_input_clause->neg_lit_in_new_input_clause = 
        var_in_input_clause->pos_lit_in_new_input_clause = 0;
    }
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses);

  /* Reschedule collected clauses and reschedule clauses which are blocked due
     to one of the rescheduled clauses. */

  QBCENonBlockedWitness pair;
  while (!QDPLL_EMPTY_STACK (clauses_to_be_rescheduled))
    {
      pair = QDPLL_POP_STACK (clauses_to_be_rescheduled);
      Constraint *rescheduled_clause = pair.blit_occ.constraint;
      /* Marks must have been reset at the time of collecting clauses to be
         rescheduled. */
      assert (!rescheduled_clause->qbcp_qbce_blocked);
      assert (!rescheduled_clause->qbcp_qbce_blocking_lit);
      /* Reschedule pair. */
      QDPLL_PUSH_STACK(qdpll->mm, qdpll->qbcp_qbce_maybe_blocked_clauses, pair);
      if (qdpll->options.verbosity >= 2)
        {
          fprintf (stderr, "Rescheduled blocking lit %d and clause: ", 
                   pair.non_blocking_lit);
          print_constraint (qdpll, rescheduled_clause);
        }
      LitID *p, *e;
      for (p = rescheduled_clause->lits, e = p + rescheduled_clause->num_lits; 
           p < e; p++)
        {
          LitID lit = *p;
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          /* If var appeared in input clause, then it has been checked already
             in loop above. */
          assert (!var->neg_lit_in_new_input_clause);
          assert (!var->pos_lit_in_new_input_clause);
          if (QDPLL_VAR_EXISTS (var))
            {
              if (QDPLL_LIT_NEG (lit))
                {
                  qbcp_qbce_collect_clauses_to_be_rescheduled 
                    (qdpll, &var->qbcp_qbce_prepro_pos_blocking_lit_clauses, 
                     &clauses_to_be_rescheduled);
                  QDPLL_RESET_STACK (var->qbcp_qbce_prepro_pos_blocking_lit_clauses);
                }
              else
                {
                  assert (QDPLL_LIT_POS (lit));
                  qbcp_qbce_collect_clauses_to_be_rescheduled 
                    (qdpll, &var->qbcp_qbce_prepro_neg_blocking_lit_clauses, 
                     &clauses_to_be_rescheduled);
                  QDPLL_RESET_STACK (var->qbcp_qbce_prepro_neg_blocking_lit_clauses);
                }
            }
        }
    }

  ConstraintPtrStack new;
  QDPLL_INIT_STACK (new);

  /* Traverse clauses blocked by preprocessing and remove those which were
     rescheduled. */
  Constraint **p, **e;
  for (p = qdpll->qbcp_qbce_blocked_clauses.start[0].start, 
         e = qdpll->qbcp_qbce_blocked_clauses.start[0].top; p < e; p++)
    {
      Constraint *c = *p;
      if (c->qbcp_qbce_blocked)
        {
          /* Clause is still blocked. */
          assert (c->qbcp_qbce_blocking_lit);
          QDPLL_PUSH_STACK (qdpll->mm, new, c);
        }
      else
        assert (!c->qbcp_qbce_blocking_lit);
    }

  ConstraintPtrStack tmp = qdpll->qbcp_qbce_blocked_clauses.start[0];
  qdpll->qbcp_qbce_blocked_clauses.start[0] = new;

  QDPLL_DELETE_STACK (qdpll->mm, clauses_to_be_rescheduled);
  QDPLL_DELETE_STACK (qdpll->mm, tmp);

#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_current_blocked_clauses = 
    QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]);
#endif
}

/* Call dynamic QBCE for the first time before actual solving as
   preprocessing. Additionally, in incremental mode, check if there
   are any blocked clauses that need to be rescheduled for the
   blocked-checked.
   NOTE: this call assumes that QBCE data structures have been
   properly set up before, e.g. see function
   'import_original_clause'. */
static void
qbcp_qbce_first_call_before_solving (QDPLL *qdpll)
{
  if (qdpll->options.qbce_preprocessing || 
      qdpll->options.qbce_inprocessing || 
      !qdpll->options.no_qbce_dynamic)
    {
      if (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]))
        {
          qbcp_qbce_check_blocked_clauses_after_clause_addition (qdpll);
        }
      
      /* Call QBCE here BEFORE watcher initialization to avoid watching blocked
         clauses. Pairs of clauses and maybe blocking
         literals have been pushed on the working queue in
         'import_original_constraint'. */
      assert (!qdpll->state.qbcp_qbce_currently_preprocessing);
      qdpll->state.qbcp_qbce_currently_preprocessing = 1;
      qbcp_qbce_find_blocked_clauses (qdpll);
      qdpll->state.qbcp_qbce_currently_preprocessing = 0;
      assert (qdpll->state.decision_level == 0);
      assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 1);
      qbcp_qbce_init_stack_of_stacks_of_next_dec_level 
        (qdpll, &qdpll->qbcp_qbce_blocked_clauses);
      assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 2);
      assert (!QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[1])); 
      assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 1);
      /* No clause must be QBCE-marked at start of solving. */
      assert (!QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses.start[0])); 
    }
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses) == 0);
}

/* Reset ALL data structures related to QBCE. This is necessary only
   in incremental mode before the formula is cleaned up dynamically
   (removing deleted clauses). */
static void
qbcp_qbce_reset_data_structures (QDPLL *qdpll)
{
  if (qdpll->options.verbosity >= 3)
    fprintf (stderr, "Resetting QBCE data structures before cleaning up popped-off variables\n");

  /* Data structures in solver object. */
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
  assert (qdpll->state.decision_level == 0);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 1);
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 1);
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_marked_clauses.start[0]);
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses);

  /* Data structures in constraint objects. */
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      c->qbcp_qbce_multi_purpose_mark = 0;
      c->qbcp_qbce_blocked = 0;
      c->qbcp_qbce_mark = 0;
      c->qbcp_qbce_blocking_lit = 0;
      QDPLL_RESET_STACK (c->qbcp_qbce_notify_maybe_blocked_clauses);
      QDPLL_RESET_STACK (c->qbcp_qbce_witness_clauses);
      QDPLL_RESET_STACK (c->qbcp_qbce_offset_of_witness_in_watched_occs);
    }

  /* Data structures in variable objects. */
  Var *v, *ve;
  for (v = qdpll->pcnf.vars, ve = qdpll->pcnf.vars + qdpll->pcnf.size_vars; v < ve; v++)
    {
      QDPLL_RESET_STACK (v->qbcp_qbce_offset_of_neg_lit_in_watched_occ);
      QDPLL_RESET_STACK (v->qbcp_qbce_offset_of_pos_lit_in_watched_occ);
      QDPLL_RESET_STACK (v->qbcp_qbce_watched_neg_occ_clauses);
      QDPLL_RESET_STACK (v->qbcp_qbce_watched_pos_occ_clauses);
      v->longest_pos_occ_size = 0;
      v->longest_neg_occ_size = 0;
      QDPLL_RESET_STACK (v->qbcp_qbce_prepro_pos_blocking_lit_clauses);
      QDPLL_RESET_STACK (v->qbcp_qbce_prepro_neg_blocking_lit_clauses);
      v->pos_lit_in_new_input_clause = 0;
      v->neg_lit_in_new_input_clause = 0;
    }

#if COMPUTE_STATS
  qdpll->stats.qbcp_qbce_current_blocked_clauses = 0;
#endif
}

/* Initialize ALL data structures related to QBCE. Calling this
   function has the same effect as the initialization of QBCE done in
   'import_original_clause', for example. Initializing explicitly is
   necessary only in incremental mode after the formula has been
   cleaned up dynamically (removing deleted clauses). */
static void
qbcp_qbce_init_data_structures (QDPLL *qdpll)
{
  if (qdpll->options.verbosity >= 3)
    fprintf (stderr, "Initializing QBCE data structures after cleaning up popped-off variables\n");

  assert (qdpll->options.qbce_preprocessing || 
          qdpll->options.qbce_inprocessing || 
          !qdpll->options.no_qbce_dynamic);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses));
  assert (!QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]));

  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      assert (!c->is_cube);
      qbcp_qbce_setup_first_call_aux (qdpll, c);
      LitID *p, *end;
      for (p = c->lits, end = p + c->num_lits; p < end; p++)
        {
          LitID lit = *p;
          assert ((VarID) LIT2VARID (lit) < qdpll->pcnf.size_vars);
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          if (QDPLL_LIT_NEG (lit))
            {
              if (c->num_lits > var->longest_neg_occ_size)
                var->longest_neg_occ_size = c->num_lits;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (c->num_lits > var->longest_pos_occ_size)
                var->longest_pos_occ_size = c->num_lits;
            }
        }
    }
}

/* Makes use of PicoSAT failed assumption API. */
static Constraint *
trivial_falsity_try_remove_innermost_existentials (QDPLL *qdpll, 
                                                   Constraint *unsat_branch_clause, 
                                                   unsigned int cnt_universals)
{
  assert (cnt_universals > 0);
  assert (cnt_universals <= unsat_branch_clause->num_lits);
  assert (picosat_res (qdpll->trivial_falsity_solver) == PICOSAT_UNSATISFIABLE);

#ifndef NDEBUG
  {
    LitID *p, *e;
    for (p = unsat_branch_clause->lits, e = p + unsat_branch_clause->size_lits; p < e; p++)
      assert (!LIT2VARPTR (qdpll->pcnf.vars, *p)->mark_tf_redundant);
  }
#endif

#if COMPUTE_STATS
  qdpll->stats.trivial_falsity_remove_inner_existentials_calls++;
#endif

  /* Set pointer to last irredundant existential literal. */
  LitID *last_irred_exist_lit = unsat_branch_clause->lits + 
    unsat_branch_clause->num_lits - 1;
  while (unsat_branch_clause->lits <= last_irred_exist_lit)
    {
      LitID last_lit = *last_irred_exist_lit;
      Var *last_var = LIT2VARPTR (qdpll->pcnf.vars, last_lit);
      /* Initially, all literals in clause are failed assumptions. */
      assert (picosat_failed_assumption (qdpll->trivial_falsity_solver, -last_lit));
      if (QDPLL_VAR_EXISTS (last_var))
        break;
      last_irred_exist_lit--;
    }
#if COMPUTE_STATS
  unsigned int cur_rounds = 0;
#endif
  unsigned int removed_existential = 0;

  /* Try to remove innermost existential literals. Enter a new round if all
     innermost existentials can be removed and then innermost universals are
     removed by universal reduction. */
  unsigned int changed = 1;
  while (changed && cnt_universals > 0/* unsat_branch_clause->lits <= last_irred_exist_lit*/)
    {
#if COMPUTE_STATS
      cur_rounds++;
#endif
      changed = 0;
      LitID *p, *e, lit;
      Var *var;
      /* Check all literals in innermost existential block for removal. */
      for (e = unsat_branch_clause->lits, p = last_irred_exist_lit;
           e <= p && 
             (lit = *p, var = LIT2VARPTR (qdpll->pcnf.vars, lit), 
              QDPLL_VAR_EXISTS(var)) && !var->mark_tf_redundant; p--)
        {
          /* Check if 'lit' can be removed. Assume all other literals and call
             SAT solver again. */
          assert (e == unsat_branch_clause->lits);
          LitID *p2;
          for (p2 = e + unsat_branch_clause->size_lits - 1; e <= p2; p2--)
            {
              LitID lit2 = *p2;
              Var *var2 = LIT2VARPTR (qdpll->pcnf.vars, lit2);
              if (lit2 != lit && 
                  (!var2->mark_tf_redundant || 
                   (QDPLL_VAR_FORALL (var2) && last_irred_exist_lit < p2)))
                picosat_assume (qdpll->trivial_falsity_solver, -lit2);
            }
#if COMPUTE_STATS
          qdpll->stats.trivial_falsity_remove_inner_existentials_sat_calls++;
#endif
          int sat_result = picosat_sat (qdpll->trivial_falsity_solver, 
                                        qdpll->options.trivial_falsity_decision_limit > 0 ? 
                                        (int) qdpll->options.trivial_falsity_decision_limit : -1);
          if (sat_result == PICOSAT_UNSATISFIABLE)
            {
#if COMPUTE_STATS
              qdpll->stats.trivial_falsity_remove_inner_existentials_removed++;
#endif
              removed_existential = 1;
              /* Set redundancy flag of variable of 'lit'. */
              var->mark_tf_redundant = 1;   
              /* Mark all redundant literals in clause up to
                 'last_irred_exist_lit' (literals to the right of
                 'last_irred_exist_lit' are either reducible universals or
                 existentials already marked as redundant) based on non-failed
                 assumptions. */
              LitID *p3;
              for (p3 = last_irred_exist_lit; e <= p3; p3--)
                {
                  LitID lit3 = *p3;
                  Var *var3 = LIT2VARPTR (qdpll->pcnf.vars, lit3);
                  if (!picosat_failed_assumption (qdpll->trivial_falsity_solver, -lit3))
                    {
                      if (!var3->mark_tf_redundant && 
                          QDPLL_VAR_FORALL (var3))
                        {
                          assert (cnt_universals > 0);
                          cnt_universals--;
                        }
                      var3->mark_tf_redundant = 1;
                    }
                }
            }
        }
      /* Update pointer 'last_irred_exist_lit'. */
      while (unsat_branch_clause->lits <= last_irred_exist_lit)
        {
          LitID last_lit = *last_irred_exist_lit;
          Var *last_var = LIT2VARPTR (qdpll->pcnf.vars, last_lit);
          /* Check if we can eliminate universals by reduction. If so then
             enter another round. */
          if (QDPLL_VAR_FORALL (last_var))
            {
              changed = 1;
#if COMPUTE_STATS
              qdpll->stats.trivial_falsity_remove_inner_existentials_reduced_univs++;
#endif
              if (!last_var->mark_tf_redundant)
                {
                  assert (cnt_universals > 0);
                  cnt_universals--;
                }
            }
          else
            if (!last_var->mark_tf_redundant)
              break;
          last_irred_exist_lit--;
        }
    }

#if COMPUTE_STATS
  qdpll->stats.trivial_falsity_remove_inner_existentials_rounds += cur_rounds;
  if (cur_rounds > qdpll->stats.trivial_falsity_remove_inner_existentials_max_rounds)
    qdpll->stats.trivial_falsity_remove_inner_existentials_max_rounds = cur_rounds;
#endif

  if (removed_existential)
    {
      LitIDStack stack_tmp;
      QDPLL_INIT_STACK (stack_tmp);

      /* Copy irredundant literals to auxiliary stack. */
      unsigned int num_lits = 0;
      LitID *p, *e;
      for (p = unsat_branch_clause->lits, e = p + unsat_branch_clause->size_lits; p < e; p++)
        {
          LitID lit = *p;
          Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
          /* Copy also redundant reducible universals. */
          if (!var->mark_tf_redundant || 
              (QDPLL_VAR_FORALL(var) && last_irred_exist_lit < p))
            {
              QDPLL_PUSH_STACK (qdpll->mm, stack_tmp, lit);
              num_lits++;
            }
          var->mark_tf_redundant = 0;
        }

      Constraint * new_unsat_branch_clause = create_constraint (qdpll, num_lits, 0); 
      delete_constraint (qdpll, unsat_branch_clause);
      unsat_branch_clause = new_unsat_branch_clause;

      /* Copy literals from stack. */
      LitID *to = unsat_branch_clause->lits;
      for (p = stack_tmp.start, e = stack_tmp.top; p < e; p++)
        {
          assert (to < unsat_branch_clause->lits + unsat_branch_clause->num_lits);
          *to++ = *p;
        }
      QDPLL_DELETE_STACK (qdpll->mm, stack_tmp);
    }

#ifndef NDEBUG
  assert_lits_sorted (qdpll, unsat_branch_clause->lits, 
                      unsat_branch_clause->lits + unsat_branch_clause->num_lits);
#endif
  top_level_reduce_constraint_simple (qdpll, unsat_branch_clause, 
                                      unsat_branch_clause->is_cube ? 
                                      QDPLL_QTYPE_FORALL : QDPLL_QTYPE_EXISTS);

  return unsat_branch_clause;
}


#ifndef NDEBUG
/* Given a clause learned by trivial falsity, the assignment defined by that
   clause is not necessarily a QCDCL assignment. That is, the variables are not
   necessarily assigned in prefix ordering. HOWEVER, the QBF under that
   assignment must be UNSAT although we skip over outer existential and universal
   variables. */
static void
assert_trivial_falsity_assumption_unsat_test (QDPLL *qdpll, Constraint *trivial_falsity_clause)
{
  QDPLL *test_solver = qdpll_create ();
  qdpll_configure (test_solver, "--dep-man=simple");
  /* must disable trivial falsity calls in 'test_solver' since
     otherwise it will call this function recursively until stack overflow. */
  qdpll_configure (test_solver, "--no-trivial-falsity");
  /* must disable empty formula watching in test solver since
     assertion may fail in 'update_empty_formula_watching' if a clause is
     falsified by having all of its literals set to false. */
  qdpll_configure (test_solver, "--no-empty-formula-watching");

  /* For out-of-order assumptions, move variables to the front of the
     prefix. Otherwise, deriving learned clauses will fail. */
  Nesting cur_nesting = 0, prev_nesting = UINT_MAX;
  LitID *p, *e;
  for (p = trivial_falsity_clause->lits, 
         e = p + trivial_falsity_clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qdpll->pcnf.vars, lit);
      cur_nesting = var->scope->nesting;
      if (cur_nesting != prev_nesting)
        {
          /* Close previously opened scope. */
          if (prev_nesting != UINT_MAX)
            qdpll_add (test_solver, 0);
          /* Open new scope. */
          qdpll_new_scope (test_solver, var->scope->type);
          prev_nesting = cur_nesting;
        }
      qdpll_add (test_solver, var->id);
    }
  /* Close previously opened scope. */
  if (prev_nesting != UINT_MAX)
    qdpll_add (test_solver, 0);

  /* Add prefix without variables in trivial falsity clause. */
  LitID *start = trivial_falsity_clause->lits;
  LitID *end = start + trivial_falsity_clause->num_lits;
  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      if (s->nesting == QDPLL_DEFAULT_SCOPE_NESTING)
        continue;
      qdpll_new_scope (test_solver, s->type);
      VarID *vp, *ve;
      for (vp = s->vars.start, ve = s->vars.top; vp < ve; vp++)
        {
          VarID vid = *vp;
          assert (vid);
          if (!qpup_res_find_lit (start, end, -vid) && 
              !qpup_res_find_lit (start, end, vid))
            qdpll_add (test_solver, vid);
        }
      qdpll_add (test_solver, 0);
    }

  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        qdpll_add (test_solver, *p);
      qdpll_add (test_solver, 0);
    }
    
  /* Assume negation of literals in clause learned by trivial falsity. Note
     that we may skip over variables in the prefix, which however should
     preserve satisfiability. */
  for (p = trivial_falsity_clause->lits, e = p + trivial_falsity_clause->num_lits; p < e; p++)
    qdpll_assume (test_solver, -(*p));

  assert (qdpll_sat (test_solver) == QDPLL_RESULT_UNSAT);

  qdpll_delete (test_solver);
}
#endif

static Constraint *
handle_trivial_falsity (QDPLL *qdpll)
{
  unsigned int cnt, cnt_universals = 0;
  const int *failed_assumptions;
  const int *p;
  if (qdpll->options.verbosity >= 2)
    fprintf (stderr, "TRIVIAL FALSITY at dec-level %d with failed assumptions:\n ", qdpll->state.decision_level);
  cnt = 0;
  failed_assumptions = picosat_failed_assumptions (qdpll->trivial_falsity_solver);
  for (p = failed_assumptions; *p; p++)
    {
      assert ((VarID)LIT2VARID(*p) <= qdpll_get_max_declared_var_id (qdpll));
      cnt++;
      if (QDPLL_VAR_FORALL (LIT2VARPTR (qdpll->pcnf.vars, *p)))
        cnt_universals++;
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "%d ", *p);
    }
  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "0\n");
      fprintf (stderr, "  total %d failed assumptions, %d assigned variables, total variables %d\n", cnt, 
               (int)(qdpll->assigned_vars_top - qdpll->assigned_vars), qdpll->pcnf.used_vars);
    }

#if COMPUTE_STATS
  qdpll->stats.trivial_falsity_assumptions_failed += cnt;
#endif

  Constraint *unsat_branch_clause = create_constraint (qdpll, cnt, 0);
  LitID *litp = unsat_branch_clause->lits;
  for (p = failed_assumptions; *p; p++)
    {
      assert ((VarID)LIT2VARID(*p) <= qdpll_get_max_declared_var_id (qdpll));
      *litp++ = -*p;
    }
  QDPLL_SORT (qdpll, int, compare_lits_by_user_variable_nesting, 
              unsat_branch_clause->lits, unsat_branch_clause->num_lits);
  const unsigned int lits_before = unsat_branch_clause->num_lits;

  /* Apply simple universal/existential reduction. */
  top_level_reduce_constraint_simple (qdpll, unsat_branch_clause, 
                                      unsat_branch_clause->is_cube ? 
                                      QDPLL_QTYPE_FORALL : QDPLL_QTYPE_EXISTS);
  assert (lits_before >= unsat_branch_clause->num_lits);
  assert (!qdpll->options.trivial_falsity_partial_mus_assumptions || 
          cnt_universals >= (lits_before - unsat_branch_clause->num_lits));
  cnt_universals -= (lits_before - unsat_branch_clause->num_lits); 
  assert (!qdpll->options.trivial_falsity_partial_mus_assumptions || 
          cnt_universals <= unsat_branch_clause->num_lits);

  /* Try to remove innermost existentials. */
  if (qdpll->options.trivial_falsity_partial_mus_assumptions && cnt_universals > 0)
    {
#if COMPUTE_STATS
      double start_time = time_stamp ();
#endif
      unsat_branch_clause = trivial_falsity_try_remove_innermost_existentials 
        (qdpll, unsat_branch_clause, cnt_universals);
#if COMPUTE_STATS
      qdpll->stats.trivial_falsity_mus_assumptions_time += (time_stamp() - start_time);
#endif
    }

  if (qdpll->options.verbosity >= 2)
    {
      fprintf (stderr, "Trivial falsity clause: ");
      print_constraint (qdpll, unsat_branch_clause);
      fprintf (stderr, "  ...has %d literals compared to %d failed assumptions\n", 
               unsat_branch_clause->num_lits, cnt);
    }
#if COMPUTE_STATS
  qdpll->stats.trivial_falsity_lits_in_falsity_clause += unsat_branch_clause->num_lits;
#endif

  if (qdpll->options.trace)
    { 
      ConstraintID next_id = 0;
      assert (unsat_branch_clause->num_lits <= unsat_branch_clause->size_lits);
      if (unsat_branch_clause->num_lits < unsat_branch_clause->size_lits)
        {
          next_id = ++(qdpll->cur_constraint_id);
          /* Trace constraint with full literal list including reduced universal
             literals. */
          qdpll->trace_constraint (next_id, unsat_branch_clause->lits, 
                                   unsat_branch_clause->size_lits, 0, 0);
          /* Must assign new idea to final clause resulting from universal reduction. */
          unsat_branch_clause->id = ++(qdpll->cur_constraint_id);
        }
      /* Trace final constraint without reduced universal literals. */
      qdpll->trace_constraint (unsat_branch_clause->id, 
                               unsat_branch_clause->lits, 
                               unsat_branch_clause->num_lits, 
                               next_id, 0);
    }

  return unsat_branch_clause;
}

static void
trivial_falsity_set_up_sat_solver (QDPLL *qdpll)
{
  /* For multiple calls of 'qdpll_sat', if user has not added or removed any
     clauses but maybe under assumptions, there is no need to re-initialize
     trivial-falsity solver. */
  if (qdpll->state.num_sat_calls > 1)
    return;

  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        picosat_add (qdpll->trivial_falsity_solver, *p);
      picosat_add (qdpll->trivial_falsity_solver, 0);
    }
}

static void
trivial_truth_set_up_sat_solver (QDPLL *qdpll)
{
  /* For multiple calls of 'qdpll_sat', if user has not added or removed any
     clauses but maybe under assumptions, there is no need to re-initialize
     trivial-truth solver.  */
  if (qdpll->state.num_sat_calls > 1)
    return;

  VarID next_selector_id = qdpll_get_max_declared_var_id (qdpll) + 1;
  assert (next_selector_id > 0);

  /* Add CNF to SAT solver. */
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        {
          LitID lit = *p;
          Var *v = LIT2VARPTR (qdpll->pcnf.vars, lit);
          /* Add existential literals to SAT solver, replace universal ones by
             their selector variable. */
          if (QDPLL_VAR_FORALL (v))
            {

            }
          else
            picosat_add (qdpll->trivial_truth_solver, lit);
        }
          /* Add fresh selector variable to disable clause if it is blocked or
             satisfied by the current QBF solver assignment. */
          assert (!c->trivial_truth_selector);
          c->trivial_truth_selector = next_selector_id++;
          picosat_add (qdpll->trivial_truth_solver, c->trivial_truth_selector);
      picosat_add (qdpll->trivial_truth_solver, 0);
    }
}

static Constraint *
dynamic_nenofex_get_unsat_branch_clause (QDPLL *qdpll)
{
  unsigned int cnt = (qdpll->assigned_vars_top - qdpll->assigned_vars);
  assert (cnt <= qdpll_get_max_declared_var_id (qdpll));
  Constraint *unsat_branch_clause = create_constraint (qdpll, cnt, 0);
  /* Create clause by negating literals in current assignment. */
  LitID *litp = unsat_branch_clause->lits;
  VarID *vp, *ve;
  for (vp = qdpll->assigned_vars, ve = qdpll->assigned_vars_top; vp < ve; vp++)
    {
      assert (litp < unsat_branch_clause->lits + unsat_branch_clause->num_lits);
      VarID vid = *vp;
      Var *var = VARID2VARPTR (qdpll->pcnf.vars, vid);
      assert (QDPLL_VAR_ASSIGNED (var));
      /* Must ignore existential pure literals as they are never
         responsible for unsatisfiability. */
      if (!(QDPLL_VAR_EXISTS (var) && var->mode == QDPLL_VARMODE_PURE))
        {
          if (QDPLL_VAR_ASSIGNED_FALSE (var))
            *litp++ = vid;
          else
            *litp++ = -vid;
        }
      else
        unsat_branch_clause->num_lits--;
    }
  QDPLL_SORT (qdpll, int, compare_lits_by_user_variable_nesting, 
              unsat_branch_clause->lits, unsat_branch_clause->num_lits);
  /* Apply simple universal/existential reduction. */
  top_level_reduce_constraint_simple (qdpll, unsat_branch_clause, 
                                      unsat_branch_clause->is_cube ? 
                                      QDPLL_QTYPE_FORALL : QDPLL_QTYPE_EXISTS);
  return unsat_branch_clause;
}

/* Solver's core loop. */
static QDPLLResult
solve (QDPLL * qdpll)
{
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses));
  QDPLL_ABORT_QDPLL (!qdpll->state.assumptions_given && count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  /* Do not support full pure literals any more since it is much worse than
     spurious pure literals in any experiments so far. */
  QDPLL_ABORT_QDPLL(qdpll->options.no_spure_literals, 
                    "Full pure literals no longer supported.");

  QDPLL_ABORT_QDPLL (!qdpll->options.no_trivial_falsity && 
                     qdpll->options.incremental_use, 
                     "temporary restriction: must not combine incremental mode with trivial falsity");
  QDPLL_ABORT_QDPLL (!qdpll->options.no_trivial_truth && 
                     qdpll->options.incremental_use, 
                     "temporary restriction: must not combine incremental mode with trivial truth");
  QDPLL_ABORT_QDPLL (!qdpll->options.no_dynamic_nenofex && 
                     qdpll->options.incremental_use, 
                     "temporary restriction: must not combine incremental mode with dynamic nenofex");

  /* Disable trivial falsity calls if limit on number of clauses in original CNF exceeded. */
  if (!qdpll->options.no_trivial_falsity && 
      !qdpll->state.trivial_falsity_disabled &&
      qdpll->options.trivial_falsity_disable_cnf_threshold > 0 && 
      qdpll->pcnf.clauses.cnt >= qdpll->options.trivial_falsity_disable_cnf_threshold)
    {
      qdpll->state.trivial_falsity_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling trivial falsity calls: CNF size is %d, %d threshold\n", 
                 qdpll->pcnf.clauses.cnt, qdpll->options.trivial_falsity_disable_cnf_threshold);
    }

  /* Disable trivial truth calls if limit on number of clauses in original CNF exceeded. */
  if (!qdpll->options.no_trivial_truth && 
      !qdpll->state.trivial_truth_disabled &&
      qdpll->options.trivial_truth_disable_cnf_threshold > 0 && 
      qdpll->pcnf.clauses.cnt >= qdpll->options.trivial_truth_disable_cnf_threshold)
    {
      qdpll->state.trivial_truth_disabled = 1;
      if (qdpll->options.verbosity >= 1)
        fprintf (stderr, "Disabling trivial truth calls: CNF size is %d, %d threshold\n", 
                 qdpll->pcnf.clauses.cnt, qdpll->options.trivial_truth_disable_cnf_threshold);
    }

  /* Set up trivial falsity solver. */
  if (!qdpll->options.no_trivial_falsity && !qdpll->state.trivial_falsity_disabled)
    trivial_falsity_set_up_sat_solver (qdpll);
  /* Set up trivial truth solver. */
  if (!qdpll->options.no_trivial_truth && !qdpll->state.trivial_truth_disabled)
    trivial_truth_set_up_sat_solver (qdpll);

  assert (!qdpll->state.restarting);

  QDPLLResult result = QDPLL_RESULT_UNKNOWN;
  QDPLLSolverState state = QDPLL_SOLVER_STATE_UNDEF;
  unsigned int backtrack_level;
  Var *decision_var;
  QDPLLAssignment assignment;
  QDPLLDepManGeneric *dm = qdpll->dm;

  if (qdpll->options.lclauses_init_size == 0)
    {
      if (qdpll->options.lclauses_min_init_size <= qdpll->pcnf.clauses.cnt &&
          qdpll->pcnf.clauses.cnt <= qdpll->options.lclauses_max_init_size)
        qdpll->options.lclauses_init_size = qdpll->pcnf.clauses.cnt;
      else if (qdpll->pcnf.clauses.cnt <
               qdpll->options.lclauses_min_init_size)
        qdpll->options.lclauses_init_size =
          qdpll->options.lclauses_min_init_size;
      else
        qdpll->options.lclauses_init_size =
          qdpll->options.lclauses_max_init_size;
    }

  if (qdpll->options.lcubes_init_size == 0)
    {
      if (qdpll->options.lcubes_min_init_size <= qdpll->pcnf.clauses.cnt &&
          qdpll->pcnf.clauses.cnt <= qdpll->options.lcubes_max_init_size)
        qdpll->options.lcubes_init_size = qdpll->pcnf.clauses.cnt;
      else if (qdpll->pcnf.clauses.cnt < qdpll->options.lcubes_min_init_size)
        qdpll->options.lcubes_init_size = qdpll->options.lcubes_min_init_size;
      else
        qdpll->options.lcubes_init_size = qdpll->options.lcubes_max_init_size;
    }

  if (qdpll->state.lclauses_size == 0)
    qdpll->state.lclauses_size = qdpll->options.lclauses_init_size;
  if (qdpll->pcnf.learnt_cubes.cnt == 0)
    qdpll->state.lcubes_size = qdpll->options.lcubes_init_size;

  QDPLL_ABORT_QDPLL(qdpll->state.lcubes_size == 0 || 
                    qdpll->state.lcubes_size < qdpll->pcnf.learnt_cubes.cnt, 
                    "Unexpected value of 'lcubes_size'!");
  QDPLL_ABORT_QDPLL(qdpll->state.lclauses_size == 0 || 
                    qdpll->state.lclauses_size < qdpll->pcnf.learnt_clauses.cnt, 
                    "Unexpected value of 'lclauses_size'!");

  assert (qdpll->state.decision_level == 0);
  assert (qdpll->state.assumptions_given || sizeof_top_level (qdpll) == 0);

  /* For incremental solving: must check which of the learned cubes can safely
     be kept. Incrementally deleting clauses is no problem, but adding clauses
     must be handled. 
     UPDATE: cube checking now also if no 'push' was called before. This is
     necessary if the user just adds clauses but never wants to remove them
     later. */
  assert (qdpll->state.num_sat_calls > 0);
  QDPLL_ABORT_QDPLL (qdpll->state.num_sat_calls <= 1 && 
                     (qdpll->pcnf.learnt_clauses.cnt > 0 || qdpll->pcnf.learnt_cubes.cnt > 0), 
                     "Unexpected learned constraints present.");
  if (qdpll->state.num_sat_calls > 1 && qdpll->state.pending_cubes_check)
    check_and_delete_cubes_incremental (qdpll);
  else if (qdpll->state.num_sat_calls <= 1)
    {
      /* No learned cubes are present in this case. */
      qdpll->state.pending_cubes_check = 0;
      qdpll->state.clauses_added_since_cube_check = 0;
    }

  /* NOTE: assign user-given assumptions AFTER possible cleanup of deleted clauses
     and resulting no-occ-vars by calling 'qdpll_gc_aux ()' below. No-occ vars
     will not be assigned as assumptions. This is necessary to handle
     situations where the user adds assumptions of variables which actually
     have no occurrences left after this INTERNAL cleanup step. The user does
     not know when the solver triggers that cleanup step. 
     FURTHER NOTE: we must assign user assumptions BEFORE initial call of QBCE
     since the formula may be unsatisfiable under assumptions which, however,
     we may not detect properly if clauses are blocked. */

  if (qdpll->options.incremental_use)
    {
      if (qdpll->state.cnt_created_clause_groups > 0 || 
	  QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0)
	{
	  /* Clean up if the number of popped off clauses exceeds 25% of the
	     number of original ones. */
	  if (qdpll->state.popped_off_orig_clause_cnt > (qdpll->pcnf.clauses.cnt >> 2))
	    qdpll_gc_aux (qdpll, 0);

          assign_user_given_assumptions (qdpll);
	  /* Call QBCE for preprocessing and check for necessary rescheduling
	     of blocked clauses after user has added clauses. */
	  qbcp_qbce_first_call_before_solving (qdpll);
	  /* For incremental solving: assign selector variables to enable/disable
	     clauses associated to currently and previously used frames. */
	  assign_frame_selector_variables (qdpll);
	}
      else
        {
          assign_user_given_assumptions (qdpll);
          qbcp_qbce_first_call_before_solving (qdpll);
        }
    }
  else
    {
      assign_user_given_assumptions (qdpll);
      qbcp_qbce_first_call_before_solving (qdpll);
    }

  if (!qdpll->dm->is_init (qdpll->dm))
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "Initializing dependencies.\n");
#if COMPUTE_STATS
      qdpll->stats.total_dep_man_init_calls++;
#endif
      qdpll->dm->init (qdpll->dm);
    }

  state = set_up_watchers (qdpll);
  /* At this point: if the original formula was decided right away
     in watcher initialization, then we must output information. Case
     UNSAT: either input formula has a clause containing ONLY universal
     literals; we can simply print that clause, which proves UNSAT. Or,
     input clause is empty under partial assignment produced during
     watcher initialization; we could then proceed to 'bcp' and derive
     empty clause by Q-resolution. Case SAT: formula does not have
     input clauses at all. */
  if (state == QDPLL_SOLVER_STATE_SAT)
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "SDCL: formula is empty or has satisfied learned cube.\n");

      generate_and_add_reason (qdpll, QDPLL_QTYPE_FORALL);

      return QDPLL_RESULT_SAT;
    }
  else if (state == QDPLL_SOLVER_STATE_UNSAT)
    {
      assert (qdpll->result_constraint);
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "CDCL: empty original clause (%u).\n",
                 qdpll->result_constraint->id);

      generate_and_add_reason (qdpll, QDPLL_QTYPE_EXISTS);

      return QDPLL_RESULT_UNSAT;
    }

  while (1)
    {
      assert (result == QDPLL_RESULT_UNKNOWN);
      if (check_limits_and_abort(qdpll))
        {
          fprintf (stderr, "User-given limit reached, exiting.\n");
          break;
        }

      /* Reset flag for QDIMACS output values from trivial truth solver. */
      qdpll->state.qdo_trivial_truth_success = 0;

      state = bcp (qdpll);

      if (state == QDPLL_SOLVER_STATE_UNDEF)
        qdpll->state.cnt_state_undetermined_after_qbcp++;

#if COMPUTE_STATS
      unsigned int dynamic_nenofex_test_success = 0;
      unsigned int trivial_truth_or_falsity_success = 0;
#endif

      if (!qdpll->options.no_dynamic_nenofex && 
          state == QDPLL_SOLVER_STATE_UNDEF &&
          (qdpll->state.cnt_state_undetermined_after_qbcp & 
           (((unsigned int)1 << qdpll->options.dyn_nenofex_pow2_call_interval) - 1)) == 0)
        {
          NenofexResult nenofex_res = dynamic_nenofex_test (qdpll);
          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "Dynamic Nenofex test: %s at decision level %d, " \
                     "%d assigned vars of %d total vars\n", 
                     nenofex_res == NENOFEX_RESULT_SAT ? "SATISFIABLE" : 
                     (nenofex_res == NENOFEX_RESULT_UNSAT ? "UNSATISFIABLE" : "UNKNOWN"), 
                     qdpll->state.decision_level, (unsigned int)
                     (qdpll->assigned_vars_top - qdpll->assigned_vars), qdpll->pcnf.used_vars);
          if (nenofex_res == NENOFEX_RESULT_SAT && 
              !qdpll->options.dyn_nenofex_ignore_sat)
            {
              /* Set state variable in order to learn a cube from the
                 current assignment. */
              state = QDPLL_SOLVER_STATE_SAT;
              assert (!qdpll->state.sat_branch_detected);
              qdpll->state.sat_branch_detected = 1;
#if COMPUTE_STATS
              assert (!dynamic_nenofex_test_success);
              dynamic_nenofex_test_success = 1;
#endif
            }
          else if (nenofex_res == NENOFEX_RESULT_UNSAT && 
                   !qdpll->options.dyn_nenofex_ignore_unsat)
            {
              assert (!qdpll->state.unsat_branch_clause);
              qdpll->state.unsat_branch_clause = 
                dynamic_nenofex_get_unsat_branch_clause (qdpll);
              if (qdpll->options.verbosity >= 2)
                {
                  fprintf (stderr, "Nenofex test unsat branch clause: ");
                  print_constraint (qdpll, qdpll->state.unsat_branch_clause);
                  fprintf (stderr, "  ...has %d literals, %d currently assigned variables\n", 
                           qdpll->state.unsat_branch_clause->num_lits, (int)(qdpll->assigned_vars_top - 
									qdpll->assigned_vars));
                }

              /* Set solver state to UNSAT so that we enter the respective
                 branch below. There, a new clause will be learned using
                 the clause learned by the dynamic Nenofex test as a start
                 point. If the start clause is already asserting then it
                 will be learned. */
              state = QDPLL_SOLVER_STATE_UNSAT;
#if COMPUTE_STATS
              assert (!dynamic_nenofex_test_success);
              dynamic_nenofex_test_success = 1;
#endif
            }
        }

      /* Check for trivial falsity by SAT solver. */
      if (!qdpll->options.no_trivial_falsity &&
          !qdpll->state.trivial_falsity_disabled && 
          state == QDPLL_SOLVER_STATE_UNDEF && 
          (/* NOTE: '-1' to make sure to test trivial falsity before the very first decision */
           (qdpll->state.cnt_state_undetermined_after_qbcp - 1) & 
           (((unsigned int)1 << qdpll->options.trivial_falsity_pow2_call_interval) - 1)) == 0)
        {
#if COMPUTE_STATS
          unsigned int assumptions_passed_in_success = 0;
#endif
          double start_time = time_stamp ();
          qdpll->state.trivial_falsity_tried++;
          VarID *vp, *ve;
          for (vp = qdpll->assigned_vars, ve = qdpll->assigned_vars_top; vp < ve; vp++)
            {
              Var *v = VARID2VARPTR (qdpll->pcnf.vars, *vp);
              assert (QDPLL_VAR_ASSIGNED (v));
              if (!(QDPLL_VAR_EXISTS (v) && v->mode == QDPLL_VARMODE_PURE))
                {
#if COMPUTE_STATS
                  assumptions_passed_in_success++;
#endif
                  picosat_assume (qdpll->trivial_falsity_solver, QDPLL_VAR_ASSIGNED_TRUE (v) ? v->id : -v->id);
                }
            }

#if COMPUTE_STATS
          unsigned long long int trivial_falsity_previous_decisions = 
            picosat_decisions (qdpll->trivial_falsity_solver);
#endif
          int sat_result = picosat_sat (qdpll->trivial_falsity_solver, 
                                        qdpll->options.trivial_falsity_decision_limit > 0 ? 
                                        (int) qdpll->options.trivial_falsity_decision_limit : -1);
#if COMPUTE_STATS
          unsigned long long int trivial_falsity_current_decisions = 
            picosat_decisions (qdpll->trivial_falsity_solver) - trivial_falsity_previous_decisions;
          if (trivial_falsity_current_decisions > qdpll->stats.trivial_falsity_max_decisions_per_call)
            qdpll->stats.trivial_falsity_max_decisions_per_call = trivial_falsity_current_decisions;
#endif
          if (sat_result == PICOSAT_UNSATISFIABLE)
            {
#if COMPUTE_STATS
              assert (!trivial_truth_or_falsity_success);
              trivial_truth_or_falsity_success = 1;
              qdpll->stats.trivial_falsity_detected++;
              qdpll->stats.trivial_falsity_assumptions_passed += assumptions_passed_in_success;
#endif
              assert (!qdpll->state.unsat_branch_clause);
              qdpll->state.unsat_branch_clause = handle_trivial_falsity (qdpll);
#ifndef NDEBUG
              assert_trivial_falsity_assumption_unsat_test 
                (qdpll, qdpll->state.unsat_branch_clause);
#endif
              /* Set solver state to UNSAT so that we enter the respective
                 branch below. There, a new clause will be learned using
                 the clause learned by trivial falsity as a start
                 point. If the start clause is already asserting then it
                 will be learned. */
#if COMPUTE_STATS
              if (qdpll->state.unsat_branch_clause->num_lits == 0)
                qdpll->stats.trivial_falsity_empty_clauses_learned++;
              else if (qdpll->state.unsat_branch_clause->num_lits == 1)
                qdpll->stats.trivial_falsity_unit_clauses_learned++;
              else if (qdpll->state.unsat_branch_clause->num_lits == 2)
                qdpll->stats.trivial_falsity_binary_clauses_learned++;
              else if (qdpll->state.unsat_branch_clause->num_lits == 3)
                qdpll->stats.trivial_falsity_ternary_clauses_learned;
#endif
              state = QDPLL_SOLVER_STATE_UNSAT;
            }
          else
            {

            }
          qdpll->state.trivial_falsity_time += (time_stamp () - start_time);

          if (qdpll->options.trivial_falsity_disable_calls_threshold > 0 && 
              qdpll->state.trivial_falsity_tried >= qdpll->options.trivial_falsity_disable_calls_threshold && 
              (qdpll->state.trivial_falsity_time / qdpll->state.trivial_falsity_tried) >= 
              qdpll->options.trivial_falsity_disable_time_threshold)
            {
              assert (!qdpll->state.trivial_falsity_disabled);
              qdpll->state.trivial_falsity_disabled = 1;
              if (qdpll->options.verbosity >= 1)
                fprintf (stderr, "Disabling trivial falsity calls: average time is %f, %d calls\n", 
                         qdpll->state.trivial_falsity_time / qdpll->state.trivial_falsity_tried, 
                         qdpll->state.trivial_falsity_tried);
            }
        }

      /* Check for trivial truth by SAT solver. */
      if (!qdpll->options.no_trivial_truth &&
          !qdpll->state.trivial_truth_disabled &&
          !qdpll->state.no_scheduled_trivial_truth && 
          state == QDPLL_SOLVER_STATE_UNDEF &&
          (/* NOTE: '-1' to make sure to test trivial truth before the very first decision */
           (qdpll->state.cnt_state_undetermined_after_qbcp - 1) & 
           (((unsigned int)1 << qdpll->options.trivial_truth_pow2_call_interval) - 1)) == 0)
        {
          double start_time = time_stamp ();
          /* Set of most recent failed assumptions used to skip redundant
             trivial truth tests must have been reset. */
          qdpll->state.trivial_truth_tried++;

          VarID *vp, *ve;
          for (vp = qdpll->assigned_vars, ve = qdpll->assigned_vars_top; vp < ve; vp++)
            {
              Var *v = VARID2VARPTR (qdpll->pcnf.vars, *vp);
              assert (QDPLL_VAR_ASSIGNED (v));
              if (QDPLL_VAR_FORALL (v))
                {

                }
              else
                picosat_assume (qdpll->trivial_truth_solver, 
                                QDPLL_VAR_ASSIGNED_TRUE (v) ? v->id : -v->id);
            }

          /* Assign selector variables to disable currently blocked or
             satisfied clauses in the SAT solver. Selector variables of
             non-blocked or non-satisfied clauses are set to false. Note that
             we need to make sure that clauses satisfied by universal literals
             are also satisfied in the SAT solver by setting the selector
             variables accordingly. 
             NOTE: may be costly if we carry out the trivial truth test frequently. */
              Constraint *c;
              for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
                {
                  assert (c->trivial_truth_selector);
                  if (c->qbcp_qbce_blocked || is_clause_satisfied (qdpll, c))
                    picosat_assume (qdpll->trivial_truth_solver, c->trivial_truth_selector);
                  else
                    picosat_assume (qdpll->trivial_truth_solver, -c->trivial_truth_selector);
                }

#if COMPUTE_STATS
          unsigned long long int trivial_truth_previous_decisions = 
            picosat_decisions (qdpll->trivial_truth_solver);
#endif
          int sat_result = picosat_sat (qdpll->trivial_truth_solver, 
					qdpll->options.trivial_truth_decision_limit > 0 ? 
                                        (int) qdpll->options.trivial_truth_decision_limit : -1);
#if COMPUTE_STATS
          unsigned long long int trivial_truth_current_decisions = 
            picosat_decisions (qdpll->trivial_truth_solver) - trivial_truth_previous_decisions;
          if (trivial_truth_current_decisions > qdpll->stats.trivial_truth_max_decisions_per_call)
            qdpll->stats.trivial_truth_max_decisions_per_call = trivial_truth_current_decisions;
#endif
          if (sat_result == PICOSAT_SATISFIABLE)
            {
#if COMPUTE_STATS
              assert (!trivial_truth_or_falsity_success);
              trivial_truth_or_falsity_success = 1;
              qdpll->stats.trivial_truth_detected++;
#endif
              if (qdpll->options.verbosity >= 2)
                fprintf (stderr, "TRIVIAL TRUTH at decision level %d, %d assigned vars of %d total vars\n", 
                         qdpll->state.decision_level, (unsigned int)
                         (qdpll->assigned_vars_top - qdpll->assigned_vars), qdpll->pcnf.used_vars);
              state = QDPLL_SOLVER_STATE_SAT;
              assert (!qdpll->state.sat_branch_detected);
              qdpll->state.sat_branch_detected = 1;
              assert (!qdpll->state.qdo_trivial_truth_success);
              qdpll->state.qdo_trivial_truth_success = 1;
            }
          else if (sat_result == PICOSAT_UNSATISFIABLE)
            {

            }
          qdpll->state.trivial_truth_time += (time_stamp () - start_time);

          if (qdpll->options.trivial_truth_disable_calls_threshold > 0 && 
              qdpll->state.trivial_truth_tried >= qdpll->options.trivial_truth_disable_calls_threshold && 
              (qdpll->state.trivial_truth_time / qdpll->state.trivial_truth_tried) >= 
              qdpll->options.trivial_truth_disable_time_threshold)
            {
              assert (!qdpll->state.trivial_truth_disabled);
              qdpll->state.trivial_truth_disabled = 1;
              if (qdpll->options.verbosity >= 1)
                fprintf (stderr, "Disabling trivial truth calls: average time is %f, %d calls\n", 
                         qdpll->state.trivial_truth_time / qdpll->state.trivial_truth_tried, 
                         qdpll->state.trivial_truth_tried);
            }
        }

      qdpll->state.restarting = 0;

      if (state == QDPLL_SOLVER_STATE_UNSAT)
        {
          /* Conflict: analyze conflict and backtrack. */
          assert ((qdpll->result_constraint
                   && !qdpll->result_constraint->is_cube) || 
                  qdpll->state.unsat_branch_clause);
          assert ((qdpll->state.unsat_branch_clause && 
                   is_clause_empty (qdpll, qdpll->state.unsat_branch_clause)) || 
                  (!qdpll->state.unsat_branch_clause && 
                   is_clause_empty (qdpll, qdpll->result_constraint)));
          assert ((qdpll->state.unsat_branch_clause && 
                   !is_clause_satisfied (qdpll, qdpll->state.unsat_branch_clause)) || 
                  (!qdpll->state.unsat_branch_clause && 
                   !is_clause_satisfied (qdpll, qdpll->result_constraint)));

          check_resize_learnt_constraints (qdpll, QDPLL_QTYPE_EXISTS);

#if QDPLL_ASSERT_SOLVE_STATE
          assert (qdpll->state.unsat_branch_clause || 
                  is_formula_false (qdpll));
          assert (qdpll->state.unsat_branch_clause || 
                  !is_formula_true (qdpll));
#endif
          backtrack_level = analyze_conflict (qdpll);
          if (qdpll->state.unsat_branch_clause)
            {
              delete_constraint (qdpll, qdpll->state.unsat_branch_clause);
              qdpll->state.unsat_branch_clause = 0;
#if COMPUTE_STATS
              assert (trivial_truth_or_falsity_success || dynamic_nenofex_test_success);
              if (qdpll->state.forced_assignment.antecedent)
                {
                  assert (!qdpll->state.forced_assignment.antecedent->derived_by_trivial_truth_or_falsity);
                  assert (!qdpll->state.forced_assignment.antecedent->derived_by_dynamic_nenofex);
                  if (trivial_truth_or_falsity_success)
                    qdpll->state.forced_assignment.antecedent->derived_by_trivial_truth_or_falsity = 1;
                  else if (dynamic_nenofex_test_success)
                    qdpll->state.forced_assignment.antecedent->derived_by_dynamic_nenofex = 1;
                }
#endif
            }
#if COMPUTE_STATS
          qdpll->stats.unsat_results++;
          qdpll->stats.total_unsat_results_dlevels +=
            qdpll->state.decision_level;
          if (backtrack_level != QDPLL_INVALID_DECISION_LEVEL)
            {
              qdpll->stats.total_unsat_results_btlevels +=
                backtrack_level - 1;
              qdpll->stats.total_unsat_results_btdist +=
                (qdpll->state.decision_level - backtrack_level) + 1;
            }
#endif
          if (backtrack_level == QDPLL_INVALID_DECISION_LEVEL)
            {
              /* Conflict can not be resolved -> terminate. */
              result = QDPLL_RESULT_UNSAT;
              break;
            }
          else
            {
              /* Check whether to restart. But only if we did not jump back to top level anyway. */
              if (!check_and_restart (qdpll, backtrack_level))
                {
#if COMPUTE_STATS
                  if (backtrack_level == 1)
                    qdpll->stats.qbcp_qbce_backtracks_to_toplevel++;
#endif
                  backtrack (qdpll, backtrack_level);
                  push_forced_assignment (qdpll);
                }
            }

          /* Conflict must be fixed now. */
          assert (!qdpll->result_constraint || 
                  !is_clause_empty (qdpll, qdpll->result_constraint));
          qdpll->result_constraint = 0;
        }
      else if (state == QDPLL_SOLVER_STATE_SAT)
        {
          assert (!qdpll->result_constraint
                  || qdpll->result_constraint->is_cube);
          assert (!qdpll->result_constraint
                  || is_cube_satisfied (qdpll, qdpll->result_constraint));
          assert (!qdpll->result_constraint
                  || !is_cube_empty (qdpll, qdpll->result_constraint));

          check_resize_learnt_constraints (qdpll, QDPLL_QTYPE_FORALL);

          /* Empty formula: analyze solution and backtrack. */
#if QDPLL_ASSERT_SOLVE_STATE
          assert (!is_formula_false (qdpll));
          assert (qdpll->state.sat_branch_detected || 
                  is_formula_true (qdpll));
#endif
          backtrack_level = analyze_solution (qdpll);

#if COMPUTE_STATS
          if (qdpll->state.sat_branch_detected)
            {
              assert (trivial_truth_or_falsity_success || dynamic_nenofex_test_success);
              if (qdpll->state.forced_assignment.antecedent)
                {
                  assert (!qdpll->state.forced_assignment.antecedent->derived_by_trivial_truth_or_falsity);
                  assert (!qdpll->state.forced_assignment.antecedent->derived_by_dynamic_nenofex);
                  if (trivial_truth_or_falsity_success)
                    qdpll->state.forced_assignment.antecedent->derived_by_trivial_truth_or_falsity = 1;
                  else if (dynamic_nenofex_test_success)
                    qdpll->state.forced_assignment.antecedent->derived_by_dynamic_nenofex = 1;
                }
            }
#endif
          qdpll->state.sat_branch_detected = 0;
#if COMPUTE_STATS
          qdpll->stats.sat_results++;
          qdpll->stats.total_sat_results_dlevels +=
            qdpll->state.decision_level;
          if (backtrack_level != QDPLL_INVALID_DECISION_LEVEL)
            {
              qdpll->stats.total_sat_results_btlevels += backtrack_level - 1;
              qdpll->stats.total_sat_results_btdist +=
                (qdpll->state.decision_level - backtrack_level) + 1;
            }
          qdpll->stats.avg_sat_res_assigned_vars +=
            (qdpll->assigned_vars_top -
             qdpll->assigned_vars) / (double) qdpll->pcnf.used_vars;
          qdpll->stats.avg_sat_res_propped_vars +=
            (qdpll->bcp_ptr + 1 -
             qdpll->assigned_vars) / (double) qdpll->pcnf.used_vars;
          qdpll->stats.avg_sat_res_propped_vars_per_assigned +=
            (double) (qdpll->bcp_ptr + 1 -
                      qdpll->assigned_vars) / (qdpll->assigned_vars_top -
                                               qdpll->assigned_vars);
#endif
          if (backtrack_level == QDPLL_INVALID_DECISION_LEVEL)
            {
              /* All branches satisfied -> terminate. */
              result = QDPLL_RESULT_SAT;
              break;
            }
          else
            {
              if (!check_and_restart (qdpll, backtrack_level))
                {
#if COMPUTE_STATS
                  if (backtrack_level == 1)
                    qdpll->stats.qbcp_qbce_backtracks_to_toplevel++;
#endif
                  backtrack (qdpll, backtrack_level);
                  push_forced_assignment (qdpll);
                }
            }

          /* Solution must be broken now. */
          assert (!qdpll->result_constraint
                  || !is_cube_satisfied (qdpll, qdpll->result_constraint));
          qdpll->result_constraint = 0;
        }
      else
        {
          assert (state == QDPLL_SOLVER_STATE_UNDEF);

          /* Result undefined: decide next branch. */
          if (qdpll->options.max_dec)
            {
              qdpll->state.num_decisions++;
              if (qdpll->options.max_dec < qdpll->state.num_decisions)
                {
                  if (qdpll->options.verbosity > 1)
                    fprintf (stderr, "Aborting after decision limit of %d.\n",
                             qdpll->options.max_dec);
                  return QDPLL_RESULT_UNKNOWN;
                }
            }

#if QDPLL_ASSERT_SOLVE_STATE
          assert (!is_formula_false (qdpll));
#endif
          assert (state == QDPLL_SOLVER_STATE_UNDEF);
          assert (qdpll->bcp_ptr == qdpll->assigned_vars_top);

          notify_inactive_at_decision_point (qdpll);

          decision_var = select_decision_variable (qdpll);
          assignment = select_decision_assignment (qdpll, decision_var);

#if COMPUTE_STATS
          qdpll->stats.decisions++;
#endif

          push_assigned_variable (qdpll, decision_var, assignment,
                                  QDPLL_VARMODE_LBRANCH);
        }
    }

  return result;
}

static int
isnumstr (char *str)
{
  /* Empty string is not considered as number-string. */
  if (!*str)
    return 0;
  char *p;
  for (p = str; *p; p++)
    {
      char c = *p;
      if (c != '.' && !isdigit (c))
        return 0;
    }
  return 1;
}

static void
reset_clean_up_assignments (QDPLL *qdpll)
{
  assert (qdpll->dm);
  /* If variables are assigned, then we must notify the dependency manager
     when unassigning them. */
  QDPLL_ABORT_QDPLL ((qdpll->assigned_vars != qdpll->assigned_vars_top) && 
                     !qdpll->dm->is_init (qdpll->dm),
                     "dependency manager is not initialized!");
  VarID *p, *e, *old_bcp_ptr = qdpll->old_bcp_ptr;
  Var *vars = qdpll->pcnf.vars;

  VarPtrStack user_assumptions;
  QDPLL_INIT_STACK (user_assumptions);
  assert (QDPLL_EMPTY_STACK (qdpll->reschedule_qbce_marked_clauses));
#ifndef NDEBUG
  /* To reschedule QBCE after assumptions: we use mark
     'constraint->qbcp_qbce_multi_purpose_mark', check that it has been fully
     reset. */
  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    assert (!c->qbcp_qbce_multi_purpose_mark);
#endif

  if (qdpll->assigned_vars != qdpll->assigned_vars_top)
    {
      /* Must handle empty assignment properly. The following for-loop is
         inelegant in that the traversal of the assigned variables starts at the
         end and proceeds towards the start. This way, the empty assignment is
         not properly detected and the loop is entered also. However, going from
         the start to the end requires some changes in the loop since we compare
         the pointer to 'qdpll->bcp_ptr'. */
      for (p = qdpll->assigned_vars_top - 1, e = qdpll->assigned_vars; p >= e;
           p--)
        {
          Var *assigned_var = VARID2VARPTR (vars, *p);
          assert (QDPLL_VAR_ASSIGNED (assigned_var));
          assert (assigned_var->assignment != QDPLL_ASSIGNMENT_UNDEF);
          assert (assigned_var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
          assert (assigned_var->mode != QDPLL_VARMODE_UNDEF);
          assert (assigned_var->mode != QDPLL_VARMODE_LBRANCH
                  || !assigned_var->antecedent);
          assert (assigned_var->mode != QDPLL_VARMODE_RBRANCH
                  || !assigned_var->antecedent);

          /*start: like backtrack-undo */
          assert (assigned_var->trail_pos != QDPLL_INVALID_TRAIL_POS);
          assert (assigned_var->trail_pos <
                  (unsigned int) (qdpll->assigned_vars_top - qdpll->assigned_vars));
          assert (qdpll->assigned_vars[assigned_var->trail_pos] == assigned_var->id);
          if (assigned_var->mode == QDPLL_VARMODE_LBRANCH
              || assigned_var->mode == QDPLL_VARMODE_RBRANCH)
            {
              /* Must remove decision variables from dec-stack. */
              assert (!QDPLL_EMPTY_STACK (qdpll->dec_vars));
              assert (*(qdpll->dec_vars.top - 1) == assigned_var->id);
              QDPLL_POP_STACK (qdpll->dec_vars);
              if (!qdpll->options.no_qbce_dynamic)
                {
                  /* Remove stack of clauses blocked at decision level of 'var' and reset
                     blocked-flag of clauses. */
                  qbcp_qbce_backtrack_clear_stack_of_stacks 
                    (qdpll, &qdpll->qbcp_qbce_blocked_clauses, 1, assigned_var->decision_level);
                  /* Remove stack of clauses marked at decision level of 'var' and reset
                     marked-flag of clauses. */
                  qbcp_qbce_backtrack_clear_stack_of_stacks 
                    (qdpll, &qdpll->qbcp_qbce_marked_clauses, 0, assigned_var->decision_level);
                }
            }
	  else if (assigned_var->mode == QDPLL_VARMODE_ASSUMED && 
		   !assigned_var->is_internal)
	    {
	      if (qdpll->options.qbce_preprocessing || 
		  qdpll->options.qbce_inprocessing || 
		  !qdpll->options.no_qbce_dynamic)
                QDPLL_PUSH_STACK (qdpll->mm, user_assumptions, assigned_var);
	    }
          assigned_var->mode = QDPLL_VARMODE_UNDEF;
          assigned_var->assignment = QDPLL_ASSIGNMENT_UNDEF;
          assigned_var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
          assigned_var->trail_pos = QDPLL_INVALID_TRAIL_POS;
          if (assigned_var->antecedent)
            {
              assert (!assigned_var->antecedent->qbcp_qbce_blocked);
              assert (assigned_var->antecedent->is_reason);
              assigned_var->antecedent->is_reason = 0;
              assigned_var->antecedent = 0;
            }
          if (qdpll->dm->is_candidate (qdpll->dm, assigned_var->id)
              && assigned_var->priority_pos == QDPLL_INVALID_PQUEUE_POS)
            var_pqueue_insert (qdpll, assigned_var->id, assigned_var->priority);
          if (QDPLL_VAR_MARKED_PROPAGATED (assigned_var))
            {
              QDPLL_VAR_UNMARK_PROPAGATED (assigned_var);
              if (p < old_bcp_ptr)
                qdpll->dm->notify_active (qdpll->dm, assigned_var->id);
            }
          /*end: like backtrack-undo */
        }
    }

  qdpll->state.decision_level = 0;

  /* Remove stack of clauses blocked by inprocessing at decision level 0 and
     reset blocked-flag of clauses. Clauses blocked by preprocessing will stay
     and be handled separately. */
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) <= 2);
  if (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 2)
    qbcp_qbce_backtrack_clear_stack_of_stacks 
      (qdpll, &qdpll->qbcp_qbce_blocked_clauses, 1, qdpll->state.decision_level);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 1);

  /* Unmark QBCE-marked clauses at decision level 0. */
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 1);
  Constraint **cp, **ce;
  for (cp = qdpll->qbcp_qbce_marked_clauses.start[0].start, 
         ce = qdpll->qbcp_qbce_marked_clauses.start[0].top; cp < ce; cp++)
    {
      Constraint *c = *cp;
      assert (c->qbcp_qbce_mark);
      c->qbcp_qbce_mark = 0;
    }
  QDPLL_RESET_STACK (qdpll->qbcp_qbce_marked_clauses.start[0]);

  assert (qdpll->state.decision_level != QDPLL_INVALID_DECISION_LEVEL);
  qdpll->old_bcp_ptr = qdpll->bcp_ptr = qdpll->assigned_vars_top = qdpll->assigned_vars;

  /* When using QBCE and user assumptions: reset and reinitialize QBCE
     data structures. */
  if (QDPLL_COUNT_STACK (user_assumptions))
    {
      qbcp_qbce_reset_data_structures (qdpll);
      qbcp_qbce_init_data_structures (qdpll);
    }
  QDPLL_DELETE_STACK (qdpll->mm, user_assumptions);
}

static void
add_aux (QDPLL * qdpll, LitID id)
{
  if (id == 0)
    {
      QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                         "Unexpected assignments of variables; "        \
                         "solver must be in reset state when adding clauses or variable!");
      /* Make sure that user prefix is properly imported. This is necessary if
         the user has added a variable but no clauses containing it. The
         variable is present in the user prefix but deleted internally by the
         solver. make sure to add it here to avoid erroneously adding a user
         variable as free variable.  NOTE: 'import_user_scope' uses a flag to
         avoid redundant calls, so calling the function here should in most
         cases not result in actual work. */
      /* New: importing prefix is needed only before we add clauses. */
      if (!qdpll->state.scope_opened)
        import_user_scopes (qdpll);

      /* '0' closes a scope or clause. */
      const char *err_msg = import_added_ids (qdpll);
      QDPLL_ABORT_QDPLL (err_msg, err_msg);
      assert (!qdpll->state.scope_opened);
      assert (QDPLL_COUNT_STACK(qdpll->add_stack) == 0);
    }
  else
    {
      VarID var_id = LIT2VARID(id);
      if (var_id > qdpll->max_var_id_on_add_stack)
        qdpll->max_var_id_on_add_stack = var_id;
      QDPLL_PUSH_STACK (qdpll->mm, qdpll->add_stack, id);
    }
}

static void
rename_internal_variable_ids_aux (QDPLL *qdpll, VarID *p, 
                                  const unsigned int add_to_offset)
{
  LitID lit = *p;
  /* Assuming that literals of internal variables occur only positively in the
     formula. */
  assert (QDPLL_LIT_POS (lit));
  assert (*p + add_to_offset < qdpll->pcnf.size_vars);
  assert (*p + add_to_offset >= qdpll->pcnf.size_user_vars);
  *p = lit + add_to_offset;
  assert (!VARID2VARPTR(qdpll->pcnf.vars, *p)->id || 
          VARID2VARPTR(qdpll->pcnf.vars, *p)->is_internal);
  assert ((unsigned int)*p >= qdpll->pcnf.size_user_vars);
}

static void
rename_internal_variable_ids_on_blits_stack_aux (QDPLL *qdpll, BLitsOcc *b, 
                                                 const unsigned int add_to_offset)
{
  assert (b->blit);
  Var *blitvar = LIT2VARPTR (qdpll->pcnf.vars, b->blit);
  if (blitvar->id == 0)
    {
      /* Assumes that internal IDs have been moved to a new index and
         entry at old index has been cleared. */
      /* Internal IDs occur positively in clauses. */
      assert (QDPLL_LIT_POS (b->blit));
      rename_internal_variable_ids_aux (qdpll, (VarID *) &(b->blit), add_to_offset);
    }
}

/* Update BLitsOcc objects in QBCENonBlockedWitness objects. */
static void
rename_internal_variable_ids_on_qbce_blits_stack (QDPLL *qdpll, QBCENonBlockedWitness *start, 
                                                  QBCENonBlockedWitness *end, 
                                       const unsigned int add_to_offset)
{
  assert (start <= end);
  QBCENonBlockedWitness *p, *e;
  for (p = start, e = end; p < e; p++)
    rename_internal_variable_ids_on_blits_stack_aux (qdpll, &(p->blit_occ), add_to_offset);
}

static void
rename_internal_variable_ids_in_constraints (QDPLL *qdpll, ConstraintList *clist, 
                                  const unsigned int add_to_offset)
{
  Constraint *c;
  for (c = clist->first; c; c = c->link.next)
    {
      rename_internal_variable_ids_on_qbce_blits_stack 
        (qdpll, c->qbcp_qbce_notify_maybe_blocked_clauses.start, 
         c->qbcp_qbce_notify_maybe_blocked_clauses.top, 
         add_to_offset);
      rename_internal_variable_ids_on_qbce_blits_stack 
        (qdpll, c->qbcp_qbce_witness_clauses.start, 
         c->qbcp_qbce_witness_clauses.top, 
         add_to_offset);
      LitID *p, *e;
      for (p = c->lits, e = p + c->num_lits; p < e; p++)
        {
          LitID lit = *p;
          Var *v = LIT2VARPTR(qdpll->pcnf.vars, lit);
          if (v->id == 0)
            {
              /* Assumes that internal IDs have been moved to a new index and
                 entry at old index has been cleared. */
              /* Internal IDs occur positively in clauses. */
              assert (QDPLL_LIT_POS (lit));
              rename_internal_variable_ids_aux (qdpll, (VarID *) p, add_to_offset);
            }
          assert (*p);
        }
    }
}

/* Rename internal variable IDs on stacks
   'qdpll->state.cur_used_internal_vars' and
   'qdpll->state.popped_off_internal_vars'.  NOTE: assumes that the variable
   table has been enlarged before and internal variables have been moved
   accordingly. */
static void
rename_internal_variable_ids_on_stack (QDPLL *qdpll, VarID *start, VarID *end, 
                                       const unsigned int add_to_offset)
{
  assert (start <= end);
  VarID *p, *e;
  for (p = start, e = end; p < e; p++)
    {
      if (*p)
        {
          Var *var = VARID2VARPTR (qdpll->pcnf.vars, *p);
          if (var->id == 0)
            {
              /* Assumes that internal IDs have been moved to a new index and
                 entry at old index has been cleared. */
              rename_internal_variable_ids_aux (qdpll, p, add_to_offset);
            }
        }
    }
}

/* Update BLitsOcc objects. */
static void
rename_internal_variable_ids_on_blits_stack (QDPLL *qdpll, BLitsOcc *start, BLitsOcc *end, 
                                       const unsigned int add_to_offset)
{
  assert (start <= end);
  BLitsOcc *p, *e;
  for (p = start, e = end; p < e; p++)
    rename_internal_variable_ids_on_blits_stack_aux (qdpll, p, add_to_offset);
}

/* After enlarging the table of user variables: traverse all clauses and
   variables in blocks and rename internal IDs by adding the additional
   offset. */
static void
rename_internal_variable_ids (QDPLL *qdpll, const unsigned int add_to_offset)
{
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  rename_internal_variable_ids_in_constraints (qdpll, &qdpll->pcnf.clauses, add_to_offset);
  rename_internal_variable_ids_in_constraints (qdpll, &qdpll->pcnf.learnt_clauses, add_to_offset);
  rename_internal_variable_ids_in_constraints (qdpll, &qdpll->pcnf.learnt_cubes, add_to_offset);
  rename_internal_variable_ids_in_constraints (qdpll, &qdpll->cover_sets, add_to_offset);

  rename_internal_variable_ids_on_stack (qdpll, qdpll->state.cur_used_internal_vars.start, 
                                         qdpll->state.cur_used_internal_vars.top, 
                                         add_to_offset);

  rename_internal_variable_ids_on_stack (qdpll, qdpll->state.popped_off_internal_vars.start, 
                                         qdpll->state.popped_off_internal_vars.top, 
                                         add_to_offset);

  rename_internal_variable_ids_on_stack (qdpll, qdpll->pcnf.scopes.first->vars.start, 
                                         qdpll->pcnf.scopes.first->vars.top, 
                                         add_to_offset);

  rename_internal_variable_ids_on_stack (qdpll, qdpll->var_pqueue, 
                                         qdpll->var_pqueue +  qdpll->cnt_var_pqueue,
                                         add_to_offset);

  rename_internal_variable_ids_on_blits_stack 
    (qdpll, qdpll->empty_formula_watching_blit_occs.start, 
     qdpll->empty_formula_watching_blit_occs.top, add_to_offset);

  rename_internal_variable_ids_on_qbce_blits_stack 
    (qdpll, qdpll->qbcp_qbce_maybe_blocked_clauses.start, 
     qdpll->qbcp_qbce_maybe_blocked_clauses.top, 
     add_to_offset);

  Var *vp, *ve;
  for (vp = qdpll->pcnf.vars, ve = vp + qdpll->pcnf.size_vars; vp < ve; vp++)
    {
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->pos_occ_clauses.start, vp->pos_occ_clauses.top, add_to_offset);
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->neg_occ_clauses.start, vp->neg_occ_clauses.top, add_to_offset);
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->pos_occ_cubes.start, vp->pos_occ_cubes.top, add_to_offset);
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->neg_occ_cubes.start, vp->neg_occ_cubes.top, add_to_offset);
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->pos_notify_lit_watchers.start, 
         vp->pos_notify_lit_watchers.top, add_to_offset);
      rename_internal_variable_ids_on_blits_stack 
        (qdpll, vp->neg_notify_lit_watchers.start, 
         vp->neg_notify_lit_watchers.top, add_to_offset);      
    }
}

static void
move_internal_ids (QDPLL *qdpll, const unsigned int cur_size_user_vars, 
                   const unsigned int new_size_user_vars, 
                   const unsigned int add_to_offset)
{
  assert (cur_size_user_vars < qdpll->pcnf.size_vars);
  assert (new_size_user_vars < qdpll->pcnf.size_vars);
  assert (cur_size_user_vars < new_size_user_vars);
  assert (qdpll->state.next_free_internal_var_id == new_size_user_vars);
  Var *p, *e, *dest;
  for (p = qdpll->pcnf.vars + cur_size_user_vars, 
         e = dest = qdpll->pcnf.vars + new_size_user_vars; p < e; p++)
    {
      if (p->id)
        {
          QDPLL_ABORT_QDPLL (dest >= qdpll->pcnf.vars + qdpll->pcnf.size_vars, 
                             "error in move-internal-vars");
          QDPLL_ABORT_QDPLL (dest->id != 0, "error in move-internal-vars");
          QDPLL_ABORT_QDPLL (!p->is_internal, "error in move-internal-vars");
          *dest = *p;
          dest->id = dest->id + add_to_offset;
          memset (p, 0, sizeof (Var));
          dest++;
          qdpll->state.next_free_internal_var_id++;
        }
      else
        {
          dest++;
          qdpll->state.next_free_internal_var_id++;
        }
    }
}

/* Returns a pointer to the user scope with nesting level 'nesting'. */
static Scope *
find_user_scope_at_nesting_level (QDPLL *qdpll, Nesting nesting)
{
  assert (nesting > 0);
  assert (nesting <= qdpll_get_max_scope_nesting (qdpll));
  assert (QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs) == 
          qdpll_get_max_scope_nesting (qdpll));
  assert (nesting <= QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs));
#ifndef NDEBUG
  Scope *s;
  for (s = qdpll->pcnf.user_scopes.first; s && s->nesting != nesting; s = s->link.next)
    ;
  assert (s);
  assert (s == qdpll->pcnf.user_scope_ptrs.start[nesting - 1]);
#endif
  return qdpll->pcnf.user_scope_ptrs.start[nesting - 1];
}


/* Returns non-zero iff the scope 's' has at least one variable which is NOT
   internal and which is free, i.e. a free user var. */
static int
has_scope_free_user_var (QDPLL *qdpll, Scope *s)
{
  VarID *p, *e;
  for (p = s->vars.start, e = s->vars.top; p < e; p++)
    {
      VarID id = *p;
      assert (id);
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      assert (var->id == id);
      /* Free variables do not have a 'var->user_scope'. See also
         'declare_and_init_variable'. */
      if (!var->is_internal && !var->user_scope)
        return 1;
    }
  return 0;
}


static void
qdpll_delete_constraint_list (QDPLL * qdpll, ConstraintList *clist)
{
  Constraint *c, *nc;
  for (c = clist->first; c; c = nc)
    {
      nc = c->link.next;
      delete_constraint (qdpll, c);
    }
}


static LitID *
remove_internals_from_lits (QDPLL *qdpll, LitID *lits)
{
  /* Find last element. */
  LitID *e;
  for (e = lits; *e; e++)
    ;
  e--;
  QDPLL_ABORT_QDPLL (e < lits, "Empty lit-list!");

  LitID *p;
  for (p = lits; *p; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->is_internal)
        {
          assert (*e);
          *p-- = *e;
          *e-- = 0;
        }
    }

  return lits;
}


static int
qdo_has_outer_scope_unassigned_vars (QDPLL *qdpll, Scope *outer, QDPLLResult result)
{
  assert (result == QDPLL_RESULT_UNSAT || result == QDPLL_RESULT_SAT);
  assert (outer->type == QDPLL_QTYPE_FORALL || outer->type == QDPLL_QTYPE_EXISTS);
  assert (outer->nesting <= QDPLL_DEFAULT_SCOPE_NESTING + 1);
  assert (outer->type != QDPLL_QTYPE_FORALL || result == QDPLL_RESULT_UNSAT);
  assert (outer->type != QDPLL_QTYPE_EXISTS || result == QDPLL_RESULT_SAT);

  VarID *p, *e;
  for (p = outer->vars.start, e = outer->vars.top; p < e; p++)
    {
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, *p);
      if (!QDPLL_VAR_ASSIGNED(var))
        return 1;
    }

  return 0;
}

static void
qdo_fix_outer_scope_unassigned_vars_aux (QDPLL *qdpll, Scope *outer, VarIDStack *stack, Constraint *c, 
                                         char *mark_table, char *assignment_table)
{
  /* FIX: if the input formula is unsatisfiable due to an input clause with
     only universal literals, which were forall-reduced to get the empty clause,
     then we must consider also these reduced literals to compute a partial
     countermodel. I.e. go until 'c->size_lits', not 'c->num_lits'. */
  LitID *p, *e;
  for (p = c->lits, e = p + c->size_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->mode == QDPLL_VARMODE_UNIT)
        {
          assert (QDPLL_VAR_ASSIGNED (var));
          if ((!c->is_cube && var->scope->type == QDPLL_QTYPE_EXISTS) || 
              (c->is_cube && var->scope->type == QDPLL_QTYPE_FORALL))
            {
              /* Check mark table and push. */
              if (!mark_table[var->id])
                {
                  mark_table[var->id] = 1;
                  QDPLL_PUSH_STACK (qdpll->mm, *stack, var->id);
                }
            }
        }
      else
        {
          if (!QDPLL_VAR_ASSIGNED (var))
            {
              /* Set the value of required unassigned variables. */
              if ((var->scope == outer || var->user_scope == outer) && 
                  assignment_table[var->id] == QDPLL_ASSIGNMENT_UNDEF)
                {
                  if (QDPLL_LIT_NEG (lit))
                    {
                      if (!c->is_cube)
                        assignment_table[var->id] = QDPLL_ASSIGNMENT_TRUE;
                      else
                        assignment_table[var->id] = QDPLL_ASSIGNMENT_FALSE;
                    }
                  else
                    {
                      assert (QDPLL_LIT_POS (lit));
                      if (!c->is_cube)
                        assignment_table[var->id] = QDPLL_ASSIGNMENT_FALSE;
                      else
                        assignment_table[var->id] = QDPLL_ASSIGNMENT_TRUE;
                    }
                }
            }
        }
    }
}

/* Traverse the implication graph starting from 'qdpll->result_constraint' and
   search for unassigned universal (existential) literals of variables from
   the leftmost quantifier block in reachable clauses (cubes). Assign values
   to these variables in order NOT to satisfy clauses (falsify cubes). */
static void
qdo_fix_outer_scope_unassigned_vars (QDPLL *qdpll, Scope *outer, QDPLLResult result, 
                                     char *assignment_table)
{
  assert (result == QDPLL_RESULT_UNSAT || result == QDPLL_RESULT_SAT);
  assert (outer->type == QDPLL_QTYPE_FORALL || outer->type == QDPLL_QTYPE_EXISTS);
  assert (outer->nesting <= QDPLL_DEFAULT_SCOPE_NESTING + 1);
  assert (outer->type != QDPLL_QTYPE_FORALL || result == QDPLL_RESULT_UNSAT);
  assert (outer->type != QDPLL_QTYPE_EXISTS || result == QDPLL_RESULT_SAT);

  VarIDStack stack;
  QDPLL_INIT_STACK(stack);
  const unsigned int table_bytes = (qdpll_get_max_declared_var_id (qdpll) + 1) * sizeof (char);
  char * mark_table = (char *) qdpll_malloc (qdpll->mm, table_bytes);

  assert (qdpll->result_constraint);
  assert (qdpll->result_constraint->is_cube || result == QDPLL_RESULT_UNSAT);
  assert (!qdpll->result_constraint->is_cube || result == QDPLL_RESULT_SAT);
  qdo_fix_outer_scope_unassigned_vars_aux (qdpll, outer, &stack, qdpll->result_constraint, 
                                           mark_table, assignment_table);

  while (!QDPLL_EMPTY_STACK(stack))
    {
      VarID id = QDPLL_POP_STACK(stack);
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      assert (mark_table[var->id]);
      assert (QDPLL_VAR_ASSIGNED(var));
      assert (var->mode == QDPLL_VARMODE_UNIT);
      assert (var->scope->type != outer->type);
      assert (var->antecedent);
      assert (var->antecedent->is_cube || result == QDPLL_RESULT_UNSAT);
      assert (!var->antecedent->is_cube || result == QDPLL_RESULT_SAT);
      qdo_fix_outer_scope_unassigned_vars_aux (qdpll, outer, &stack, var->antecedent, 
                                               mark_table, assignment_table);
    }

  qdpll_free (qdpll->mm, mark_table, table_bytes);
  QDPLL_DELETE_STACK(qdpll->mm, stack);
}
 

/* Returns non-zero if 'c' contains a selector variable of a frame which has
   been popped off. In this case the clause has been effectively deleted from the
   formula although it is physically present in the clause list. */
static int
clause_has_popped_off_var (QDPLL *qdpll, Constraint *c)
{
  assert (!c->is_cube);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->is_internal)
        {
          /* 'var' is a selector variable of a popped off frame. */
          if (!var->is_cur_used_internal_var)
            return 1;
        }
      else
        return 0;
      /* Can immediately return if we see a user variable because internal
         ones appear at the left end of the list */
    }

  return 0;
}


/* Returns non-zero if 'c' contains a selector variable of a group which has
   been deactivated by 'qdpll_deactivate_clause_group'. In this case the
   clause has been effectively deleted from the formula although it is
   physically present in the clause list. */
static int
clause_has_inactive_var (QDPLL *qdpll, Constraint *c)
{
  assert (!c->is_cube);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
      if (var->is_internal)
        {
          assert (!var->is_cur_inactive_group_selector || var->is_cur_used_internal_var);
          /* 'var' is a selector variable of a deactivated clause group. */
          if (var->is_cur_inactive_group_selector)
            return 1;
        }
      else
        return 0;
      /* Can immediately return if we see a user variable because internal
         ones appear at the left end of the list */
    }

  return 0;
}


static void
qdpll_print_aux_scope (QDPLL *qdpll, Scope *s, FILE *out)
{
  if (QDPLL_SCOPE_EXISTS (s))
    fprintf (out, "e");
  else
    fprintf (out, "a");

  VarID *p, *e;
  for (p = s->vars.start, e = s->vars.top; p < e; p++)
    {
      /* For incremental use: do not print internal variables. */
      VarID id = *p;
      Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
      /* Print all variables if 's' is a user scope. Otherwise, print only
         free user variables. */
      if (!s->is_internal || (!var->is_internal && !var->user_scope))
        fprintf (out, " %u", id);
    }
  fprintf (out, " 0\n");
}


static ClauseGroupID
new_clause_group_aux (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->state.next_free_internal_var_id > qdpll->pcnf.size_vars, 
                     "Next free internal ID must be smaller than or equal to size of vars!");
  QDPLL_ABORT_QDPLL (qdpll->state.next_free_internal_var_id < qdpll->pcnf.size_user_vars, 
                     "Next free internal ID must be greater than or equal to size of user vars!");

  const VarID cur_size_vars = qdpll->pcnf.size_vars;
  if (qdpll->state.next_free_internal_var_id == cur_size_vars)
    {
      /* Enlarge variable table to store additional internal variable IDs. */
      assert ((cur_size_vars - qdpll->pcnf.size_user_vars) <= cur_size_vars);
      const unsigned int new_size_vars = cur_size_vars + DEFAULT_INTERNAL_VARS_INCREASE; 
      qdpll->pcnf.vars = (Var *) qdpll_realloc (qdpll->mm, qdpll->pcnf.vars,
                                                cur_size_vars * sizeof (Var),
                                                new_size_vars * sizeof (Var));
      qdpll->pcnf.size_vars = new_size_vars;
      assert (qdpll->pcnf.size_user_vars <= qdpll->pcnf.size_vars);
      assert_internal_vars_integrity (qdpll);
      if (qdpll->options.verbosity >= 2)
        fprintf (stderr, "Push: enlarging internal variables, new internal size %d.\n", 
                 qdpll->pcnf.size_vars - qdpll->pcnf.size_user_vars);
    }
  assert (qdpll->state.next_free_internal_var_id < qdpll->pcnf.size_vars);
  assert (qdpll->state.next_free_internal_var_id >= qdpll->pcnf.size_user_vars);

  /* We could also recycle internal IDs which are not used currently. However,
     the implementation would be more complex. Now, we always allocate group
     IDs in an incremental way. The user will never see ID multiple times when
     calling 'qdpll_new_clause_group' and 'delete_clause_group'. However, if
     push/pop API is used then frame indices are returned to the user, which
     can occur mutliple times. */

  VarID internal_id = qdpll->state.next_free_internal_var_id++;
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->state.cur_used_internal_vars, internal_id);
  /* ID 'clause_group_id' will be made public to the user via the API. */
  unsigned int clause_group_id = QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars);
  qdpll->state.cnt_created_clause_groups++;
  assert (clause_group_id >= qdpll->state.cnt_created_clause_groups);

  /* NOTE: always keep default scope as internal scope to store internal variables. */
  assert (qdpll->pcnf.scopes.first->is_internal);
  declare_and_init_variable (qdpll, qdpll->pcnf.scopes.first, internal_id, 1, 1);

  /* Set group index of internal variable. */
  assert (qdpll->pcnf.vars[internal_id].clause_group_id == 0);
  qdpll->pcnf.vars[internal_id].clause_group_id = clause_group_id;
  assert (qdpll->pcnf.vars[internal_id].clause_group_id > 0);

  /* Set flag to indicate that internal variable appears on the stack
     'qdpll->state.cur_used_internal_vars'. */
  assert (!qdpll->pcnf.vars[internal_id].is_cur_used_internal_var);
  qdpll->pcnf.vars[internal_id].is_cur_used_internal_var = 1;

  return clause_group_id;
}


static int
exists_clause_group_aux (QDPLL *qdpll, ClauseGroupID clause_group)
{
  /* Check if there is a valid entry (i.e. selector variable of group) in
     table 'qdpll->state.cur_used_internal_vars' at position 'clause_group'. */
  if (clause_group == 0 || 
      clause_group > QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars) || 
      !qdpll->state.cur_used_internal_vars.start[clause_group - 1])
    return 0;
  else
    return 1;
}


static void
delete_clause_group_aux (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!exists_clause_group_aux (qdpll, clause_group), 
                     "Invalid clause group ID!");

  /* Get selector variable ID of clause group from table. */
  unsigned int deleted_group_selector_var_id = 
    qdpll->state.cur_used_internal_vars.start[clause_group - 1];
  assert (deleted_group_selector_var_id);
  Var *deleted_group_selector_var = 
    VARID2VARPTR(qdpll->pcnf.vars, deleted_group_selector_var_id);

  /* Decrease number of active clause groups. */
  qdpll->state.cnt_created_clause_groups--;
  assert (qdpll->state.cnt_created_clause_groups < 
          QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));

  /* Store selector variable on other stack of deleted variables. */
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->state.popped_off_internal_vars, 
                   deleted_group_selector_var_id);

  /* Count the number of deleted original clauses to trigger cleanup
     later. Deleted learned clauses are not counted since they are deleted
     anyway according to the usual deletion schedule of learned clauses.
     NOTE: this count is exact since we never cound clauses multiple times;
     original clauses contain exactly one selector variable. */
  assert (deleted_group_selector_var->id);
  assert (deleted_group_selector_var->is_internal);
  /* Reset flag of group selector variable. */
  assert (deleted_group_selector_var->is_cur_used_internal_var);
  deleted_group_selector_var->is_cur_used_internal_var = 0;

  /* Reset entry of selector variable on stack of active variables. NOTE: in
     qdpll_pop, we in fact remove this entry from the stack by a pop
     operation. For clause groups in general, we just reset it to zero. */
  qdpll->state.cur_used_internal_vars.start[clause_group - 1] = 0;

  qdpll->state.popped_off_orig_clause_cnt += 
    QDPLL_COUNT_STACK(deleted_group_selector_var->pos_occ_clauses);
  QDPLL_ABORT_QDPLL(QDPLL_COUNT_STACK(deleted_group_selector_var->neg_occ_clauses) > 0, 
                    "Unexpected neg. occurrences of internal variable!");
}

/* Returns a pointer to the selector variable of the given clause group. */
static Var *
clause_group_to_var_ptr (QDPLL *qdpll, ClauseGroupID clause_group)
{
  assert (qdpll_exists_clause_group (qdpll, clause_group));
  VarID vid = qdpll->state.cur_used_internal_vars.start[clause_group - 1];
  assert (vid);
  return VARID2VARPTR(qdpll->pcnf.vars, vid);
}

static ClauseGroupID
get_open_clause_group_aux (QDPLL *qdpll)
{
  return qdpll->state.cur_open_group_id;
}

static void
recompute_var_act_scores_occs (QDPLL *qdpll, Constraint *c)
{
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, *p);
      increase_var_activity (qdpll, var, var->user_scope ? 
                             var->user_scope : var->scope);
    }
}


static void
recompute_var_act_scores (QDPLL *qdpll)
{
  /* Reset delta of variable activity like at initialization time. */
  qdpll->state.var_act_inc = qdpll->options.var_act_inc;
  /* Cleanup priority queue of variables. */
  while (var_pqueue_remove_first (qdpll))
    ;
  /* Optional: reset activity of variables to initial value. */
  Var *p, *e;
  for (p = qdpll->pcnf.vars, e = p + qdpll->pcnf.size_vars; p < e; p++)
    {
      if (p->id)
        p->priority = 1;
    }
  /* Optional: recompute activities based on original clauses, learned clauses
     and learned cubes. */
  Constraint *cp, *ce;
  for (cp = qdpll->pcnf.clauses.first; cp; cp = cp->link.next)
    recompute_var_act_scores_occs (qdpll, cp);

  for (cp = qdpll->pcnf.learnt_clauses.first; cp; cp = cp->link.next)
    recompute_var_act_scores_occs (qdpll, cp);

  for (cp = qdpll->pcnf.learnt_cubes.first; cp; cp = cp->link.next)
    recompute_var_act_scores_occs (qdpll, cp);
}

/* Consider a clause satisfied only if it is satisfied by a literal which is
left to the blocking literal, or by the blocking literal itself. Otherwise
flip blocking literal. */
static int
qdo_reconstruct_cnf_model_is_clause_empty (QDPLL * qdpll, Constraint * clause)
{
  assert (clause->qbcp_qbce_blocked);
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars, *sat_var = 0;
  LitID blocking_lit = clause->qbcp_qbce_blocking_lit;
  assert (blocking_lit);
  Var *blocking_var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);

  LitID *p, *e;
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);

      /* Stop and return 'clause is empty' if we see a variable to the right
         of blocking literal.*/
      if (blocking_var->scope->nesting < var->scope->nesting)
        return 1;

      if (!QDPLL_VAR_ASSIGNED (var))
        {
          /* Consider clause as nonempty when seeing unassigned variable to
             the left. */
          if (QDPLL_VAR_EXISTS (var))
            return 0;
        }
      else
        {
          if (QDPLL_LIT_NEG (lit))
            {
              if (QDPLL_VAR_ASSIGNED_FALSE (var))
                return 0;
            }
          else
            {
              assert (QDPLL_LIT_POS (lit));
              if (QDPLL_VAR_ASSIGNED_TRUE (var))
                return 0;
            }
        }
    }

  return 1;
}

/* Reconstruct assigment to variables of outermost existential block so that
   no clause containing variables of that block is falsified under the current
   assignment. Clauses may be falsified if the inout formula contains blocked
   clauses. Check currently blocked clauses in reverse order of discovering
   that they are blocked. If a blocked clause is unsatisfied, then flip the
   value of the blocking literal. Note that we do not reconstruct a full model
   of the CNF. We only make sure that the input formula under the assigment
   returned as QDIMACS output is satisfiable. */
static void
qdo_qbcp_qbce_reconstruct_cnf_model (QDPLL *qdpll, Scope *outer)
{
  if (qdpll->state.qdo_no_schedule_model_reconstruction)
    return;
  qdpll->state.qdo_no_schedule_model_reconstruction = 1;
  assert (outer);
  if (!QDPLL_EMPTY_STACK (qdpll->qbcp_qbce_blocked_clauses))
    {
      /* Consider clauses currently blocked in the input formula in reverse
         ordering. */
      ConstraintPtrStack *sp, *se;
      for (sp = qdpll->qbcp_qbce_blocked_clauses.top - 1, 
           se = qdpll->qbcp_qbce_blocked_clauses.start; se <= sp; sp--)
        {
          ConstraintPtrStack stack = *sp;
          if (QDPLL_EMPTY_STACK (stack))
            continue;
          Constraint **p, **e;
          for (p = stack.top - 1, e = stack.start; e <= p; p--)
            {
              Constraint *c = *p;
              assert (c->qbcp_qbce_blocked);
              /* Consider a clause satisfied only if it is satisfied by a literal which is
                 left to the blocking literal, or by the blocking literal itself. Otherwise
                 flip blocking literal. */
              if (qdo_reconstruct_cnf_model_is_clause_empty (qdpll, c))
                {
                  LitID blocking_lit = c->qbcp_qbce_blocking_lit;
                  assert (blocking_lit);
                  Var *var = LIT2VARPTR (qdpll->pcnf.vars, blocking_lit);
                  assert (QDPLL_VAR_EXISTS (var));
                  assert (QDPLL_VAR_ASSIGNED (var));
                  assert ((QDPLL_LIT_NEG (blocking_lit) && QDPLL_VAR_ASSIGNED_TRUE (var)) || 
                          (QDPLL_LIT_POS (blocking_lit) && QDPLL_VAR_ASSIGNED_FALSE (var)));
                  /* Flip assignment of the blocking literal's variable. */
                  var->assignment = -var->assignment;
                  assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
                  if (qdpll->options.verbosity >= 2)
                    {
                      fprintf (stderr, "Formerly unsatisfied blocked clause: ");
                      print_constraint (qdpll, c);
                      fprintf (stderr, "  -> now satisfied by flipping literal %d\n", 
                               blocking_lit);
                    }
                }
              else 
                {
                  if (qdpll->options.verbosity >= 2)
                    {
                      fprintf (stderr, "Satisfied blocked clause: ");
                      print_constraint (qdpll, c);
                    }
                }
            }
        }
    }
}

/* -------------------- START: PUBLIC FUNCTIONS --------------------*/

QDPLL *
qdpll_create ()
{
  QDPLLMemMan *mm = qdpll_create_mem_man ();
  QDPLL *qdpll = (QDPLL *) qdpll_malloc (mm, sizeof (QDPLL));
  qdpll->mm = mm;
  Scope *default_scope = (Scope *) qdpll_malloc (mm, sizeof (Scope));
  default_scope->type = QDPLL_QTYPE_EXISTS;
  assert (!default_scope->is_internal);
  default_scope->is_internal = 1;
  QDPLL_ABORT_QDPLL (default_scope->nesting != QDPLL_DEFAULT_SCOPE_NESTING, 
                     "Nesting of default scope must be zero.");
  LINK_LAST (qdpll->pcnf.scopes, default_scope, link);
  QDPLL_ABORT_QDPLL(DEFAULT_VARS_SIZE <= 0, 
                    "Expecting vars-size greater than zero!");
  QDPLL_ABORT_QDPLL(DEFAULT_USER_VARS_SIZE <= 0, 
                    "Expecting user-vars-size greater than zero!");
  QDPLL_ABORT_QDPLL(DEFAULT_VARS_SIZE < DEFAULT_USER_VARS_SIZE, 
                    "Expecting user-vars-size smaller than or equal to vars-size!");
  QDPLL_ABORT_QDPLL(DEFAULT_INTERNAL_VARS_INCREASE <= 0, 
                    "Default increase value of internal vars must be greater than zero!");
  qdpll->pcnf.size_vars = DEFAULT_VARS_SIZE;
  qdpll->pcnf.size_user_vars = DEFAULT_USER_VARS_SIZE;
  qdpll->pcnf.vars =
    (Var *) qdpll_malloc (mm, DEFAULT_VARS_SIZE * sizeof (Var));
  qdpll->state.next_free_internal_var_id = qdpll->pcnf.size_user_vars;

  PriorityQueue *pqueue = pqueue_create (mm, 1);
  qdpll->qpup_nodes = pqueue;

  /* Set default options. */

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  qdpll->options.elim_univ_dynamic_switch_delay = 
    ELIM_UNIV_DYNAMIC_SWITCH_DELAY_INIT_VAL;
  QDPLL_ABORT_QDPLL (qdpll->options.elim_univ_dynamic_switch_delay == 0, 
                     "expecting value greater than zero for elim-univ dynamic switch delay!");
#endif

  /* Empty formula watching enabled by default, must schedule update. */
  qdpll->state.empty_formula_watcher_scheduled_update = 1;
  /* Dynamic QBCE enabled by default. */
  assert (!qdpll->options.no_qbce_dynamic);
  /* Set QBCE default cutoff values. */
  qdpll->options.qbcp_qbce_max_clause_size = 50;
  qdpll->options.qbcp_qbce_find_witness_max_occs = 50;
  /* Set default trivial truth options. */
  qdpll->options.trivial_truth_pow2_call_interval = 10; 
  qdpll->options.trivial_truth_decision_limit = 1000000; 
  qdpll->options.trivial_truth_disable_calls_threshold = 1; 
  qdpll->options.trivial_truth_disable_time_threshold = 5.000; 
  qdpll->options.trivial_truth_disable_cnf_threshold = 500000; 
  /* Set default trivial falsity options. */
  qdpll->options.trivial_falsity_pow2_call_interval = 10; 
  qdpll->options.trivial_falsity_decision_limit = 1000000; 
  qdpll->options.trivial_falsity_disable_calls_threshold = 1; 
  qdpll->options.trivial_falsity_disable_time_threshold = 5.000; 
  qdpll->options.trivial_falsity_disable_cnf_threshold = 500000; 
  qdpll->options.trivial_falsity_partial_mus_assumptions = 1; 
  /* Set default dynamic nenofex options. */
  qdpll->options.dyn_nenofex_pow2_call_interval = 11; 
  qdpll->options.dyn_nenofex_disable_calls_threshold = 5; 
  qdpll->options.dyn_nenofex_disable_time_threshold = 0.125; 
  qdpll->options.dyn_nenofex_disable_cnf_threshold = 500000; 

  /* NEW: decision heuristics 'QTYPE' turned out to perform MUCH better than
     the old default one 'SDCL'. */
  qdpll->options.dh = QDPLL_DH_QTYPE;

  if (DEFAULT_DEPMANTYPE == QDPLL_DEPMAN_TYPE_QDAG)
    {
      qdpll->options.depman_qdag = 1;
      assert (!qdpll->options.depman_simple);
    }
  else if (DEFAULT_DEPMANTYPE == QDPLL_DEPMAN_TYPE_SIMPLE)
    {
      qdpll->options.depman_simple = 1;
      assert (!qdpll->options.depman_qdag);
    }
  else
    {
      QDPLL_ABORT_QDPLL (1, "Unexpected value for DM!");
    }
  qdpll->dm = (QDPLLDepManGeneric *)
    qdpll_qdag_dep_man_create (qdpll->mm,
                               &(qdpll->pcnf),
                               DEFAULT_DEPMANTYPE,
                               qdpll->options.
                               depman_qdag_print_deps_by_search, qdpll);

  qdpll->trace_scope = &print_qrp_scope;
  qdpll->trace_constraint = &print_qrp_constraint;
  qdpll->trace_full_cover_set = &print_qrp_full_cover_set;

  qdpll->options.var_act_inc = 1.0;
  qdpll->state.var_act_inc = qdpll->options.var_act_inc;
  qdpll->options.var_act_decay_ifactor = 0.95;
  qdpll->var_act_decay = 1.0 / qdpll->options.var_act_decay_ifactor;

  qdpll->options.lclauses_delfactor = 0.5;
  qdpll->options.lcubes_delfactor = 0.5;

  qdpll->options.lclauses_resize_value = LCLAUSES_RESIZE_VAL;
  qdpll->options.lcubes_resize_value = LCUBES_RESIZE_VAL;
  qdpll->options.lclauses_init_size = LCLAUSES_INIT_VAL;
  qdpll->options.lcubes_init_size = LCUBES_INIT_VAL;

  qdpll->options.irestart_dist_init = IRESTART_DIST_INIT_VAL;
  qdpll->options.irestart_dist_inc = IRESTART_DIST_INC_INIT_VAL;
  qdpll->state.irestart_dist = qdpll->options.irestart_dist_init;

  qdpll->options.orestart_dist_init = ORESTART_DIST_INIT_VAL;
  qdpll->options.orestart_dist_inc = ORESTART_DIST_INC_INIT_VAL;
  qdpll->state.orestart_dist = qdpll->options.orestart_dist_init;

  qdpll->options.lclauses_min_init_size = LCLAUSES_MIN_INIT_VAL;
  qdpll->options.lclauses_max_init_size = LCLAUSES_MAX_INIT_VAL;
  qdpll->options.lcubes_min_init_size = LCUBES_MIN_INIT_VAL;
  qdpll->options.lcubes_max_init_size = LCUBES_MAX_INIT_VAL;

  qdpll->options.var_act_bias = 1;

  /* Size of learnt clauses/cubes list will be set when solving starts. */

  /* Must also set seed when new seed is configured. */
  srand (qdpll->options.seed);

  /* Maintain blocked clauses and marked clauses found at each decision
     level. */
  assert (qdpll->state.decision_level == 0);
  ConstraintPtrStack cstack;
  QDPLL_INIT_STACK (cstack);
  QDPLL_PUSH_STACK (qdpll->mm, qdpll->qbcp_qbce_blocked_clauses, cstack);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) == 
          qdpll->state.decision_level + 1);
  /* Marked clauses per decision level. */
  QDPLL_PUSH_STACK (qdpll->mm, qdpll->qbcp_qbce_marked_clauses, cstack);
  assert (QDPLL_COUNT_STACK (qdpll->qbcp_qbce_marked_clauses) == 
          qdpll->state.decision_level + 1);

  qdpll->trivial_falsity_solver = picosat_init ();
  qdpll->trivial_truth_solver = picosat_init ();

  qdpll->nenofex_oracle = nenofex_create ();
  /* Push default configuration strings used to bound execution time of
     Nenofex. Each time a new instance of Nenofex is created, these configuration
     strings will be added. */
  QDPLL_PUSH_STACK (qdpll->mm, qdpll->nenofex_option_strings, 
                    "--abs-graph-size-cutoff=1.5");
  QDPLL_PUSH_STACK (qdpll->mm, qdpll->nenofex_option_strings, 
                    "--sat-solver-dec-limit=1000");

  return qdpll;
}


void
qdpll_delete (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLLMemMan *mm = qdpll->mm;

  QDPLL_DELETE_STACK (mm, qdpll->add_stack);
  QDPLL_DELETE_STACK (mm, qdpll->add_stack_tmp);
  QDPLL_DELETE_STACK (mm, qdpll->wreason_a);
  QDPLL_DELETE_STACK (mm, qdpll->wreason_e);
  QDPLL_DELETE_STACK (mm, qdpll->dec_vars);
  QDPLL_DELETE_STACK (mm, qdpll->smaller_type_lits);
  pqueue_delete (mm, qdpll->qpup_nodes);
  QDPLL_DELETE_STACK (mm, qdpll->qpup_vars);
  QDPLL_DELETE_STACK (mm, qdpll->qpup_units);
  QDPLL_DELETE_STACK (mm, qdpll->qpup_kept_lits);
  QDPLL_DELETE_STACK (mm, qdpll->qpup_weak_predict_lits);
  QDPLL_DELETE_STACK (mm, qdpll->state.popped_off_internal_vars);
  QDPLL_DELETE_STACK (mm, qdpll->state.cur_used_internal_vars);
  QDPLL_DELETE_STACK (mm, qdpll->pcnf.user_scope_ptrs);
  QDPLL_DELETE_STACK (mm, qdpll->internal_cover_lits);
  QDPLL_DELETE_STACK (mm, qdpll->user_given_assumptions);
  QDPLL_DELETE_STACK (mm, qdpll->empty_formula_watchers_per_dec_level);
  QDPLL_DELETE_STACK (mm, qdpll->empty_formula_watching_blit_occs);
  QDPLL_DELETE_STACK (mm, qdpll->qbcp_qbce_maybe_blocked_clauses);
  QDPLL_DELETE_STACK (mm, qdpll->qbcp_qbce_relevant_vars_in_new_input_clauses);
  QDPLL_DELETE_STACK (mm, qdpll->qdo_dummy_assigned_vars);
  QDPLL_DELETE_STACK (mm, qdpll->reschedule_qbce_marked_clauses);
  QDPLL_DELETE_STACK (mm, qdpll->nenofex_option_strings);
  ConstraintPtrStack *csp, *cse;
  /* NOTE: must go until stack.end, not just stack.top, because we did not
     free the stacks after pop. */
  for (csp = qdpll->qbcp_qbce_blocked_clauses.start, 
         cse = qdpll->qbcp_qbce_blocked_clauses.end; csp < cse; csp++)
    {
      ConstraintPtrStack stack = *csp;
      QDPLL_DELETE_STACK (mm, stack);
    }
  QDPLL_DELETE_STACK (mm, qdpll->qbcp_qbce_blocked_clauses);
  /* Marked clauses per decision level. */
  /* NOTE: must go until stack.end, not just stack.top, because we did not
     free the stacks after pop. */
  for (csp = qdpll->qbcp_qbce_marked_clauses.start, 
         cse = qdpll->qbcp_qbce_marked_clauses.end; csp < cse; csp++)
    {
      ConstraintPtrStack stack = *csp;
      QDPLL_DELETE_STACK (mm, stack);
    }
  QDPLL_DELETE_STACK (mm, qdpll->qbcp_qbce_marked_clauses);

  if (qdpll->qdo_assignment_table)
    {
      assert (qdpll->qdo_table_bytes);
      qdpll_free (qdpll->mm, qdpll->qdo_assignment_table, qdpll->qdo_table_bytes);
      qdpll->qdo_table_bytes = 0;
      qdpll->qdo_assignment_table = 0;
    }

  if (qdpll->assumption_lits_constraint)
    delete_constraint (qdpll, qdpll->assumption_lits_constraint);

  /* Delete scopes. */
  delete_scope_list (qdpll, &qdpll->pcnf.scopes);
  delete_scope_list (qdpll, &qdpll->pcnf.user_scopes);

  /* Delete variables. Can ignore variable with ID 0. */
  Var *vars = qdpll->pcnf.vars;
  Var *v, *ve;
  for (v = vars, ve = vars + qdpll->pcnf.size_vars; v < ve; v++)
    {
      if (v->id)
        delete_variable (qdpll, v);
    }
  qdpll_free (mm, vars, qdpll->pcnf.size_vars * sizeof (Var));

  /* Delete clauses. */
  qdpll_delete_constraint_list (qdpll, &(qdpll->pcnf.clauses));
  /* Delete learnt clauses. */
  qdpll_delete_constraint_list (qdpll, &(qdpll->pcnf.learnt_clauses));
  /* Delete learnt cubes. */
  qdpll_delete_constraint_list (qdpll, &(qdpll->pcnf.learnt_cubes));
  /* Delete cover sets, if any. */
  if (qdpll->state.collect_full_cover_sets)
    qdpll_delete_constraint_list (qdpll, &(qdpll->cover_sets));

  qdpll_free (mm, qdpll->var_pqueue, qdpll->size_var_pqueue * sizeof (VarID));
  qdpll_free (mm, qdpll->assigned_vars,
              size_assigned_vars (qdpll) * sizeof (VarID));

  assert (qdpll->dm);
  assert ((qdpll->options.depman_simple && !qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && !qdpll->options.depman_qdag));
  /* Delete dependency manager. 
     IMPORTANT NOTE: all heap-memory managed by DepMan must already have been
     deleted before! */
  qdpll_qdag_dep_man_delete ((QDPLLDepManQDAG *) qdpll->dm);

  picosat_reset (qdpll->trivial_falsity_solver);
  picosat_reset (qdpll->trivial_truth_solver);

  nenofex_delete (qdpll->nenofex_oracle);

  qdpll_free (mm, qdpll, sizeof (QDPLL));
  qdpll_delete_mem_man (mm);
}


/* Configure solver instance via configuration string. 
   Returns null pointer on success and error string otherwise. */
char *
qdpll_configure (QDPLL * qdpll, char *configure_str)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  char *result = 0;

  if (!strncmp (configure_str, "--trace", strlen ("--trace")))
    {
      qdpll->options.trace = TRACE_QRP;

      configure_str += strlen ("--trace");
      if (!strcmp (configure_str, "=bqrp"))
        {
          qdpll->options.trace = TRACE_BQRP;
          qdpll->trace_scope = &print_bqrp_scope;
          qdpll->trace_constraint = &print_bqrp_constraint;
          qdpll->trace_full_cover_set = &print_bqrp_full_cover_set;
        }
      else if (strlen (configure_str) != 0 && strcmp (configure_str, "=qrp"))
        QDPLL_ABORT_QDPLL (1, "unknown tracing format!");
    }
    else if (!strcmp (configure_str, "--qbcp-qbce-watcher-list-mtf"))
      {
        qdpll->options.qbcp_qbce_watcher_list_mtf = 1;
      }
#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
    else if (!strcmp (configure_str, "--elim-univ-dynamic-switch"))
      {
        qdpll->options.elim_univ_dynamic_switch = 1;
      }
    else if (!strncmp
        (configure_str, "--elim-univ-dynamic-switch-delay=", strlen ("--elim-univ-dynamic-switch-delay=")))
    {
      configure_str += strlen ("--elim-univ-dynamic-switch-delay=");
      if (isnumstr (configure_str))
        {
          qdpll->options.elim_univ_dynamic_switch_delay = atoi (configure_str);
          if (qdpll->options.elim_univ_dynamic_switch_delay == 0)
            result = "Expecting value greater than 0 after '--elim-univ-dynamic-switch-delay='";
        }
      else
        result = "Expecting number after '--elim-univ-dynamic-switch-delay='";
    }
    else if (!strncmp
        (configure_str, "--elim-univ-dynamic-success-threshold=", strlen ("--elim-univ-dynamic-success-threshold=")))
    {
      configure_str += strlen ("--elim-univ-dynamic-success-threshold=");
      if (isnumstr (configure_str))
        {
          qdpll->options.elim_univ_dynamic_success_threshold = atoi (configure_str);
          if (qdpll->options.elim_univ_dynamic_success_threshold > 100)
            result = "Expecting value smaller than or equal to 100 after '--elim-univ-dynamic-success-threshold='";
        }
      else
        result = "Expecting number after '--elim-univ-dynamic-success-threshold='";
    }
#endif
    else if (!strncmp
        (configure_str, "--qbce-witness-max-occs=", strlen ("--qbce-witness-max-occs=")))
    {
      configure_str += strlen ("--qbce-witness-max-occs=");
      if (isnumstr (configure_str))
        {
          qdpll->options.qbcp_qbce_find_witness_max_occs = atoi (configure_str);
        }
      else
        result = "Expecting number after '--qbce-witness-max-occs='";
    }
    else if (!strncmp
        (configure_str, "--qbce-max-clause-size=", strlen ("--qbce-max-clause-size=")))
    {
      configure_str += strlen ("--qbce-max-clause-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.qbcp_qbce_max_clause_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--qbce-max-clause-size='";
    }
  else if (!strcmp (configure_str, "--qbce-preprocessing"))
    {
      qdpll->options.qbce_preprocessing = 1;
      if (qdpll->options.qbce_inprocessing || !qdpll->options.no_qbce_dynamic)
        result = "Must enable at most one of QBCE pre/inprocessing or dynamic variant";
    }
  else if (!strcmp (configure_str, "--qbce-inprocessing"))
    {
      qdpll->options.qbce_inprocessing = 1;
      if (qdpll->options.qbce_preprocessing || !qdpll->options.no_qbce_dynamic)
        result = "Must enable at most one of QBCE pre/inprocessing or dynamic variant";
    }
  else if (!strcmp (configure_str, "--no-qbce-dynamic"))
    {
      qdpll->options.no_qbce_dynamic = 1;
    }
  else if (!strcmp (configure_str, "--no-empty-formula-watching"))
    {
      qdpll->options.no_empty_formula_watching = 1;
      qdpll->state.empty_formula_watcher_scheduled_update = 0;
    }
  else if (!strcmp (configure_str, "--no-trivial-falsity"))
    {
      qdpll->options.no_trivial_falsity = 1;
    }
  else if (!strncmp
           (configure_str, "--trivial-falsity-pow2-call-interval=", 
            strlen ("--trivial-falsity-pow2-call-interval=")))
    {
      configure_str += strlen ("--trivial-falsity-pow2-call-interval=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          if (res < 0)
            qdpll->options.trivial_falsity_pow2_call_interval = 0;
          else if (res > 31)
            qdpll->options.trivial_falsity_pow2_call_interval = 31;
          else
            qdpll->options.trivial_falsity_pow2_call_interval = res;
        }
      else
        result = "Expecting number after '--trivial-falsity-pow2-call-interval='";
    }
  else if (!strncmp
           (configure_str, "--dyn-nenofex-pow2-call-interval=", 
            strlen ("--dyn-nenofex-pow2-call-interval=")))
    {
      configure_str += strlen ("--dyn-nenofex-pow2-call-interval=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          if (res < 0)
            qdpll->options.dyn_nenofex_pow2_call_interval = 0;
          else if (res > 31)
            qdpll->options.dyn_nenofex_pow2_call_interval = 31;
          else
            qdpll->options.dyn_nenofex_pow2_call_interval = res;
        }
      else
        result = "Expecting number after '--dyn-nenofex-pow2-call-interval='";
    }
  else if (!strncmp
           (configure_str, "--dyn-nenofex-disable-calls-threshold=", 
            strlen ("--dyn-nenofex-disable-calls-threshold=")))
    {
      configure_str += strlen ("--dyn-nenofex-disable-calls-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.dyn_nenofex_disable_calls_threshold = res;
        }
      else
        result = "Expecting number after '--dyn-nenofex-disable-calls-threshold='";
    }
  else if (!strncmp (configure_str, "--dyn-nenofex-disable-time-threshold=", 
                  strlen ("--dyn-nenofex-disable-time-threshold=")))
    {
      configure_str += strlen ("--dyn-nenofex-disable-time-threshold=");
      if (isnumstr (configure_str))
        qdpll->options.dyn_nenofex_disable_time_threshold = strtod (configure_str, 0);
      else
        result = "Expecting real number after '--dyn-nenofex-disable-time-threshold='";
    }
  else if (!strncmp
           (configure_str, "--dyn-nenofex-disable-cnf-threshold=", 
            strlen ("--dyn-nenofex-disable-cnf-threshold=")))
    {
      configure_str += strlen ("--dyn-nenofex-disable-cnf-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.dyn_nenofex_disable_cnf_threshold = res;
        }
      else
        result = "Expecting number after '--dyn-nenofex-disable-cnf-threshold='";
    }
  else if (!strncmp
           (configure_str, "--trivial-falsity-disable-cnf-threshold=", 
            strlen ("--trivial-falsity-disable-cnf-threshold=")))
    {
      configure_str += strlen ("--trivial-falsity-disable-cnf-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_falsity_disable_cnf_threshold = res;
        }
      else
        result = "Expecting number after '--trivial-falsity-disable-cnf-threshold='";
    }
  else if (!strncmp
           (configure_str, "--trivial-falsity-disable-calls-threshold=", 
            strlen ("--trivial-falsity-disable-calls-threshold=")))
    {
      configure_str += strlen ("--trivial-falsity-disable-calls-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_falsity_disable_calls_threshold = res;
        }
      else
        result = "Expecting number after '--trivial-falsity-disable-calls-threshold='";
    }
  else
    if (!strncmp (configure_str, "--trivial-falsity-disable-time-threshold=", 
                  strlen ("--trivial-falsity-disable-time-threshold=")))
    {
      configure_str += strlen ("--trivial-falsity-disable-time-threshold=");
      if (isnumstr (configure_str))
        qdpll->options.trivial_falsity_disable_time_threshold = strtod (configure_str, 0);
      else
        result = "Expecting real number after '--trivial-falsity-disable-time-threshold='";
    }
  else if (!strncmp
           (configure_str, "--trivial-falsity-decision-limit=", 
            strlen ("--trivial-falsity-decision-limit=")))
    {
      configure_str += strlen ("--trivial-falsity-decision-limit=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_falsity_decision_limit = res;
        }
      else
        result = "Expecting number after '--trivial-falsity-decision-limit='";
    }
  else if (!strcmp (configure_str, "--trivial-falsity-partial-mus-assumptions"))
    {
      qdpll->options.trivial_falsity_partial_mus_assumptions = 1;
    }
  else if (!strcmp (configure_str, "--no-trivial-truth"))
    {
      qdpll->options.no_trivial_truth = 1;
    }
  else if (!strncmp
           (configure_str, "--trivial-truth-pow2-call-interval=", 
            strlen ("--trivial-truth-pow2-call-interval=")))
    {
      configure_str += strlen ("--trivial-truth-pow2-call-interval=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          if (res < 0)
            qdpll->options.trivial_truth_pow2_call_interval = 0;
          else if (res > 31)
            qdpll->options.trivial_truth_pow2_call_interval = 31;
          else
            qdpll->options.trivial_truth_pow2_call_interval = res;
        }
      else
        result = "Expecting number after '--trivial-truth-pow2-call-interval='";
    }
  else if (!strncmp
           (configure_str, "--trivial-truth-disable-calls-threshold=", 
            strlen ("--trivial-truth-disable-calls-threshold=")))
    {
      configure_str += strlen ("--trivial-truth-disable-calls-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_truth_disable_calls_threshold = res;
        }
      else
        result = "Expecting number after '--trivial-truth-disable-calls-threshold='";
    }
  else
    if (!strncmp (configure_str, "--trivial-truth-disable-time-threshold=", 
                  strlen ("--trivial-truth-disable-time-threshold=")))
    {
      configure_str += strlen ("--trivial-truth-disable-time-threshold=");
      if (isnumstr (configure_str))
        qdpll->options.trivial_truth_disable_time_threshold = strtod (configure_str, 0);
      else
        result = "Expecting real number after '--trivial-truth-disable-time-threshold='";
    }
  else if (!strncmp
           (configure_str, "--trivial-truth-decision-limit=", 
            strlen ("--trivial-truth-decision-limit=")))
    {
      configure_str += strlen ("--trivial-truth-decision-limit=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_truth_decision_limit = res;
        }
      else
        result = "Expecting number after '--trivial-truth-decision-limit='";
    }
  else if (!strncmp
           (configure_str, "--trivial-truth-disable-cnf-threshold=", 
            strlen ("--trivial-truth-disable-cnf-threshold=")))
    {
      configure_str += strlen ("--trivial-truth-disable-cnf-threshold=");
      if (isnumstr (configure_str))
        {
          int res = atoi (configure_str);
          qdpll->options.trivial_truth_disable_cnf_threshold = res;
        }
      else
        result = "Expecting number after '--trivial-truth-disable-cnf-threshold='";
    }
  else if (!strcmp (configure_str, "--no-dynamic-nenofex"))
    {
      qdpll->options.no_dynamic_nenofex = 1;
    }
  else if (!strcmp (configure_str, "--dyn-nenofex-ignore-sat"))
    {
      qdpll->options.dyn_nenofex_ignore_sat = 1;
    }
  else if (!strcmp (configure_str, "--dyn-nenofex-ignore-unsat"))
    {
      qdpll->options.dyn_nenofex_ignore_unsat = 1;
    }
  else
    if (!strncmp
        (configure_str, "--nenofex-option=", strlen ("--nenofex-option=")))
    {
      /* Collect Nenofex conigure string to be passed to Nenofex later. */
      configure_str += strlen ("--nenofex-option=");
      QDPLL_PUSH_STACK (qdpll->mm, qdpll->nenofex_option_strings, configure_str);
    }
  else if (!strcmp (configure_str, "--traditional-qcdcl"))
    {
      qdpll->options.traditional_qcdcl = qdpll->options.no_qpup_cdcl = qdpll->options.no_qpup_sdcl = 1;
    }
  else if (!strcmp (configure_str, "--no-qpup-cdcl"))
    {
      qdpll->options.no_qpup_cdcl = 1;
      qdpll->options.traditional_qcdcl = 1;
    }
  else if (!strcmp (configure_str, "--no-qpup-sdcl"))
    {
      qdpll->options.no_qpup_sdcl = 1;
      qdpll->options.traditional_qcdcl = 1;
    }
  else if (!strcmp (configure_str, "--incremental-use"))
    {
      qdpll->options.incremental_use = 1;
      /* Empty formula watching, dynamic nenofex tests, trivial falsity, and
         trivial truth tests must be disabled in incremental use. */
      qdpll->options.no_empty_formula_watching = 1;
      qdpll->options.no_dynamic_nenofex = 1;
      qdpll->options.no_trivial_falsity = 1;
      qdpll->options.no_trivial_truth = 1;
    }
  else if (!strcmp (configure_str, "--no-lazy-qpup"))
    {
      qdpll->options.no_lazy_qpup = 1;
    }
  else if (!strcmp (configure_str, "--long-dist-res"))
    {
      qdpll->options.long_dist_res = 1;
    }
  else if (!strcmp (configure_str, "--bump-vars-once"))
    {
      qdpll->options.bump_vars_once = 1;
    }
  else if (!strcmp (configure_str, "--no-pure-literals"))
    {
      qdpll->options.no_pure_literals = 1;
    }
  else if (!strcmp (configure_str, "--no-spure-literals"))
    {
      qdpll->options.no_spure_literals = 1;
    }
  else if (!strcmp (configure_str, "--no-cdcl"))
    {
      qdpll->options.no_cdcl = 1;
    }
  else if (!strcmp (configure_str, "--no-sdcl"))
    {
      qdpll->options.no_sdcl = 1;
    }
  else if (!strcmp (configure_str, "--no-unit-mtf"))
    {
      qdpll->options.no_unit_mtf = 1;
    }
  else if (!strcmp (configure_str, "--no-res-mtf"))
    {
      qdpll->options.no_res_mtf = 1;
    }
  else
    if (!strncmp
        (configure_str, "--var-act-bias=", strlen ("--var-act-bias=")))
    {
      configure_str += strlen ("--var-act-bias=");
      if (isnumstr (configure_str))
        {
          qdpll->options.var_act_bias = atoi (configure_str);
        }
      else
        result = "Expecting number after '--var-act-bias='";
    }
  else if (!strcmp (configure_str, "--no-univ-cache"))
    {
      qdpll->options.no_univ_cache = 1;
    }
  else if (!strcmp (configure_str, "--no-exists-cache"))
    {
      qdpll->options.no_exists_cache = 1;
    }
  else
    if (!strncmp
        (configure_str, "--no-lin-lcubes-inc",
         strlen ("--no-lin-lcubes-inc")))
    {
      qdpll->options.no_lin_lcubes_inc = 1;
    }
  else
    if (!strncmp
        (configure_str, "--no-lin-lclauses-inc",
         strlen ("--no-lin-lclauses-inc")))
    {
      qdpll->options.no_lin_lclauses_inc = 1;
    }
  else
    if (!strncmp
        (configure_str, "--no-lin-orestart-inc",
         strlen ("--no-lin-orestart-inc")))
    {
      qdpll->options.no_lin_orestart_inc = 1;
    }
  else
    if (!strncmp
        (configure_str, "--no-lin-irestart-inc",
         strlen ("--no-lin-irestart-inc")))
    {
      qdpll->options.no_lin_irestart_inc = 1;
    }
  else
    if (!strncmp
        (configure_str, "--orestart-dist-init=",
         strlen ("--orestart-dist-init=")))
    {
      configure_str += strlen ("--orestart-dist-init=");
      if (isnumstr (configure_str))
        {
          qdpll->options.orestart_dist_init = atoi (configure_str);
          qdpll->state.orestart_dist = qdpll->options.orestart_dist_init;
        }
      else
        result = "Expecting number after '--orestart-dist-init='";
    }
  else
    if (!strncmp
        (configure_str, "--orestart-dist-inc=",
         strlen ("--orestart-dist-inc=")))
    {
      configure_str += strlen ("--orestart-dist-inc=");
      if (isnumstr (configure_str))
        {
          qdpll->options.orestart_dist_inc = atoi (configure_str);
        }
      else
        result = "Expecting number after '--orestart-dist-inc'";
    }
  else
    if (!strncmp
        (configure_str, "--irestart-dist-init=",
         strlen ("--irestart-dist-init=")))
    {
      configure_str += strlen ("--irestart-dist-init=");
      if (isnumstr (configure_str))
        {
          qdpll->options.irestart_dist_init = atoi (configure_str);
          qdpll->state.irestart_dist = qdpll->options.irestart_dist_init;
        }
      else
        result = "Expecting number after '--irestart-dist-init='";
    }
  else
    if (!strncmp
        (configure_str, "--irestart-dist-inc=",
         strlen ("--irestart-dist-inc=")))
    {
      configure_str += strlen ("--irestart-dist-inc=");
      if (isnumstr (configure_str))
        {
          qdpll->options.irestart_dist_inc = atoi (configure_str);
        }
      else
        result = "Expecting number after '--irestart-dist-inc'";
    }
  else
    if (!strncmp
        (configure_str, "--lclauses-init-size=",
         strlen ("--lclauses-init-size=")))
    {
      configure_str += strlen ("--lclauses-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lclauses_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lclauses-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lclauses-min-init-size=",
         strlen ("--lclauses-min-init-size=")))
    {
      configure_str += strlen ("--lclauses-min-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lclauses_min_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lclauses-min-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lclauses-max-init-size=",
         strlen ("--lclauses-max-init-size=")))
    {
      configure_str += strlen ("--lclauses-max-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lclauses_max_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lclauses-max-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lcubes-min-init-size=",
         strlen ("--lcubes-min-init-size=")))
    {
      configure_str += strlen ("--lcubes-min-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lcubes_min_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lcubes-min-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lcubes-max-init-size=",
         strlen ("--lcubes-max-init-size=")))
    {
      configure_str += strlen ("--lcubes-max-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lcubes_max_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lcubes-max-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lcubes-init-size=",
         strlen ("--lcubes-init-size=")))
    {
      configure_str += strlen ("--lcubes-init-size=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lcubes_init_size = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lcubes-init-size='";
    }
  else
    if (!strncmp
        (configure_str, "--lclauses-resize-value=",
         strlen ("--lclauses-resize-value=")))
    {
      configure_str += strlen ("--lclauses-resize-value=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lclauses_resize_value = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lclauses-resize-value='";
    }
  else
    if (!strncmp
        (configure_str, "--lcubes-resize-value=",
         strlen ("--lcubes-resize-value=")))
    {
      configure_str += strlen ("--lcubes_resize_value=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lcubes_resize_value = atoi (configure_str);
        }
      else
        result = "Expecting number after '--lcubes-resize-value='";
    }
  else
    if (!strncmp (configure_str, "--var-act-inc=", strlen ("--var-act-inc=")))
    {
      configure_str += strlen ("--var-act-inc=");
      if (isnumstr (configure_str))
        {
          qdpll->options.var_act_inc = strtod (configure_str, 0);
          qdpll->state.var_act_inc = qdpll->options.var_act_inc;
        }
      else
        result = "Expecting real number after '--var-act-inc='";
    }
  else
    if (!strncmp
        (configure_str, "--var-act-dec-ifactor=",
         strlen ("--var-act-dec-ifactor=")))
    {
      configure_str += strlen ("--var-act-dec-ifactor=");
      if (isnumstr (configure_str))
        {
          qdpll->options.var_act_decay_ifactor = strtod (configure_str, 0);
          qdpll->var_act_decay = 1.0 / qdpll->options.var_act_decay_ifactor;
        }
      else
        result = "Expecting real number after '--var-act-dec-ifactor='";
    }
  else
    if (!strncmp
        (configure_str, "--lclauses-delfactor=",
         strlen ("--lclauses-delfactor=")))
    {
      configure_str += strlen ("--lclauses-delfactor=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lclauses_delfactor = strtod (configure_str, 0);
        }
      else
        result = "Expecting real number after '--lclauses-delfactor='";
    }
  else
    if (!strncmp
        (configure_str, "--lcubes-delfactor=",
         strlen ("--lcubes-delfactor=")))
    {
      configure_str += strlen ("--lcubes-delfactor=");
      if (isnumstr (configure_str))
        {
          qdpll->options.lcubes_delfactor = strtod (configure_str, 0);
        }
      else
        result = "Expecting real number after '--lcubes-delfactor='";
    }
  else if (!strncmp (configure_str, "--dec-heur=", strlen ("--dec-heur=")))
    {
      configure_str += strlen ("--dec-heur=");
      if (!strncmp (configure_str, "simple", strlen ("simple")))
        qdpll->options.dh = QDPLL_DH_SIMPLE;
      else if (!strncmp (configure_str, "sdcl", strlen ("sdcl")))
        qdpll->options.dh = QDPLL_DH_SDCL;
      else if (!strncmp (configure_str, "qtype", strlen ("qtype")))
        qdpll->options.dh = QDPLL_DH_QTYPE;
      else if (!strncmp (configure_str, "rand", strlen ("rand")))
        qdpll->options.dh = QDPLL_DH_RANDOM;
      else if (!strncmp (configure_str, "falsify", strlen ("falsify")))
        qdpll->options.dh = QDPLL_DH_FALSIFY;
      else if (!strncmp (configure_str, "satisfy", strlen ("satisfy")))
        qdpll->options.dh = QDPLL_DH_SATISFY;
      else
        result =
          "Expecting one of 'simple, sdcl, qtype, rand' after '--dec-heur='";
    }
  else if (!strncmp (configure_str, "--max-space=", strlen ("--max-space=")))
    {
      configure_str += strlen ("--max-space=");
      if (isnumstr (configure_str))
        {
          qdpll->options.max_space = atoi (configure_str);
          /* Space limit takes effect immediately when set. */
          qdpll_set_mem_limit (qdpll->mm, qdpll->options.max_space);
        }
      else
        result = "Expecting number after '--max-space='";
    }
  else
    if (!strncmp
        (configure_str, "--soft-max-space=", strlen ("--soft-max-space=")))
    {
      configure_str += strlen ("--soft-max-space=");
      if (isnumstr (configure_str))
        {
          qdpll->options.soft_max_space = atoi (configure_str);
        }
      else
        result = "Expecting number after '--soft-max-space='";
    }
  else if (!strncmp (configure_str, "--max-dec=", strlen ("--max-dec=")))
    {
      configure_str += strlen ("--max-dec=");
      if (isnumstr (configure_str))
        {
          qdpll->options.max_dec = atoi (configure_str);
          if (qdpll->options.max_dec == 0)
            {
              if (qdpll->options.max_btracks == 0 && qdpll->options.max_secs == 0)
                qdpll->options.limit_set = 0;
            }
          else
            qdpll->options.limit_set = 1;
        }
      else
        result = "Expecting number after '--max-dec='";
    }
  else if (!strncmp (configure_str, "--max-btracks=", strlen ("--max-btracks=")))
    {
      configure_str += strlen ("--max-btracks=");
      if (isnumstr (configure_str))
        {
          qdpll->options.max_btracks = atoi (configure_str);
          if (qdpll->options.max_btracks == 0)
            {
              if (qdpll->options.max_dec == 0 && qdpll->options.max_secs == 0)
                qdpll->options.limit_set = 0;
            }
          else
            qdpll->options.limit_set = 1;
        }
      else
        result = "Expecting number after '--max-btracks='";
    }
  else if (!strncmp (configure_str, "--max-secs=", strlen ("--max-secs=")))
    {
      configure_str += strlen ("--max-secs=");
      if (isnumstr (configure_str))
        {
          qdpll->options.max_secs = atoi (configure_str);
          if (qdpll->options.max_secs == 0)
            {
              if (qdpll->options.max_dec == 0 && qdpll->options.max_btracks == 0)
                qdpll->options.limit_set = 0;
            }
          else
            qdpll->options.limit_set = 1;
        }
      else
        result = "Expecting number after '--max-secs='";
    }
  else if (!strncmp (configure_str, "--seed=", strlen ("--seed=")))
    {
      configure_str += strlen ("--seed=");
      if (isnumstr (configure_str))
        {
          qdpll->options.seed = atoi (configure_str);
          srand (qdpll->options.seed);
        }
      else
        result = "Expecting number after '--seed='";
    }
  else if (!strncmp (configure_str, "--dep-man=", strlen ("--dep-man=")))
    {
      assert (qdpll->dm);
      assert ((qdpll->options.depman_simple && !qdpll->options.depman_qdag)
              || (!qdpll->options.depman_simple && qdpll->options.depman_qdag)
              || (!qdpll->options.depman_simple
                  && !qdpll->options.depman_qdag));

      QDPLLDepManType current;
      if (qdpll->options.depman_qdag)
        current = QDPLL_DEPMAN_TYPE_QDAG;
      else if (qdpll->options.depman_simple)
        current = QDPLL_DEPMAN_TYPE_SIMPLE;
      else
        {
          QDPLL_ABORT_QDPLL (1, "unexpected value for DM!");
        }

      configure_str += strlen ("--dep-man=");

      QDPLLDepManType new;
      if (!strcmp (configure_str, "qdag"))
        new = QDPLL_DEPMAN_TYPE_QDAG;
      else if (!strcmp (configure_str, "simple"))
        new = QDPLL_DEPMAN_TYPE_SIMPLE;
      else
        {
          result = "expecting 'simple' or 'qdag' after '--dep-man='";
          return result;
        }

      if (current != new)
        {
          /* Delete old, create new DepMan. */
          qdpll->options.depman_qdag = qdpll->options.depman_simple = 0;
          qdpll_qdag_dep_man_delete ((QDPLLDepManQDAG *) qdpll->dm);
          qdpll->dm =
            (QDPLLDepManGeneric *)
            qdpll_qdag_dep_man_create (qdpll->mm, &(qdpll->pcnf), new,
                                       qdpll->options.
                                       depman_qdag_print_deps_by_search,
                                       qdpll);
          if (new == QDPLL_DEPMAN_TYPE_QDAG)
            {
              assert (!qdpll->options.depman_qdag);
              qdpll->options.depman_qdag = 1;
            }
          else if (new == QDPLL_DEPMAN_TYPE_SIMPLE)
            {
              assert (!qdpll->options.depman_simple);
              qdpll->options.depman_simple = 1;
            }
        }
    }
  else if (!strcmp (configure_str, "--qdag-print-deps-by-search"))
    {
      if (qdpll->options.depman_qdag)
        {
          assert (!qdpll->options.depman_simple);
          result =
            "must use '--qdag-print-deps-by-search' before configuring QDAG dependency manager";
        }
      else
        qdpll->options.depman_qdag_print_deps_by_search = 1;
    }

  else if (!strcmp (configure_str, "-v"))
    {
      qdpll->options.verbosity++;
    }
  else
    {
      result = "unknown option";
    }

  return result;
}


/* Decrease the current frame index by one and cleanup all clauses associated
   to old, popped off frame. Learned cubes still are valid after clauses have
   been cleaned up. Returns either the old frame index which was popped off or
   zero if there is no frame to be popped off. */
unsigned int
qdpll_pop (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable push/pop API!");
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->state.clause_group_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  qdpll->state.push_pop_api_called = 1;

  if (qdpll->state.cnt_created_clause_groups == 0)
    return 0;

  unsigned int popped_off_index = qdpll->state.cnt_created_clause_groups;

  assert (qdpll->state.cnt_created_clause_groups == 
          QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));
  delete_clause_group_aux (qdpll, popped_off_index);
  QDPLL_POP_STACK(qdpll->state.cur_used_internal_vars);
  assert (qdpll->state.cnt_created_clause_groups == 
          QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));

  /* Declare next frame open. */
  assert (qdpll->state.cur_open_group_id == qdpll->state.cnt_created_clause_groups + 1);
  qdpll->state.cur_open_group_id = qdpll->state.cnt_created_clause_groups; 

  return popped_off_index;
}


/* Enforce the deletion of variables which have no occurrences
   left. E.g. after 'qdpll_pop', a variable might not have any clauses
   left and hence can be cleaned up. This can be useful if the user
   wants to re-use the indices of these variables by adding them to a
   new scope. A 'qdpll_pop' usually does not delete variables and
   clauses physically each time, but only logically. Physical deletion
   is done heuristically. This means that the logically deleted
   variables are still present and cannot be declared again in a new
   scope, for example. This function 'qdpll_gc' makes sure that
   physical deletion of all logically deleted clauses and variables is
   carried out. */
void qdpll_gc (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  qdpll_gc_aux (qdpll, 1);
}


/* Increase the current frame index by one. If necessary, then increase the
   size of the table storing internal variable IDs. Every clause added to the
   current frame gets a positive literal of a fresh internal variable,
   attaching that clause to the current frame. Returns the new frame index
   resulting from the pop operation. */
unsigned int
qdpll_push (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable push/pop API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->state.clause_group_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  qdpll->state.push_pop_api_called = 1;

  unsigned int frame_index = new_clause_group_aux (qdpll);
  assert (frame_index == QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));
  assert (frame_index == qdpll->state.cnt_created_clause_groups);

  /* Declare new frame open. */
  qdpll->state.cur_open_group_id = frame_index; 

  return frame_index;
}


/* ------------ START: API functions for clause groups ------------ */

/* Creates a new clause group and returns its ID. The returned ID is a handle
   of the created clause group and should be passed to API functions to
   manipulate clause groups. Initially, the newly created clause group is
   empty (i.e. it does not contain any clauses) and it is closed. To add
   clauses to a group, the group must be opened by 'open_clause_group'. Only
   one clause group can be open at a time. Clauses can be added to the
   currently open group as usual by calling 'qdpll_add'. To add clauses to a
   different group, the currently open group must be closed again by
   'close_clause_group' and the other group must be opened. */
ClauseGroupID 
qdpll_new_clause_group (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll), 
                     "Must close currently open clause group before creating a new one!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "Must close currently open scope before creating new clause group!");

  /* Allocate a new clause group with ID 'group_id'. New groups are closed and
     have to be opened by calling 'qdpll_open_clause_group'. */
  unsigned int group_id = new_clause_group_aux (qdpll);
  assert (QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars) > 0);
  assert (group_id == QDPLL_COUNT_STACK(qdpll->state.cur_used_internal_vars));
  assert (qdpll->state.cnt_created_clause_groups <= group_id);

  return group_id;
}

/* Delete the clause group with ID 'clause_group'. The ID of the deleted group
   becomes invalid and must not be passed to the API functions anymore. All
   clauses in the deleted group are deleted from the formula. */
void 
qdpll_delete_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (!qdpll_exists_clause_group(qdpll, clause_group), "Invalid clause group ID!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll) == clause_group, 
                     "Clause group to be deleted must not be open!");
  QDPLL_ABORT_QDPLL (clause_group_to_var_ptr (qdpll, clause_group)->is_cur_inactive_group_selector,
                     "Clause group to be deleted must not be deactivated!");

  delete_clause_group_aux (qdpll, clause_group);
}

/* Open the clause group with ID 'clause_group'. That group must not be open
   already. Only one group can be open at a time. Clauses can be added to the
   currently open group as usual by calling 'qdpll_add'. An open group will
   stay open across calls of e.g. 'qdpll_sat'. However, to add clauses to a
   another group, the currently open group must be closed again by
   'close_clause_group' and the other group must be opened. */
void 
qdpll_open_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (!qdpll_exists_clause_group(qdpll, clause_group), "Invalid clause group ID!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll), 
                     "There is already an open clause group!");
  QDPLL_ABORT_QDPLL (clause_group_to_var_ptr (qdpll, clause_group)->is_cur_inactive_group_selector,
                     "Clause group to be opened must not be deactivated!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "Must close currently open scope before opening a clause group!");

  qdpll->state.cur_open_group_id = clause_group;
}

/* Returns the ID of the currently open clause group, or NULL if no group is
   currently open. If there is currently no open group, then all clauses added
   via 'qdpll_add' will be permanently added to the formula and cannot be
   removed. */
ClauseGroupID 
qdpll_get_open_clause_group (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.cur_open_group_id && 
                     !qdpll_exists_clause_group 
                     (qdpll, qdpll->state.cur_open_group_id), 
                     "Internal error: invalid clause group ID.");
  QDPLL_ABORT_QDPLL (qdpll->state.cur_open_group_id && 
                     clause_group_to_var_ptr 
                     (qdpll, qdpll->state.cur_open_group_id)->is_cur_inactive_group_selector,
                     "Internal error: current open group is deactivated!");

  return get_open_clause_group_aux (qdpll);
}

/* Returns non-zero if and only if (1) a clause group with ID 'clause_group'
   has been created before and (2) the ID 'clause_group' was returned by
   'qdpll_new_clause_group' and (3) that clause group was not deleted by 
   calling 'qdpll_delete_clause_group'. */
int 
qdpll_exists_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");

  return exists_clause_group_aux (qdpll, clause_group);
}

/* Close the clause group with ID 'clause_group'. That group must have been
   opened by a previous call of 'open_clause_group'. */
void 
qdpll_close_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (!qdpll_exists_clause_group(qdpll, clause_group), "Invalid clause group ID!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll) != clause_group, 
                     "Clause group to be closed is currently not open!");
  QDPLL_ABORT_QDPLL (clause_group_to_var_ptr (qdpll, clause_group)->is_cur_inactive_group_selector,
                     "Clause group to be closed must not be deactivated!");

  qdpll->state.cur_open_group_id = 0;
}

/* Returns a zero-terminated array of clause group IDs representing those
   clause groups which contain clauses used by the solver to determine
   UNSATISFIABILITY by the most recent call of 'qdpll_sat'. That is, this
   function returns a subset of those clause groups which participiate in the
   resolution refutation of the current formula. This function can be called
   only if the most recent call of 'qdpll_sat' returned QDPLL_RESULT_UNSAT.

   NOTE: the caller is responsible to release the memory of the array returned
   by this function. */
ClauseGroupID * 
qdpll_get_relevant_clause_groups (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->result == QDPLL_RESULT_UNKNOWN, 
                     "Formula must be solved before calling this function!");
  QDPLL_ABORT_QDPLL (qdpll->result != QDPLL_RESULT_UNSAT, 
                     "Formula must be unsatisfiable when calling this function!");
  QDPLL_ABORT_QDPLL(!qdpll->assumption_lits_constraint, 
                    "Unexpected error: no assumption subset computed!");
  QDPLL_ABORT_QDPLL(!(qdpll->assumption_lits_constraint && qdpll->state.assumptions_given), 
                    "Unexpected error: cannot retrieve relevant assumptions.");
  QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint->is_cube, 
                    "Unexpected error: assumption-lits constraint is a cube.");

  ClauseGroupIDStack clause_group_ids;
  QDPLL_INIT_STACK(clause_group_ids);

  LitID *p, *e;
  for (p = qdpll->assumption_lits_constraint->lits, 
         e = p + qdpll->assumption_lits_constraint->num_lits; 
       p < e; p++)
    {
      LitID a_lit = *p;
      Var *a_var = LIT2VARPTR(qdpll->pcnf.vars, a_lit);
      if (a_var->is_internal)
        {
          /* Watch out for literals of clause group selector variables. Here,
             we will only find variables assigned to FALSE since the formula is
             unsatisfiable and 'qdpll->assumption_lits_constraint' is a clause
             containing literals of the relevant internal assumptions. */
          assert (a_var->is_cur_used_internal_var);
          assert (!a_var->is_cur_inactive_group_selector);
          assert (a_var->assignment == QDPLL_ASSIGNMENT_FALSE);
          ClauseGroupID group_id = a_var->clause_group_id;
          assert (qdpll_exists_clause_group (qdpll, group_id));
          assert (!clause_group_to_var_ptr 
                  (qdpll, group_id)->is_cur_inactive_group_selector);
          assert (qdpll->state.cur_used_internal_vars.start[group_id - 1] == a_var->id);
          QDPLL_PUSH_STACK(qdpll->mm, clause_group_ids, group_id);
        }
    }

  unsigned int size = 
    (QDPLL_COUNT_STACK(clause_group_ids) + 1) * sizeof (ClauseGroupID);
  /* Do not use internal memory manager here because the user has to free the
     memory. */
  ClauseGroupID *relevant_clause_groups = malloc (size);
  memset (relevant_clause_groups, 0, size);

  /* Copy collected clause group ID to newly allocated array. */
  ClauseGroupID *gp, *ge, *dest = relevant_clause_groups;
  for (gp = clause_group_ids.start, ge = clause_group_ids.top; 
       gp < ge; gp++, dest++)
    *dest = *gp;
  assert (dest == 
          relevant_clause_groups + QDPLL_COUNT_STACK(clause_group_ids));
  assert (!*dest);

  QDPLL_DELETE_STACK(qdpll->mm, clause_group_ids);

  return relevant_clause_groups;
}

/* Activates all clauses in the group 'clause_group', which has been
   deactivated before by 'qdpll_deactivate_clause_group'. Clause groups are
   activated at the time they are created and can be deactivated by calling
   'qdpll_deactivate_clause_group'. */
void 
qdpll_activate_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (!qdpll_exists_clause_group(qdpll, clause_group), "Invalid clause group ID!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll) == clause_group, 
                     "Internal error: deactivated clause group to be activated must not be open!");

  Var *var = clause_group_to_var_ptr (qdpll, clause_group);
  assert(var->is_cur_used_internal_var);
  QDPLL_ABORT_QDPLL (!var->is_cur_inactive_group_selector,
                     "Clause group to be activated is already activated!");
  /* Set flag to indicate that the group with selector variable 'var' is
     activated. */
  var->is_cur_inactive_group_selector = 0;
}

/* Deactivates all clauses in the group 'clause_group'. The ID of a
   deactivated group cannot be passed to any API functions except
   'qdpll_activate_clause_group' and 'qdpll_exists_clause_group'. Clause
   groups are activated at the time they are created. When calling
   'qdpll_sat', clauses in deactivated groups are ignored. Thus deactivating a
   clause group amounts to temporarily deleting these groups from the
   formula. However, unlike 'qdpll_delete_clause_group' which permanently
   deletes the clauses in a group, deactivated groups can be activated again
   by calling 'qdpll_activate_clause_group'. This adds the formerly
   deactivated clauses back to the formula. */
void 
qdpll_deactivate_clause_group (QDPLL *qdpll, ClauseGroupID clause_group)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable clause groups API!");
  qdpll->state.clause_group_api_called = 1;
  QDPLL_ABORT_QDPLL (qdpll->state.push_pop_api_called, 
                     "Must not mix calls of push/pop API and clause groups API!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (!qdpll_exists_clause_group(qdpll, clause_group), "Invalid clause group ID!");
  QDPLL_ABORT_QDPLL (qdpll_get_open_clause_group (qdpll) == clause_group, 
                     "Clause group to be deactivated must not be open!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "Must close currently open scope before deactivating a clause group!");

  Var *var = clause_group_to_var_ptr (qdpll, clause_group);
  assert(var->is_cur_used_internal_var);
  QDPLL_ABORT_QDPLL (var->is_cur_inactive_group_selector,
                     "Clause group to be deactivated is already deactivated!");
  /* Set flag to indicate that the group with selector variable 'var' is
     deactivated. */
  var->is_cur_inactive_group_selector = 1;
}

/* ------------ END: API functions for clause groups ------------ */


/* Make sure that at least a user-given variable with ID 'num' is
   available. Enlarge variable table if necessary, rename internal variable
   IDs. */
void
qdpll_adjust_vars (QDPLL * qdpll, VarID num)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  const VarID cur_size_vars = qdpll->pcnf.size_vars;
  const VarID cur_size_user_vars = qdpll->pcnf.size_user_vars;
  QDPLL_ABORT_QDPLL (cur_size_user_vars > cur_size_vars, 
                     "Size of user vars must be smaller than or equal to size of vars!");

  /* Index 0 is never used in variable table, hence increase 'num' */
  unsigned int new_size_user_vars = num + 1;
  if (cur_size_user_vars < new_size_user_vars)
    {
      QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                         "Unexpected decision level != 0; solver must be in reset state!");
      QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                         "Unexpected assignments of variables; solver must be in reset state!");

      /* Make sure that old and new portion of internal vars do not overlap;
         this simplifies the way of updating old IDs of internal variables by
         adding a fixed offset. 
         POSSIBLE OPTIMIZATION: we likely have unused variable indices using this policy. */
      if (new_size_user_vars < cur_size_vars)
        new_size_user_vars = cur_size_vars;

      const unsigned int cur_size_internal_vars = cur_size_vars - cur_size_user_vars;
      assert (cur_size_internal_vars <= cur_size_vars);
      const unsigned int new_size_vars = new_size_user_vars + cur_size_internal_vars; 
      assert (new_size_user_vars <= new_size_vars);
      qdpll->pcnf.vars = (Var *) qdpll_realloc (qdpll->mm, qdpll->pcnf.vars,
                                                cur_size_vars * sizeof (Var),
                                                new_size_vars * sizeof (Var));
      qdpll->pcnf.size_vars = new_size_vars;
      qdpll->pcnf.size_user_vars = new_size_user_vars;
      qdpll->state.next_free_internal_var_id = qdpll->pcnf.size_user_vars;

      /* Rename internal IDs by adding additional offset. Rename only if
         current frame index is greater than zero: this indicates that 'push' was
         called before and that there are in fact USED internal variables. */
      if (qdpll->state.cnt_created_clause_groups > 0 || 
          QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) > 0)
        {
          assert (cur_size_internal_vars >= qdpll->state.cnt_created_clause_groups);

          if (qdpll->options.verbosity >= 2)
            fprintf (stderr, "Adjust user vars: moving and renaming internal variables, new internal size %d.\n", 
                     qdpll->pcnf.size_vars - qdpll->pcnf.size_user_vars);

          move_internal_ids (qdpll, cur_size_user_vars, new_size_user_vars, new_size_user_vars - cur_size_user_vars);

          rename_internal_variable_ids (qdpll, new_size_user_vars - cur_size_user_vars);

          /* Reset dependencies here to clear any old-internal candidates
             maintained in dependency manager. */
          qdpll_reset_deps (qdpll);
        }
      assert_internal_vars_integrity (qdpll);
    }

  assert (qdpll->pcnf.size_user_vars <= qdpll->pcnf.size_vars);
}


/* Add a new variable with ID 'id' to the scope with nesting level
   'nesting'. The variable 'id' must not have been added before by either this
   function or 'qdpll_add'. The scope must exist, i.e. it must have been added
   by either 'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'. The value of
   the parameter 'nesting' of this function should be a value returned by a
   previous call of 'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'. In any
   case, it must be smaller than or equal to the return value of
   'qdpll_get_max_scope_nesting'. */
void 
qdpll_add_var_to_scope (QDPLL *qdpll, VarID id, Nesting nesting)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (nesting == 0, "Parameter 'nesting' must be greater than zero!");
  QDPLL_ABORT_QDPLL (qdpll_get_max_scope_nesting (qdpll) == 0, 
                     "Empty scope list; must add scopes first by 'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "there is an open scope (must be closed with 'qdpll_add(qdpll, 0)')!");
  QDPLL_ABORT_QDPLL (nesting > qdpll_get_max_scope_nesting (qdpll), 
                     "'nesting' must be smaller than or equal to the return value of 'qdpll_get_max_scope_nesting'");
  QDPLL_ABORT_QDPLL (QDPLL_COUNT_STACK(qdpll->add_stack) != 0, 
                     "Started adding a variable to a scope while adding a clause!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  /* The scope used in the previous call of this function is cached in
     'qdpll->state.scope_opened_ptr'. If possible, then re-use that cached
     value. This way, we avoid linear-time search for the scope where 'id'
     should be added to. */
  if (!qdpll->state.scope_opened_ptr || 
      qdpll->state.scope_opened_ptr->nesting != nesting)
    qdpll->state.scope_opened_ptr = find_user_scope_at_nesting_level (qdpll, nesting);

  assert (qdpll->state.scope_opened_ptr && 
          !qdpll->state.scope_opened_ptr->is_internal &&  
          qdpll->state.scope_opened_ptr->nesting == nesting);

  const char *err_msg = add_id_to_scope (qdpll, id, qdpll->state.scope_opened_ptr, 1);
  /* Abort if variables are added multiple times. */
  QDPLL_ABORT_QDPLL (err_msg, err_msg);

  /* Schedule the import of user prefix next time 'import_user_scopes' is called. */
  qdpll->state.no_scheduled_import_user_scopes = 0;

  assert (!qdpll->state.scope_opened);
}


/* Returns the nesting level of the current rightmost scope or zero if there
   are no scopes. */
Nesting 
qdpll_get_max_scope_nesting (QDPLL *qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  assert (qdpll->pcnf.user_scopes.first || !qdpll->pcnf.user_scopes.last);
  assert (!qdpll->pcnf.user_scopes.first || qdpll->pcnf.user_scopes.last);
  return qdpll->pcnf.user_scopes.last ? qdpll->pcnf.user_scopes.last->nesting : 0;
}


Nesting
qdpll_new_scope (QDPLL * qdpll, QDPLLQuantifierType qtype)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL ((qtype != QDPLL_QTYPE_EXISTS &&
                      qtype != QDPLL_QTYPE_FORALL), "invalid 'qtype'!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "there is already a new, open scope (must be closed with 'qdpll_add(qdpll, 0)')!");
  QDPLL_ABORT_QDPLL (QDPLL_COUNT_STACK(qdpll->add_stack) != 0, 
                     "Started adding a scope while adding a clause!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  qdpll->state.scope_opened = 1;
  /* Allocate a new rightmost scope. */
  Scope *scope = (Scope *) qdpll_malloc (qdpll->mm, sizeof (Scope));
  scope->nesting = qdpll->pcnf.user_scopes.last ? 
    qdpll->pcnf.user_scopes.last->nesting + 1 : QDPLL_DEFAULT_SCOPE_NESTING + 1;
  assert (scope->nesting > 0);
  scope->type = qtype;
  LINK_LAST (qdpll->pcnf.user_scopes, scope, link);
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->pcnf.user_scope_ptrs, scope);
  assert (QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs) == 
          qdpll_get_max_scope_nesting (qdpll));
  qdpll->state.scope_opened_ptr = scope;
  assert (!qdpll->state.scope_opened_ptr->is_internal);

  return qdpll->state.scope_opened_ptr->nesting;
}


/* Open a new scope at nesting level '1 <= nesting <=
   qdpll_get_max_scope_nesting () + 1' with quantifier type 'qtype'. If
   'nesting == qdpll_get_max_scope_nesting () + 1' then the new scope is
   appended to the list of present scopes, which has the same effect as
   calling 'qdpll_new_scope'. Otherwise, the new scope is inserted at level
   'nesting' and the present scopes with nesting levels equal to and greater
   than 'nesting' (i.e. before inserting the new scope) are shifted right.
   Variables can be added to the scope opened by the most recent call of this
   function by 'qdpll_add' (similar to 'qdpll_new_scope'). The opened scope
   must be closed by adding '0' via 'qdpll_add'. Adjacent scopes of the same
   quantifier type can be added (but internally they will be merged into a single
   scope). Returns the nesting of the added scope, which should be used as a
   handle of this scope, and which can safely be passed to
   'qdpll_add_var_to_scope'.
   NOTE: the run time of this function is linear in the length of quantifier prefix. */
Nesting
qdpll_new_scope_at_nesting (QDPLL * qdpll, QDPLLQuantifierType qtype, Nesting nesting)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (nesting == 0, "Parameter 'nesting' must be greater than zero!");
  QDPLL_ABORT_QDPLL (nesting > qdpll_get_max_scope_nesting (qdpll) + 1, 
                     "Parameter 'nesting' must be smaller than or equal to 'qdpll_get_max_scope_nesting () + 1'!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "there is already a new, open scope (must be closed with 'qdpll_add(qdpll, 0)')!");
  QDPLL_ABORT_QDPLL (QDPLL_COUNT_STACK(qdpll->add_stack) != 0, 
                     "Started adding a scope while adding a clause!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  /* Check when to append new scope to list of existing scopes. */
  if (nesting > qdpll_get_max_scope_nesting (qdpll))
    return qdpll_new_scope (qdpll, qtype);
  else
    {
      assert (nesting > QDPLL_DEFAULT_SCOPE_NESTING);
      /* The list of user scopes is not empty. */
      assert (qdpll_get_max_scope_nesting (qdpll) > 0);
      assert (qdpll->pcnf.user_scopes.first);
      assert (qdpll->pcnf.user_scopes.last);
      qdpll->state.scope_opened = 1;
      Scope *s = find_user_scope_at_nesting_level (qdpll, nesting);
      assert (s && s->nesting == nesting);
      assert (s->nesting <= qdpll_get_max_scope_nesting (qdpll));
      assert (!s->is_internal);

      /* Allocate a new user scope to be inserted. */
      Scope *scope = (Scope *) qdpll_malloc (qdpll->mm, sizeof (Scope));
      scope->type = qtype;
      assert (!scope->is_internal);
      qdpll->state.scope_opened_ptr = scope;

      if (s == qdpll->pcnf.user_scopes.first)
        LINK_FIRST (qdpll->pcnf.user_scopes, scope, link);
      else
        {
          /* Insert new user scope into scope list. */
          assert (s->link.prev);
          assert (s->link.next || s == qdpll->pcnf.user_scopes.last);
          assert (!scope->link.next);
          assert (!scope->link.prev);
          scope->link.next = s;
          scope->link.prev = s->link.prev;
          s->link.prev->link.next = scope;
          s->link.prev = scope; 
          qdpll->pcnf.user_scopes.cnt++;
        }

      scope->nesting = nesting;
      assert (scope->nesting > 0);

      /* Update the nesting levels of all scopes and collect pointers to scopes. */
      update_scope_nestings_and_ptrs_on_stack (qdpll, 1);
      assert (QDPLL_COUNT_STACK(qdpll->pcnf.user_scope_ptrs) == 
              qdpll->pcnf.user_scopes.cnt);

      assert (qdpll->state.scope_opened_ptr == scope);
      return qdpll->state.scope_opened_ptr->nesting;
    }
}

/* This function is deprecated. */
int 
qdpll_has_var_active_occs (QDPLL *qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL(1,"function deprecated");
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL(!id || id > qdpll->pcnf.max_declared_user_var_id, 
                    "Invalid variable ID!");
  Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
  QDPLL_ABORT_QDPLL(!var->id, 
                    "Variable is not declared!");

  return has_variable_active_occs_in_clauses (qdpll, var, &(var->neg_occ_clauses), 0) ||
    has_variable_active_occs_in_clauses (qdpll, var, &(var->pos_occ_clauses), 0);
}

/* NOTE: semantics of 'qdpll_add' must support DIMACS as well as QDIMACS format.
   For DIMACS, all variables must be added to the default, existential scope, 
   which could be done e.g. before solving starts.
   For QDIMACS, scopes are closed - as clauses are in (Q)DIMACS - by adding '0'. */
void
qdpll_add (QDPLL * qdpll, LitID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  add_aux (qdpll, id);
}


QDPLLResult
qdpll_sat (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL(qdpll->options.depman_qdag && qdpll->options.trace,
                    "Trace mode must be combined with '--dep-man=simple'!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "there is an open scope (must be closed with 'qdpll_add(qdpll, 0)')!");
  QDPLL_ABORT_QDPLL (QDPLL_COUNT_STACK(qdpll->add_stack) != 0, 
                     "most recently added clause has not been closed!");
  /* Value of 'qdpll->state.num_sat_calls' is used to trigger cube checking later in 'solve'. */
  QDPLL_ABORT_QDPLL (qdpll->state.num_sat_calls == UINT_MAX, 
                     "Number of calls of 'qdpll_sat()' has reached UINT_MAX.");
  qdpll->state.num_sat_calls++;

  qdpll->state.solving_start_time = time_stamp();

  QDPLL_ABORT_QDPLL (qdpll->state.num_sat_calls > 1 && qdpll->state.pending_cubes_check && 
                     !qdpll->options.incremental_use, 
                     "Must configure by '--incremental-use' to enable incremental use!");

  QDPLL_ABORT_QDPLL(((qdpll->state.num_sat_calls > 1 && qdpll->state.pending_cubes_check && 
                     qdpll->options.depman_qdag)), 
                    "Must configure by '--dep-man=simple' in incremental use!");

  QDPLL_ABORT_QDPLL (qdpll->options.incremental_use && qdpll->options.depman_qdag, 
                    "Must configure by '--dep-man=simple' in incremental use!");

  QDPLL_ABORT_QDPLL (qdpll->qdo_assignment_table || qdpll->qdo_table_bytes, 
                     "Unexpected computed assignment for QDIMACS output. "\
                     "Must call 'qdpll_reset()' before calling 'qdpll_sat ()'.");
  QDPLL_ABORT_QDPLL ((!qdpll->state.assumptions_given && count_assigned_vars(qdpll) != 0) || 
                     qdpll->assigned_vars != qdpll->bcp_ptr || qdpll->result_constraint || 
                     qdpll->state.decision_level != 0 || qdpll->result != QDPLL_RESULT_UNKNOWN, 
                     "Unexpected assignments of variables; solver must be in reset state!");

  QDPLL_ABORT_QDPLL (!qdpll->options.no_qbce_dynamic && 
                     (qdpll->options.qbce_preprocessing || qdpll->options.qbce_inprocessing), 
                     "must enable at most one of dynamic, inprocessing, or preprocessing QBCE!");
  QDPLL_ABORT_QDPLL (qdpll->options.qbce_preprocessing && 
                     (!qdpll->options.no_qbce_dynamic || qdpll->options.qbce_inprocessing), 
                     "must enable at most one of dynamic, inprocessing, or preprocessing QBCE!");
  QDPLL_ABORT_QDPLL (qdpll->options.qbce_inprocessing && 
                     (!qdpll->options.no_qbce_dynamic || qdpll->options.qbce_preprocessing), 
                     "must enable at most one of dynamic, inprocessing, or preprocessing QBCE!");

  QDPLL_ABORT_QDPLL (qdpll->options.incremental_use && 
                     !qdpll->options.no_empty_formula_watching, 
                     "temporarily disabled: empty-formula-watching in incremental mode");

  QDPLL_ABORT_QDPLL (qdpll->options.incremental_use && !qdpll->options.depman_simple, 
                     "must use '--dep-man=simple' with incremental mode!");

  if (qdpll->options.trace && 
      (!qdpll->options.no_qbce_dynamic || 
       qdpll->options.qbce_preprocessing || 
       qdpll->options.qbce_inprocessing || 
       !qdpll->options.no_trivial_falsity || 
       !qdpll->options.no_trivial_truth || 
       !qdpll->options.no_dynamic_nenofex))
    fprintf (stderr, "WARNING: tracing is not yet fully compatible with generalized axioms.\n");

  /* In incremental mode: when using QBCE then stored cover sets may not cover
     clauses which were blocked at the time when the cover sets are
     produced. Hence never collect cover sets. Further set QBCE limits to
     zero, i.e. disabling the limits. */
  if (qdpll->options.incremental_use && !qdpll->options.qbce_preprocessing && 
      !qdpll->options.qbce_inprocessing && qdpll->options.no_qbce_dynamic)
    qdpll->state.collect_full_cover_sets = 1;
  else if (qdpll->options.incremental_use)
    {
      qdpll->options.qbcp_qbce_max_clause_size = 0;
      qdpll->options.qbcp_qbce_find_witness_max_occs = 0;
    }

  QDPLL_ABORT_QDPLL (qdpll->options.incremental_use && 
                     (qdpll->options.qbce_preprocessing || 
                      qdpll->options.qbce_inprocessing || 
                      !qdpll->options.no_qbce_dynamic) && 
                     (qdpll->options.qbcp_qbce_max_clause_size || 
                      qdpll->options.qbcp_qbce_find_witness_max_occs), 
                     "QBCE limits temporarily disabled in incremental mode, must set them to 0");

  if (qdpll->options.verbosity >= 3)
    {
      fprintf (stderr, "Set state 'collect_full_cover_sets': %u\n", 
	       qdpll->state.collect_full_cover_sets);
      fprintf (stderr, "Set state 'qbcp_qbce_max_clause_size': %u\n", 
	       qdpll->options.qbcp_qbce_max_clause_size);
      fprintf (stderr, "Set state 'qbcp_qbce_find_witness_max_occs': %u\n", 
	       qdpll->options.qbcp_qbce_find_witness_max_occs);
    }

  QDPLL_ABORT_QDPLL (!qdpll->options.no_dynamic_nenofex && qdpll->options.incremental_use, 
                     "temporarily disabled: dynamic Nenofex and incremental use");

  QDPLL_ABORT_QDPLL((!qdpll->options.no_lazy_qpup && !qdpll->options.traditional_qcdcl) && 
                    qdpll->options.trace, 
                    "Must combine either '--no-lazy-qpup' or '--traditional-qcdcl' with tracing");

#if COMPUTE_TIMES
  qdpll->time_stats.sat_time_start = time_stamp ();
#endif

  /* Reset any previous result. */
  qdpll->result = QDPLL_RESULT_UNKNOWN;

  assert ((qdpll->options.depman_simple && !qdpll->options.depman_qdag) ||
          (!qdpll->options.depman_simple && qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && !qdpll->options.depman_qdag));

  QDPLLResult r = QDPLL_RESULT_UNKNOWN;

  /* Decide formula. */
  set_up_formula (qdpll);
#ifndef NDEBUG
#if QDPLL_ASSERT_FULL_FORMULA_INTEGRITY
  assert_full_formula_integrity (qdpll);
#endif
#endif

  r = solve (qdpll);
  qdpll->result = r;
#if COMPUTE_TIMES
  qdpll->time_stats.total_sat_time +=
    (time_stamp () - qdpll->time_stats.sat_time_start);
#endif
  return r;
}


/* Get assignment of variable.  */
QDPLLAssignment
qdpll_get_value (QDPLL * qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!qdpll_is_var_declared (qdpll, id), 
                     "Variable with given ID is not declared!");

  /* In general, use of Nenofex must be disabled in order to extract partial
     certificates. However, if the formula is satisfiable (unsatisfiable),
     then it should be sufficient to ignore satisfiable (unsatisfiable)
     branches found by Nenofex by arguments '--dyn-nenofex-ignore-sat' and
     '--dyn-nenofex-ignore-unsat', respectively. */
  QDPLL_ABORT_QDPLL (!qdpll->options.no_dynamic_nenofex, 
                     "Must configure solver with '--no-dynamic-nenofex' to extract values!");

  /* Fix: we do NOT call 'import_user_scopes' here because this will copy
     scopes and hence destroy the QDAG. see 'qdpll_print_qdimacs_output' for
     comment. */
  const QDPLLResult result = qdpll->result;
  assert (id);
  assert (id < qdpll->pcnf.size_vars);
  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);
  QDPLL_ABORT_QDPLL (var->is_internal, "Unexpected internal variable ID.");

  if (!qdpll->qdo_assignment_table)
    {
      assert (qdpll->qdo_table_bytes == 0);
      Scope *outer = 0;
      assert (qdpll->pcnf.scopes.first);
      if (!qdpll->pcnf.user_scopes.first)
        {
          /* Formula is propositional; can print model only if satisfiable. */
          if (result == QDPLL_RESULT_SAT)
            outer = qdpll->pcnf.scopes.first;
        }
      else
        {
          if (result == QDPLL_RESULT_UNSAT)
            {
              /* Formula is unsatisfiable; cannot print countermodel if the
                 outermost scope is existential or if the formula contains free
                 variables, which by default are quantified existentially and
                 leftmost. */
              if (qdpll->pcnf.user_scopes.first->type == QDPLL_QTYPE_FORALL && 
                  !has_scope_free_user_var (qdpll, qdpll->pcnf.scopes.first))
                outer = qdpll->pcnf.user_scopes.first;
            }
          else
            {
              assert (result == QDPLL_RESULT_SAT);
              /* Formula is satisfiable; cannot print countermodel if the
                 outermost scope is universal AND if the formula DOES NOT contain free
                 variables. */
              if (qdpll->pcnf.user_scopes.first->type == QDPLL_QTYPE_EXISTS || 
                  has_scope_free_user_var (qdpll, qdpll->pcnf.scopes.first))
                {
                  outer = qdpll->pcnf.scopes.first;
                  if (QDPLL_COUNT_STACK(qdpll->pcnf.scopes.first->vars) == 0)
                    {
                      assert (outer->link.next);
                      assert (outer->link.next->type == outer->type);
                      outer = outer->link.next;
                    }
                }
            }
        }

        if (outer)
        {
          /* Bug fix: must check if 'result_constraint' is set (set
             only if we have top-level conflict/solution). If it is not
             set then, for satisfiable formulas, we just set every unassigned
             variable to false. */
          if (qdpll->result_constraint && qdo_has_outer_scope_unassigned_vars (qdpll, outer, qdpll->result))
            {
              qdpll->qdo_table_bytes = (qdpll_get_max_declared_var_id (qdpll) + 1) * sizeof (char);
              qdpll->qdo_assignment_table = (char *) qdpll_malloc (qdpll->mm, qdpll->qdo_table_bytes);
              qdo_fix_outer_scope_unassigned_vars(qdpll, outer, qdpll->result, qdpll->qdo_assignment_table);
            }
          if (result == QDPLL_RESULT_SAT && outer->type == QDPLL_QTYPE_EXISTS)
            {
              /* Set every unassigned variable to false. E.g. we may have
                 unassigned variables if the formula is completely solved by
                 QBCE. Do not overwrite predetermined values in assignment table. 
                 NOTE: we assign these variables as dummy "pure
                 literals" at the current decision level. This is just because
                 every assigned variable has to have a mode (unit, pure,
                 decision) and a decision level, but the actual values do not
                 matter for reconstruction. */
              if (qdo_has_outer_scope_unassigned_vars (qdpll, outer, qdpll->result))
                {
                  assert (QDPLL_COUNT_STACK (qdpll->qdo_dummy_assigned_vars) == 0);
                  VarID *p, *e;
                  for (p = outer->vars.start, e = outer->vars.top; p < e; p++)
                    {
                      Var *var = VARID2VARPTR(qdpll->pcnf.vars, *p);
                      if (!QDPLL_VAR_ASSIGNED(var) && 
                          (!qdpll->qdo_assignment_table || 
                           qdpll->qdo_assignment_table[var->id] == QDPLL_ASSIGNMENT_UNDEF))
                        {
                          if (qdpll->state.qdo_trivial_truth_success)
                            {
                              /* Get value from trivial truth solver, if any,
                                 otherwise set variable to false like in default
                                 case. */
                              assert (picosat_res (qdpll->trivial_truth_solver) == PICOSAT_SATISFIABLE);
                              var->assignment = picosat_deref (qdpll->trivial_truth_solver, var->id);
                              if (var->assignment == QDPLL_ASSIGNMENT_UNDEF)
                                var->assignment = QDPLL_ASSIGNMENT_FALSE;
                            }
                          else
                            var->assignment = QDPLL_ASSIGNMENT_FALSE;
                          var->decision_level = qdpll->state.decision_level;
                          var->mode = QDPLL_VARMODE_PURE;
                          if (qdpll->options.verbosity >= 2)
                            fprintf (stderr, "Partial model reconstruction: outer unassigned var. %d set to %d\n", 
                                     var->id, var->assignment);
                          QDPLL_PUSH_STACK (qdpll->mm, qdpll->qdo_dummy_assigned_vars, var->id);
                        }
                    }
                }
              /* Reconstruct partial model if QBCE was applied. */
              qdo_qbcp_qbce_reconstruct_cnf_model (qdpll, outer);
            }
        }
    }

  assert (var->assignment == QDPLL_ASSIGNMENT_TRUE ||
          var->assignment == QDPLL_ASSIGNMENT_FALSE ||
          var->assignment == QDPLL_ASSIGNMENT_UNDEF);

  if (var->assignment != QDPLL_ASSIGNMENT_UNDEF || !qdpll->qdo_assignment_table)
    return var->assignment;
  else 
    {
      assert (qdpll->qdo_assignment_table);
      assert (qdpll->qdo_assignment_table[var->id] == QDPLL_ASSIGNMENT_UNDEF || 
              qdpll->qdo_assignment_table[var->id] == QDPLL_ASSIGNMENT_TRUE || 
              qdpll->qdo_assignment_table[var->id] == QDPLL_ASSIGNMENT_FALSE);
      return qdpll->qdo_assignment_table[var->id];
    }
}


void
qdpll_print (QDPLL * qdpll, FILE * out)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  set_up_formula (qdpll);
#ifndef NDEBUG
#if QDPLL_ASSERT_FULL_FORMULA_INTEGRITY
  assert_full_formula_integrity (qdpll);
#endif
#endif
  assert (qdpll->pcnf.clauses.cnt ==
          count_constraints (&(qdpll->pcnf.clauses)));

  fprintf (out, "p cnf %d %d\n", qdpll->pcnf.max_declared_user_var_id,
           qdpll->pcnf.clauses.cnt);

  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.first->is_internal);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  assert (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.first));

  /* Print additional scope with FREE user variables, if any. */
  if (has_scope_free_user_var (qdpll, qdpll->pcnf.scopes.first))
      qdpll_print_aux_scope (qdpll, qdpll->pcnf.scopes.first, out);

  /* Print user scopes. This way, we also print variables which do not have
     occurrences. */
  Scope *s;
  for (s = qdpll->pcnf.user_scopes.first; s; s = s->link.next)
    {
      if (QDPLL_COUNT_STACK (s->vars) > 0)
        qdpll_print_aux_scope (qdpll, s, out);
    }

  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      assert (!c->is_cube);

      /* New: do not print clauses which effectively have been deleted from the
         clause stack by either deleting the group/frame or deactivating the group. */
      if (clause_has_popped_off_var (qdpll, c) || clause_has_inactive_var (qdpll, c))
        continue;

          /* For incremental use: do not print literals of internal variables. */
          LitID *p, *e;
          for (p = c->lits, e = p + c->num_lits; p < e; p++)
            {
              LitID lit = *p;
              Var *var = LIT2VARPTR(qdpll->pcnf.vars, lit);
              if (!var->is_internal)
                fprintf (out, "%d ", lit);
            }
          fprintf (out, "0\n");
    }
}


/* Print QDIMACS-compliant output to stdout as defined at:
   http://www.qbflib.org/qdimacs.html */
void
qdpll_print_qdimacs_output (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  /* NOTE: here we print the largest declared variable ID and the
     number of used original clauses. This might differ from the preamble
     of the original input file if that file was not strictly QDIMACS
     compliant or if clauses were removed. */
  const QDPLLResult result = qdpll->result;
  char *res_string;
  if (result == QDPLL_RESULT_UNKNOWN)
    res_string = "-1";
  else if (result == QDPLL_RESULT_SAT)
    res_string = "1";
  else if (result == QDPLL_RESULT_UNSAT)
    res_string = "0";
  else
    QDPLL_ABORT_QDPLL (1, "invalid result!");

  fprintf (stdout, "s cnf %s %d %d\n", res_string,
           qdpll->pcnf.max_declared_user_var_id, qdpll->pcnf.clauses.cnt);

  Scope *outer;
  assert (qdpll->pcnf.scopes.first);
  if (!qdpll->pcnf.user_scopes.first)
    {
      /* Formula is propositional; when unsatisfiable then cannot print
         countermodel. */
      if (result == QDPLL_RESULT_UNSAT)
        return;
      else
        outer = qdpll->pcnf.scopes.first;
    }
  else
    {
      if (result == QDPLL_RESULT_UNSAT)
        {
          /* Formula is unsatisfiable; cannot print countermodel if the
             outermost scope is existential or if the formula contains free
             variables, which by default are quantified existentially and
             leftmost. */
          if (qdpll->pcnf.user_scopes.first->type == QDPLL_QTYPE_EXISTS || 
              has_scope_free_user_var (qdpll, qdpll->pcnf.scopes.first))
            return;
          else
            outer = qdpll->pcnf.user_scopes.first;
        }
      else
        {
          assert (result == QDPLL_RESULT_SAT);
          /* Formula is satisfiable; cannot print countermodel if the
             outermost scope is universal AND if the formula DOES NOT contain free
             variables. */
          if (qdpll->pcnf.user_scopes.first->type == QDPLL_QTYPE_FORALL && 
              !has_scope_free_user_var (qdpll, qdpll->pcnf.scopes.first))
            return;
          else
            {
              outer = qdpll->pcnf.scopes.first;
              if (QDPLL_COUNT_STACK(qdpll->pcnf.scopes.first->vars) == 0)
                {
                  assert (outer->link.next);
                  assert (outer->link.next->type == outer->type);
                  outer = outer->link.next;
                }
            }
        }
    }

  Var *vars = qdpll->pcnf.vars;
  VarID *p, *e;
  for (p = outer->vars.start, e = outer->vars.top; p < e; p++)
    {
      assert (*p);
      VarID id = *p;
      Var *var = VARID2VARPTR (vars, id);
      assert (!var->id || var->id == id);
      QDPLLAssignment a;
      /* FIX: Do not print assignments of internal variables, ignore also
         reset internal variables. */
      if ((!var->is_internal && id <= qdpll_get_max_declared_var_id (qdpll)) && 
          (a = qdpll_get_value (qdpll, id)) != QDPLL_ASSIGNMENT_UNDEF)
        fprintf (stdout, "V %d 0\n", 
                 a == QDPLL_ASSIGNMENT_FALSE ? -id : id);
    }
}


void
qdpll_init_deps (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);

  set_up_formula (qdpll);

  if (!dm->is_init (dm))
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "Initializing dependencies.\n");
#if COMPUTE_STATS
      qdpll->stats.total_dep_man_init_calls++;
#endif
      dm->init (dm);
    }
}


void
qdpll_reset_deps (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  /* NOTE: at this point, we may have assigned assumptions which were provided
     by the user. */
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  if (dm->is_init (dm))
    dm->reset (dm);
  assert (!dm->is_init (dm));
}


/* Returns non-zero if variable 'id2' depends on variable 'id1', 
   i.e. if id1 < id2, with respect to the current dependency scheme. */
int 
qdpll_var_depends (QDPLL * qdpll, VarID x, VarID y)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (qdpll->state.decision_level != 0, 
                     "Unexpected decision level != 0; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (qdpll->assigned_vars != qdpll->bcp_ptr, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLL_ABORT_QDPLL (count_assigned_vars(qdpll) != 0, 
                     "Unexpected assignments of variables; solver must be in reset state!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");
  QDPLL_ABORT_QDPLL (!qdpll_is_var_declared (qdpll, x), "variable is not declared!");
  QDPLL_ABORT_QDPLL (!qdpll_is_var_declared (qdpll, y), "variable is not declared!");
  /* New: a variable is considered to be declared if the user has added it to
     the formula's prefix. However, if the variable does not occur in any
     clauses, then there can not be any dependencies. */
  if (!QDPLL_VAR_HAS_OCCS(VARID2VARPTR(qdpll->pcnf.vars, x)) || 
      !QDPLL_VAR_HAS_OCCS(VARID2VARPTR(qdpll->pcnf.vars, y)))
    return 0;
  return dm->depends(dm, x, y);
}


/* Note: could also return a collection of variable IDs. */
void
qdpll_print_deps (QDPLL * qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (qdpll->pcnf.max_declared_user_var_id >= qdpll->pcnf.size_vars,
                     "largest declared ID larger than size of variables!");
  QDPLL_ABORT_QDPLL (!qdpll_is_var_declared (qdpll, id), "variable is not declared!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");

  dm->print_deps (dm, id);
}


VarID
qdpll_get_max_declared_var_id (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  assert (qdpll->pcnf.max_declared_user_var_id == 
          find_max_declared_user_var_id (qdpll, qdpll->pcnf.vars + qdpll->pcnf.size_vars - 1));
  return qdpll->pcnf.max_declared_user_var_id;
}


/* Returns non-zero if and only if (1) a variable with ID 'id' has been added
   to the solver by a previous call of 'qdpll_add', 'qdpll_add_cube' or
   'qdpll_add_var_to_scope' and (2) that variable has not been cleaned up by
   the solver. A variable will be cleaned up if it is added to the solver but
   there are no clauses where that variable occurs. This function can be
   useful for incremental use of the solver: before adding a clause to the
   solver, this function can be used to check if the variable of each literal
   in the clause has been declared already. If not, then it can be declared by
   'qdpll_add_var_to_scope' and put in the right scope.
   NOTE: if a clause containing literals of undeclared variables is added by
   'qdpll_add' then these literals by default will be existentially quantified
   and put in the leftmost scope. */
int qdpll_is_var_declared (QDPLL * qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (id == 0, "Zero is not a valid variable ID!");
  if (id > qdpll->pcnf.max_declared_user_var_id)
    return 0;
  /* The solver has to ensure the following property. */
  QDPLL_ABORT_QDPLL (id >= qdpll->pcnf.size_user_vars, "Unexpected internal variable ID.");
  QDPLL_ABORT_QDPLL (qdpll->pcnf.size_user_vars > qdpll->pcnf.size_vars, 
                     "Unexpected sizes of variable table.");
  Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);
  /* The solver has to ensure the following properties. */
  QDPLL_ABORT_QDPLL (var->is_internal, "Unexpected internal variable ID.");
  QDPLL_ABORT_QDPLL (var->id && var->id != id, "Unexpected mismatch of variable IDs.");
  if (var->id)
    return var->id;
  /* Import the user prefix to make sure that 'var->id' is true for a user
     variable which has been deleted previously because it did not have
     occurrences. Redundant calls of 'import_user_scopes' are prevented by the
     flag 'qdpll->state.no_scheduled....'. */
  import_user_scopes (qdpll);
  return var->id;
}


/* Returns the nesting level 'level' in the range '1 <= level <=
   qdpll_get_max_scope_nesting()' of the previously declared variable with ID
   'id'. Returns 0 if the variable with ID 'id' is free, i.e. not explicitly
   associated to a quantifier block. Fails if 'id' does not correspond to a
   declared variable, which should be checked with function
   'qdpll_is_var_declared()' before. */
Nesting qdpll_get_nesting_of_var (QDPLL * qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (id == 0, "Value of 'id' must be greater than zero.");
  QDPLL_ABORT_QDPLL (!qdpll_is_var_declared (qdpll, id), 
                     "Variable with 'id' is not declared!");
  /* Make sure that user prefix is properly imported. This usually is done
     already in 'qdpll_is_var_declared' above and the additional call does not
     incur overhead. */
  import_user_scopes (qdpll);
  Var *var = VARID2VARPTR(qdpll->pcnf.vars, id);

  /* Return nesting level 0 if the variable is free. */
  if (!var->user_scope)
    {
      QDPLL_ABORT_QDPLL (!var->scope, "Null pointer encountered!");
      return 0;
    }

  QDPLL_ABORT_QDPLL(var->user_scope->nesting == 0 || 
                    var->user_scope->nesting > qdpll_get_max_scope_nesting(qdpll), 
                    "Unexpected user scope nesting!");
  return var->user_scope->nesting;
}


/* Returns the quantifier type (i.e. either QDPLL_QTYPE_EXISTS or
   QDPLL_QTYPE_FORALL) of the scope at nesting level 'nesting'. 
   Returns zero if there is no scope with nesting level 'nesting'. */
QDPLLQuantifierType 
qdpll_get_scope_type (QDPLL *qdpll, Nesting nesting)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (nesting == 0, "Parameter 'nesting' must be greater than zero!");
  if (nesting > qdpll_get_max_scope_nesting (qdpll))
    return QDPLL_QTYPE_UNDEF;
  Scope *scope = find_user_scope_at_nesting_level (qdpll, nesting);
  QDPLL_ABORT_QDPLL(!scope, "Unexpected null pointer to scope.");
  QDPLL_ABORT_QDPLL ((scope->type != QDPLL_QTYPE_EXISTS && 
                      scope->type != QDPLL_QTYPE_FORALL), "Unexpected scope type.");
  return scope->type;
}


/* Dump dependency graph to 'stdout' in DOT format. */
void
qdpll_dump_dep_graph (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");

  dm->dump_dep_graph (dm);
}


void
qdpll_print_stats (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (!(COMPUTE_STATS || COMPUTE_TIMES),
                     "must enable statistics!");
#if COMPUTE_TIMES
  /* Fix time stats when solver was interrupted e.g. by time-out. */
  if (qdpll->result == QDPLL_RESULT_UNKNOWN)
    qdpll->time_stats.total_sat_time +=
      (time_stamp () - qdpll->time_stats.sat_time_start);
#endif
#if COMPUTE_STATS
  assert (COMPUTE_STATS);
  fprintf (stderr, "\n---------------- STATS ----------------");
  fprintf (stderr, "\npushed assignments: \t%13llu\n",
           qdpll->stats.pushed_assignments);
  fprintf (stderr, "assignment flips: \t%13llu\n",
           qdpll->stats.assignment_flips);
  fprintf (stderr, "decisions: \t\t%13llu\n", qdpll->stats.decisions);
  fprintf (stderr, "dec. per assignm.: \t%13f\n",
           qdpll->stats.pushed_assignments ? qdpll->stats.decisions /
           (float) qdpll->stats.pushed_assignments : 0);
  fprintf (stderr, "backtracks: \t\t%13u\n", qdpll->state.num_backtracks);
  fprintf (stderr, "sat. results: \t\t%13llu\n", qdpll->stats.sat_results);
  fprintf (stderr, "unsat. results: \t%13llu\n", qdpll->stats.unsat_results);
  fprintf (stderr, "propagations: \t\t%13llu\n", qdpll->stats.propagations);
  fprintf (stderr, "pushed unit literals: \t%13llu ( top: %llu )\n",
           qdpll->stats.pushed_unit_literals,
           qdpll->stats.pushed_top_unit_literals);
  fprintf (stderr, "pushed univ. unit literals: \t%llu\n",
           qdpll->stats.pushed_univ_unit_literals);
  fprintf (stderr, "unit per assignm.: \t%13f\n",
           qdpll->stats.pushed_assignments ? qdpll->stats.
           pushed_unit_literals /
           (float) qdpll->stats.pushed_assignments : 0);
  fprintf (stderr, "pushed pure literals: \t%13llu ( top: %llu )\n",
           qdpll->stats.pushed_pure_literals,
           qdpll->stats.pushed_top_pure_literals);
  fprintf (stderr, "pure per assignm.: \t%13f\n",
           qdpll->stats.pushed_assignments ? qdpll->stats.
           pushed_pure_literals /
           (float) qdpll->stats.pushed_assignments : 0);
  fprintf (stderr, "deps init: \t\t%13llu\n\n",
           qdpll->stats.total_dep_man_init_calls);

  fprintf (stderr, "Total var.act. rescales:\t%llu\n",
           qdpll->stats.total_var_act_rescales);
  fprintf (stderr, "Total sat. cubes:\t\t%llu\n\n",
           qdpll->stats.total_sat_cubes);

  fprintf (stderr, "Total sat. result dlevels: \t%13llu\n",
           qdpll->stats.total_sat_results_dlevels);
  fprintf (stderr, "Avg. sat. result dlevel:\t%13f\n",
           qdpll->stats.sat_results ? qdpll->stats.total_sat_results_dlevels /
           (float) qdpll->stats.sat_results : 0);
  fprintf (stderr, "Total sat. result btlevels: \t%13llu\n",
           qdpll->stats.total_sat_results_btlevels);
  fprintf (stderr, "Avg. sat. result btlevel:\t%13f\n",
           qdpll->stats.sat_results ? qdpll->
           stats.total_sat_results_btlevels /
           (float) qdpll->stats.sat_results : 0);
  fprintf (stderr, "Total sat. result btdist: \t%13llu\n",
           qdpll->stats.total_sat_results_btdist);
  fprintf (stderr, "Avg. sat. result btdist:\t%13f\n",
           qdpll->stats.sat_results ? qdpll->stats.total_sat_results_btdist /
           (float) qdpll->stats.sat_results : 0);

  fprintf (stderr, "Total unsat. result dlevels: \t%13llu\n",
           qdpll->stats.total_unsat_results_dlevels);
  fprintf (stderr, "Avg. unsat. result dlevel:\t%13f\n",
           qdpll->stats.unsat_results ? qdpll->
           stats.total_unsat_results_dlevels /
           (float) qdpll->stats.unsat_results : 0);
  fprintf (stderr, "Total unsat. result btlevels: \t%13llu\n",
           qdpll->stats.total_unsat_results_btlevels);
  fprintf (stderr, "Avg. unsat. result btlevel:\t%13f\n",
           qdpll->stats.unsat_results ? qdpll->
           stats.total_unsat_results_btlevels /
           (float) qdpll->stats.unsat_results : 0);
  fprintf (stderr, "Total unsat. result btdist: \t%13llu\n",
           qdpll->stats.total_unsat_results_btdist);
  fprintf (stderr, "Avg. unsat. result btdist:\t%13f\n",
           qdpll->stats.unsat_results ? qdpll->
           stats.total_unsat_results_btdist /
           (float) qdpll->stats.unsat_results : 0);
  fprintf (stderr, "Total prop. dlevels: \t\t%13llu\n",
           qdpll->stats.total_prop_dlevels);
  fprintf (stderr, "Avg. prop. dlevel:\t\t%13f\n\n",
           qdpll->stats.propagations ? qdpll->stats.total_prop_dlevels /
           (float) qdpll->stats.propagations : 0);

  fprintf (stderr, "Total restarts: \t%13u\n", qdpll->state.num_restarts);
  fprintf (stderr, "Total restart dlevels: \t%13llu\n",
           qdpll->stats.total_restart_dlevels);
  fprintf (stderr, "Avg. restart dlevel:\t%13f\n",
           qdpll->state.num_restarts ? qdpll->stats.total_restart_dlevels /
           (float) qdpll->state.num_restarts : 0);
  fprintf (stderr, "Total restart-at dlevels: %13llu\n",
           qdpll->stats.total_restart_at_dlevels);
  fprintf (stderr, "Avg. restart-at dlevel:\t%13f\n",
           qdpll->state.num_restarts ? qdpll->stats.total_restart_at_dlevels /
           (float) qdpll->state.num_restarts : 0);
  fprintf (stderr, "Total restart-at dist: \t%13llu\n",
           qdpll->stats.total_restart_at_dist);
  fprintf (stderr, "Avg. restart-at dist:\t%13f\n\n",
           qdpll->state.num_restarts ? qdpll->stats.total_restart_at_dist /
           (float) qdpll->state.num_restarts : 0);

  fprintf (stderr,
           "NOTE: literal visits NOT including early watcher checking.\n");
  fprintf (stderr, "Literal watcher total find-calls:\t%13llu\n",
           qdpll->stats.total_lit_watcher_find_calls);
  fprintf (stderr, "Literal watcher total literal visits:\t%13llu\n",
           qdpll->stats.total_lit_watcher_find_lit_visits);
  fprintf (stderr, "Literal watcher avg. literal visits:\t%13f\n\n",
           qdpll->stats.total_lit_watcher_find_calls ?
           qdpll->stats.total_lit_watcher_find_lit_visits /
           (float) qdpll->stats.total_lit_watcher_find_calls : 0);

  fprintf (stderr, "Literal watcher update calls:\t\t%13llu\n",
           qdpll->stats.total_lit_watcher_update_calls);
  fprintf (stderr, "Literal watcher update sat. by lw:\t%13llu\n",
           qdpll->stats.total_lit_watcher_update_sat_by_lw);
  fprintf (stderr, "Literal watcher update sat. by rw:\t%13llu\n",
           qdpll->stats.total_lit_watcher_update_sat_by_rw);
  fprintf (stderr, "Literal watcher update w-sat. ratio:\t%13f\n\n",
           qdpll->stats.total_lit_watcher_update_calls ?
           (qdpll->stats.total_lit_watcher_update_sat_by_lw +
            qdpll->stats.total_lit_watcher_update_sat_by_rw) /
           (float) qdpll->stats.total_lit_watcher_update_calls : 0);

  fprintf (stderr, "Clause watcher total find-calls:\t%13llu\n",
           qdpll->stats.total_clause_watcher_find_calls);
  fprintf (stderr, "Clause watcher total clause visits:\t%13llu\n",
           qdpll->stats.total_clause_watcher_find_clause_visits);
  fprintf (stderr, "Clause watcher total l.clause visits:\t%13llu\n",
           qdpll->stats.total_clause_watcher_find_learnt_clause_visits);
  fprintf (stderr, "Clause watcher avg. clause visits:\t%13f\n",
           qdpll->stats.total_clause_watcher_find_calls ?
           qdpll->stats.total_clause_watcher_find_clause_visits /
           (float) qdpll->stats.total_clause_watcher_find_calls : 0);
  fprintf (stderr, "Clause watcher avg. l.clause visits:\t%13f\n\n",
           qdpll->stats.total_clause_watcher_find_calls ?
           qdpll->stats.total_clause_watcher_find_learnt_clause_visits /
           (float) qdpll->stats.total_clause_watcher_find_calls : 0);

  fprintf (stderr,
           "NOTE: literal visits including early watcher checking.\n");
  fprintf (stderr, "Clause sat. total calls:\t%13llu\n",
           qdpll->stats.total_is_clause_sat_calls);
  fprintf (stderr, "Clause sat. total lit. visits:\t%13llu\n",
           qdpll->stats.total_is_clause_sat_lit_visits);
  fprintf (stderr, "Clause sat. avg. lit. visits:\t%13f\n",
           qdpll->stats.total_is_clause_sat_calls ?
           qdpll->stats.total_is_clause_sat_lit_visits /
           (float) qdpll->stats.total_is_clause_sat_calls : 0);
  fprintf (stderr, "Clause sat. by lw:\t\t%13llu\n",
           qdpll->stats.total_is_clause_sat_by_lw);
  fprintf (stderr, "Clause sat. by rw:\t\t%13llu\n",
           qdpll->stats.total_is_clause_sat_by_rw);
  fprintf (stderr, "Clause sat. w-sat ratio:\t%13f\n\n",
           qdpll->stats.total_is_clause_sat_calls ?
           (qdpll->stats.total_is_clause_sat_by_lw +
            qdpll->stats.total_is_clause_sat_by_rw) /
           (float) qdpll->stats.total_is_clause_sat_calls : 0);

  fprintf (stderr, "BLits tested:\t\t%13llu\n", qdpll->stats.blits_tested);
  fprintf (stderr, "BLits disabe:\t\t%13llu\n", qdpll->stats.blits_disabling);
  assert (qdpll->stats.blits_disabling <= qdpll->stats.blits_tested);
  fprintf (stderr, "BLits disable ratio:\t%13f\n",
           qdpll->stats.blits_tested ?
           qdpll->stats.blits_disabling /
           (float) qdpll->stats.blits_tested : 0);
  fprintf (stderr, "BLits avg. tested:\t%13f\n\n",
           qdpll->stats.propagations ?
           qdpll->stats.blits_tested / (float) qdpll->stats.propagations : 0);

  fprintf (stderr, "BLit update calls:\t%13llu\n",
           qdpll->stats.blits_update_calls);
  fprintf (stderr, "BLit update done:\t%13llu\n",
           qdpll->stats.blits_update_done);
  fprintf (stderr, "BLits update avg. done:\t%13f\n\n",
           qdpll->stats.blits_update_calls ?
           qdpll->stats.blits_update_done /
           (float) qdpll->stats.blits_update_calls : 0);
  fprintf (stderr, "BLits update visits:\t%13llu\n",
           qdpll->stats.blits_update_visits);
  fprintf (stderr, "BLits update avg. visits:\t%13f\n\n",
           qdpll->stats.blits_update_calls ?
           qdpll->stats.blits_update_visits /
           (float) qdpll->stats.blits_update_calls : 0);

  fprintf (stderr, "BLits pure tested:\t\t%13llu\n",
           qdpll->stats.blits_pure_tested);
  fprintf (stderr, "BLits pure disabe:\t\t%13llu\n",
           qdpll->stats.blits_pure_disabling);
  assert (qdpll->stats.blits_pure_disabling <=
          qdpll->stats.blits_pure_tested);
  fprintf (stderr, "BLits pure disable ratio:\t%13f\n",
           qdpll->stats.blits_pure_tested ? qdpll->stats.
           blits_pure_disabling / (float) qdpll->stats.blits_pure_tested : 0);
  fprintf (stderr, "BLits pure avg. tested:\t%13f\n\n",
           qdpll->stats.total_clause_watcher_find_calls ? qdpll->stats.
           blits_pure_tested /
           (float) qdpll->stats.total_clause_watcher_find_calls : 0);

  fprintf (stderr, "Notify-list stats (literal and clause watching):\n");
  fprintf (stderr, "Avg. litw. notify-list cnt:\t\t%f\n",
           qdpll->stats.total_notify_litw_list_adds ?
           qdpll->stats.total_notify_litw_list_cnt /
           (float) qdpll->stats.total_notify_litw_list_adds : 0);
  fprintf (stderr, "Avg. litw. notify-list size:\t\t%f ( filled: %f )\n",
           qdpll->stats.total_notify_litw_list_adds ?
           qdpll->stats.total_notify_litw_list_size /
           (float) qdpll->stats.total_notify_litw_list_adds : 0,
           (qdpll->stats.total_notify_litw_list_size ?
            qdpll->stats.total_notify_litw_list_cnt /
            (float) qdpll->stats.total_notify_litw_list_size : 0));
  fprintf (stderr, "Avg. clausew. notify-list cnt:\t\t%f\n",
           qdpll->stats.total_notify_clausew_list_adds ?
           qdpll->stats.total_notify_clausew_list_cnt /
           (float) qdpll->stats.total_notify_clausew_list_adds : 0);
  fprintf (stderr, "Avg. clausew. notify-list size:\t\t%f ( filled: %f )\n",
           qdpll->stats.total_notify_clausew_list_adds ?
           qdpll->stats.total_notify_clausew_list_size /
           (float) qdpll->stats.total_notify_clausew_list_adds : 0,
           qdpll->stats.total_notify_clausew_list_size ?
           qdpll->stats.total_notify_clausew_list_cnt /
           (float) qdpll->stats.total_notify_clausew_list_size : 0);
  fprintf (stderr, "Avg. occ. cnt:\t\t\t\t%f\n\n",
           qdpll->stats.total_occ_list_adds ?
           qdpll->stats.total_occ_list_cnt /
           (float) qdpll->stats.total_occ_list_adds : 0);

  fprintf (stderr, "Total covers:\t\t\t\t%llu\n",
           qdpll->stats.initial_cubes);

  fprintf (stderr, "Total learnt cubes mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_cubes_mtfs);
  fprintf (stderr, "Total learnt clause mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_clauses_mtfs);
  fprintf (stderr, "Total learnt constr. mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_clauses_mtfs +
           qdpll->stats.total_learnt_cubes_mtfs);

  fprintf (stderr, "Total learnt constr.:\t\t%llu\n",
           qdpll->stats.total_learnt_cubes +
           qdpll->stats.total_learnt_clauses);
  fprintf (stderr, "Total learnt clauses:\t\t%llu\n",
           qdpll->stats.total_learnt_clauses);
  fprintf (stderr, "Total learnt cubes:\t\t%llu\n",
           qdpll->stats.total_learnt_cubes);
  fprintf (stderr, "Total learnt constr. sizes:\t%llu\n",
           qdpll->stats.total_learnt_clauses_size +
           qdpll->stats.total_learnt_cubes_size);
  fprintf (stderr, "Total learnt clause sizes:\t%llu\n",
           qdpll->stats.total_learnt_clauses_size);
  fprintf (stderr, "Total learnt cube sizes:\t%llu\n",
           qdpll->stats.total_learnt_cubes_size);
  fprintf (stderr, "Avg. learnt clause size:\t%f\n",
           qdpll->stats.total_learnt_clauses ? qdpll->stats.
           total_learnt_clauses_size /
           (float) (qdpll->stats.total_learnt_clauses) : 0);
  fprintf (stderr, "Avg. learnt cube size:\t\t%f\n",
           qdpll->stats.total_learnt_cubes ? qdpll->stats.
           total_learnt_cubes_size /
           (float) (qdpll->stats.total_learnt_cubes) : 0);
  fprintf (stderr, "Avg. learnt constr. size:\t%f\n\n",
           (qdpll->stats.total_learnt_cubes
            || qdpll->stats.total_learnt_clauses) ? (qdpll->stats.
                                                     total_learnt_clauses_size
                                                     +
                                                     qdpll->stats.
                                                     total_learnt_cubes_size)
           / (float) (qdpll->stats.total_learnt_cubes +
                      qdpll->stats.total_learnt_clauses) : 0);

  fprintf (stderr, "Total learnt tautologies: \t%llu ( %f of learnt constraints)\n", qdpll->stats.total_learnt_taut_cubes +
           qdpll->stats.total_learnt_taut_clauses, 
           (qdpll->stats.total_learnt_cubes + qdpll->stats.total_learnt_clauses) ? 
           (qdpll->stats.total_learnt_taut_cubes + qdpll->stats.total_learnt_taut_clauses) / 
           (float)(qdpll->stats.total_learnt_cubes + qdpll->stats.total_learnt_clauses) : 0);
  fprintf (stderr, "Total learnt taut. clauses: \t%llu ( %f of learnt clauses)\n", 
           qdpll->stats.total_learnt_taut_clauses, qdpll->stats.total_learnt_clauses ? 
           (qdpll->stats.total_learnt_taut_clauses / (float) qdpll->stats.total_learnt_clauses) : 0);
  fprintf (stderr, "Total learnt taut. cubes: \t%llu ( %f of learnt cubes)\n", 
           qdpll->stats.total_learnt_taut_cubes, qdpll->stats.total_learnt_cubes ? 
           (qdpll->stats.total_learnt_taut_cubes / (float) qdpll->stats.total_learnt_cubes) : 0);

  fprintf (stderr, "Last lclauses size:\t\t%d\n", qdpll->state.lclauses_size);
  fprintf (stderr, "Last lclauses cnt:\t\t%d\n",
           qdpll->pcnf.learnt_clauses.cnt);
  fprintf (stderr, "Last lcubes size:\t\t%d\n", qdpll->state.lcubes_size);
  fprintf (stderr, "Last lcubes cnt:\t\t%d\n", qdpll->pcnf.learnt_cubes.cnt);
  fprintf (stderr, "Total constr. resizes:\t\t%u\n",
           (qdpll->state.clause_resizes + qdpll->state.cube_resizes));
  fprintf (stderr, "Total cube resizes:\t\t%u\n", qdpll->state.cube_resizes);
  fprintf (stderr, "Total clause resizes:\t\t%u\n",
           qdpll->state.clause_resizes);
  fprintf (stderr, "Total dels. in resizes:\t\t%llu\n",
           qdpll->stats.total_constraint_dels);
  fprintf (stderr, "Total cube dels.:\t\t%llu\n",
           qdpll->stats.total_cube_dels);
  fprintf (stderr, "Total clause dels.:\t\t%llu\n",
           qdpll->stats.total_clause_dels);
  fprintf (stderr, "Avg. dels. per resize:\t\t%f\n\n",
           (qdpll->state.clause_resizes || qdpll->state.cube_resizes) ?
           qdpll->stats.total_constraint_dels /
           (float) (qdpll->state.clause_resizes +
                    qdpll->state.cube_resizes) : 0);

  fprintf (stderr, "C.resize unit cl. cnt.:\t%llu ( avg.: %f )\n",
           qdpll->stats.total_del_unit_clause_cnt,
           qdpll->stats.total_clause_dels ?
           qdpll->stats.total_del_unit_clause_cnt /
           (float) qdpll->stats.total_clause_dels : 0);
  fprintf (stderr, "C.resize res cl. cnt.:\t%llu ( avg.: %f )\n",
           qdpll->stats.total_del_res_clause_cnt,
           qdpll->stats.total_clause_dels ?
           qdpll->stats.total_del_res_clause_cnt /
           (float) qdpll->stats.total_clause_dels : 0);
  fprintf (stderr, "C.resize unit cu. cnt.:\t%llu ( avg.: %f )\n",
           qdpll->stats.total_del_unit_cube_cnt,
           qdpll->stats.total_cube_dels ?
           qdpll->stats.total_del_unit_cube_cnt /
           (float) qdpll->stats.total_cube_dels : 0);
  fprintf (stderr, "C.resize res cu. cnt.:\t%llu ( avg.: %f )\n\n",
           qdpll->stats.total_del_res_cube_cnt,
           qdpll->stats.total_cube_dels ?
           qdpll->stats.total_del_res_cube_cnt /
           (float) qdpll->stats.total_cube_dels : 0);

  fprintf (stderr, "Total splits. ig.unit clauses:\t%llu\n",
           qdpll->stats.total_splits_ignored_unit_clauses);
  fprintf (stderr, "Total splits. ig.unit cubes:\t%llu\n",
           qdpll->stats.total_splits_ignored_unit_cubes);
  fprintf (stderr, "Total splits. ig.empty clauses:\t%llu\n",
           qdpll->stats.total_splits_ignored_empty_clauses);
  fprintf (stderr, "Total splits. ig.sat. cubes:\t%llu\n\n",
           qdpll->stats.total_splits_ignored_satisfied_cubes);

  fprintf (stderr, "Total resolutions:\t\t%llu\n",
           qdpll->stats.num_unsat_res_steps + qdpll->stats.num_sat_res_steps);
  fprintf (stderr, "Total sat. res.:\t\t%llu\n",
           qdpll->stats.num_sat_res_steps);
  fprintf (stderr, "Total unsat. res.:\t\t%llu\n",
           qdpll->stats.num_unsat_res_steps);
  fprintf (stderr, "Avg. resolutions:\t\t%f\n",
           (qdpll->stats.sat_results || qdpll->stats.unsat_results) ?
           (qdpll->stats.num_unsat_res_steps +
            qdpll->stats.num_sat_res_steps) /
           ((float) qdpll->stats.sat_results +
            qdpll->stats.unsat_results) : 0);
  fprintf (stderr, "Avg. res. per sat.:\t\t%f\n",
           qdpll->stats.sat_results ? qdpll->stats.num_sat_res_steps /
           (float) qdpll->stats.sat_results : 0);
  fprintf (stderr, "Avg. res. per unsat.:\t\t%f\n\n",
           qdpll->stats.unsat_results ? qdpll->stats.num_unsat_res_steps /
           (float) qdpll->stats.unsat_results : 0);

  fprintf (stderr, "Total type-red. calls:\t\t%llu\n",
           qdpll->stats.total_type_reduce_calls);
  fprintf (stderr, "Total type-red. effort:\t\t%llu\n",
           qdpll->stats.total_type_reduce_effort);
  fprintf (stderr, "Total type-red. costs:\t\t%llu\n",
           qdpll->stats.total_type_reduce_costs);
  fprintf (stderr, "Avg. type-red costs: \t\t%f\n",
           qdpll->stats.total_type_reduce_calls ?
           qdpll->stats.total_type_reduce_costs /
           ((float) qdpll->stats.total_type_reduce_calls) : 0);
  fprintf (stderr, "Avg. type-red effort: \t\t%f\n",
           qdpll->stats.total_type_reduce_calls ?
           qdpll->stats.total_type_reduce_effort /
           ((float) qdpll->stats.total_type_reduce_calls) : 0);
  fprintf (stderr, "Total type-red. lits:\t\t%llu\n",
           qdpll->stats.total_type_reduce_lits);
  fprintf (stderr, "Avg. type-red. lits per call:\t%f\n\n",
           qdpll->stats.total_type_reduce_calls ?
           qdpll->stats.total_type_reduce_lits /
           (float) qdpll->stats.total_type_reduce_calls : 0);

  fprintf (stderr, "Choose-vars: \t\t%llu\n",
           qdpll->stats.num_learn_choose_vars);
  fprintf (stderr, "Trail pivots:\t\t%llu ( %f )\n\n",
           qdpll->stats.num_learn_trail_pivot,
           qdpll->stats.num_learn_choose_vars ?
           (float) qdpll->stats.num_learn_trail_pivot /
           qdpll->stats.num_learn_choose_vars : 0);

  fprintf (stderr, "Total l-watched:\t%llu\n", qdpll->stats.total_lwatched);
  fprintf (stderr, "Total tested:\t\t%llu\n",
           qdpll->stats.total_lwatched_tested);
  fprintf (stderr, "Total skipped:\t\t%llu\n",
           qdpll->stats.non_dep_lwatched_skipped);
  fprintf (stderr, "N.dep. skipped/call:\t%f\n",
           qdpll->stats.total_lit_watcher_find_calls ? (float) qdpll->
           stats.non_dep_lwatched_skipped /
           qdpll->stats.total_lit_watcher_find_calls : 0);
  fprintf (stderr, "N.dep. skipped/lwatched:\t%f\n",
           qdpll->stats.total_lwatched ? (float) qdpll->
           stats.non_dep_lwatched_skipped / qdpll->stats.total_lwatched : 0);
  fprintf (stderr, "N.dep. skipped/tested:\t%f\n",
           qdpll->stats.total_lwatched_tested ? (float) qdpll->
           stats.non_dep_lwatched_skipped /
           qdpll->stats.total_lwatched_tested : 0);
  fprintf (stderr, "N.dep. tested/call:\t%f\n",
           qdpll->stats.total_lit_watcher_find_calls ? (float) qdpll->
           stats.total_lwatched_tested /
           qdpll->stats.total_lit_watcher_find_calls : 0);
  fprintf (stderr, "N.dep. tested/lwatched:\t%f\n\n",
           qdpll->stats.total_lwatched ? (float) qdpll->
           stats.total_lwatched_tested / qdpll->stats.total_lwatched : 0);

  fprintf (stderr, "Total unit lcubes: %llu\n",
           qdpll->stats.total_unit_lcubes);
  fprintf (stderr, "Total sat lcubes: %llu\n", qdpll->stats.total_sat_lcubes);
  fprintf (stderr, "Total unit lclauses: %llu\n",
           qdpll->stats.total_unit_lclauses);
  fprintf (stderr, "Total empty lclauses: %llu\n\n",
           qdpll->stats.total_empty_lclauses);

  fprintf (stderr, "Total unit taut lcubes: %llu ( %f of unit lcubes )\n",
           qdpll->stats.total_unit_taut_lcubes, qdpll->stats.total_unit_lcubes ? (qdpll->stats.total_unit_taut_lcubes / (float)qdpll->stats.total_unit_lcubes) : 0);
  fprintf (stderr, "Total sat taut lcubes: %llu ( %f of sat lcubes )\n", qdpll->stats.total_sat_taut_lcubes, 
           qdpll->stats.total_sat_lcubes ? (qdpll->stats.total_sat_taut_lcubes / (float)qdpll->stats.total_sat_lcubes) : 0);
  fprintf (stderr, "Total unit taut lclauses: %llu ( %f of unit lclauses )\n",
           qdpll->stats.total_unit_taut_lclauses, qdpll->stats.total_unit_lclauses ? (qdpll->stats.total_unit_taut_lclauses / (float)qdpll->stats.total_unit_lclauses) : 0);
  fprintf (stderr, "Total empty taut lclauses: %llu ( %f of empty lclauses )\n\n",
           qdpll->stats.total_empty_taut_lclauses, qdpll->stats.total_empty_lclauses ? (qdpll->stats.total_empty_taut_lclauses / (float)qdpll->stats.total_empty_lclauses) : 0);

  fprintf (stderr, "Total const min lits reducible: %llu\n",
           qdpll->stats.constr_min_lits_reducible);
  fprintf (stderr, "Avg. const min lits reducible: %f\n\n",
           qdpll->stats.constr_min_lits_seen ?
           qdpll->stats.constr_min_lits_reducible /
           (float) qdpll->stats.constr_min_lits_seen : 0);

  fprintf (stderr, "empty-formula-watcher total update calls: %llu\n", 
           qdpll->stats.empty_formula_watcher_total_update_calls);
  fprintf (stderr, "empty-formula-watcher effective update calls: %llu ( %f of total) \n\n", 
           qdpll->stats.empty_formula_watcher_effective_update_calls, qdpll->stats.empty_formula_watcher_total_update_calls ? 
           (qdpll->stats.empty_formula_watcher_effective_update_calls / (float) qdpll->stats.empty_formula_watcher_total_update_calls) : 0);

  fprintf (stderr, "empty-formula-watcher is-clause-sat cache accesses: %llu\n", qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses);
  fprintf (stderr, "empty-formula-watcher is-clause-sat cache hits: %llu ( %f per access)\n", qdpll->stats.empty_formula_watcher_is_clause_sat_cache_hits, 
           qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses ? (qdpll->stats.empty_formula_watcher_is_clause_sat_cache_hits / 
                                                                  (float)qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "empty-formula-watcher is-clause-sat found blocked: %llu ( %f per access)\n", qdpll->stats.empty_formula_watcher_is_clause_sat_found_blocked, 
           qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses ? (qdpll->stats.empty_formula_watcher_is_clause_sat_found_blocked / 
                                                                  (float)qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "empty-formula-watcher is-clause-sat found sat: %llu ( %f per access)\n\n", qdpll->stats.empty_formula_watcher_is_clause_sat_found_sat, 
           qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses ? (qdpll->stats.empty_formula_watcher_is_clause_sat_found_sat / 
                                                                  (float)qdpll->stats.empty_formula_watcher_is_clause_sat_cache_accesses) : 0);

  fprintf (stderr, "QBCE completed rounds: %llu\n", qdpll->stats.qbcp_qbce_rounds);
  fprintf (stderr, "QBCE total blocked clauses: %llu ( %f per round )\n", qdpll->stats.qbcp_qbce_clauses_blocked, 
           qdpll->stats.qbcp_qbce_rounds ? (qdpll->stats.qbcp_qbce_clauses_blocked / (float) qdpll->stats.qbcp_qbce_rounds) : 0);
  /* Clauses blocked by preprocessing, not taking top-level assignment into account. */
  fprintf (stderr, "QBCE preprocessing blocked clauses: %d\n", 
           QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) >= 1 ? 
           QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]) : 0);
  fprintf (stderr, "QBCE backtracks to top level: %llu\n", qdpll->stats.qbcp_qbce_backtracks_to_toplevel);
  fprintf (stderr, "QBCE inprocessing rounds: %llu\n", qdpll->stats.qbcp_qbce_inprocessing_rounds);
  /* Clauses additionally blocked by inprocessing, taking top-level assignment into account.*/
  fprintf (stderr, "QBCE inprocessing blocked clauses: %d\n", 
           QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses) >= 2 ? 
           QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[1]) : 0);

  fprintf (stderr, "QBCE initial cubes: %llu\n", qdpll->stats.initial_cubes);
  float avg_initial_cube_size = qdpll->stats.initial_cubes ? 
    (qdpll->stats.initial_cubes_sizes / (float) qdpll->stats.initial_cubes) : 0;
  fprintf (stderr, "QBCE initial cubes sizes: %llu ( %f per initial cube, which is %f of used vars %d )\n", 
           qdpll->stats.initial_cubes_sizes, 
           avg_initial_cube_size, qdpll->pcnf.used_vars ? 
           (avg_initial_cube_size / (float) qdpll->pcnf.used_vars) : 0, qdpll->pcnf.used_vars);
  fprintf (stderr, "QBCE initial cubes univ lits: %llu ( %f of initial cube size %f )\n", qdpll->stats.initial_cubes_univ_lits, 
           qdpll->stats.initial_cubes_sizes ? (qdpll->stats.initial_cubes_univ_lits / 
                                               (float) qdpll->stats.initial_cubes_sizes) : 0, avg_initial_cube_size);

  float avg_current_blocked_per_init_cube = qdpll->stats.initial_cubes ? 
    (qdpll->stats.qbcp_qbce_total_current_blocked_clauses / (float) qdpll->stats.initial_cubes) : 0;
  fprintf (stderr, "QBCE total clauses blocked when learning initial cube: %llu ( %f per initial cube, which is %f of CNF size %d )\n", 
           qdpll->stats.qbcp_qbce_total_current_blocked_clauses, avg_current_blocked_per_init_cube, 
           qdpll->pcnf.clauses.cnt ? (avg_current_blocked_per_init_cube / (float) qdpll->pcnf.clauses.cnt) : 0, qdpll->pcnf.clauses.cnt);

  fprintf (stderr, "QBCE clauses ignored by clause size limit: %llu ( %f of total clauses %d )\n", 
           qdpll->stats.qbcp_qbce_ignored_clauses_by_size_limit, qdpll->pcnf.clauses.cnt ? 
           (qdpll->stats.qbcp_qbce_ignored_clauses_by_size_limit / (float) qdpll->pcnf.clauses.cnt) : 0, qdpll->pcnf.clauses.cnt);

  fprintf (stderr, "QBCE maybe blocking lits ignored by clause size limit: %llu ( %f of total maybe blocking lits %llu )\n", 
           qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_size_limit, 
           qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen ? 
           (qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_size_limit / 
            (float) qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen) : 0, 
           qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen);

  fprintf (stderr, "QBCE maybe blocking lits ignored by occ limit: %llu ( %f of total maybe blocking lits %llu )\n", 
           qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_occ_limit, 
           qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen ? 
           (qdpll->stats.qbcp_qbce_ignored_maybe_blocking_literals_by_occ_limit / 
            (float) qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen) : 0, 
           qdpll->stats.qbcp_qbce_total_maybe_blocking_literals_seen);

  fprintf (stderr, "QBCE clauses seen: %llu ( %f of CNF size)\n", qdpll->stats.qbcp_qbce_clauses_seen, 
           qdpll->stats.qbcp_qbce_clauses_seen ? (qdpll->stats.qbcp_qbce_clauses_seen / (float)qdpll->pcnf.clauses.cnt) : 0);
  fprintf (stderr, "QBCE literals seen: %llu\n", qdpll->stats.qbcp_qbce_literals_seen);
  fprintf (stderr, "QBCE seen literals per clause: %f\n", qdpll->stats.qbcp_qbce_clauses_seen ? 
           (qdpll->stats.qbcp_qbce_literals_seen / (float)qdpll->stats.qbcp_qbce_clauses_seen) : 0);
  fprintf (stderr, "QBCE find-entry calls: %llu\n", qdpll->stats.qbcp_qbce_find_entry_calls);
  fprintf (stderr, "QBCE find entries seen: %llu ( %f per call)\n\n", qdpll->stats.qbcp_qbce_find_entries_seen, 
           qdpll->stats.qbcp_qbce_find_entry_calls ? (qdpll->stats.qbcp_qbce_find_entries_seen / 
                                                      (float)qdpll->stats.qbcp_qbce_find_entry_calls) : 0);

  fprintf (stderr, "QBCE watched-occ find-entry calls: %llu\n", qdpll->stats.qbcp_qbce_watched_occ_find_entry_calls);
  fprintf (stderr, "QBCE watched-occ find entries seen: %llu ( %f per call)\n", qdpll->stats.qbcp_qbce_watched_occ_find_entries_seen, 
           qdpll->stats.qbcp_qbce_watched_occ_find_entry_calls ? (qdpll->stats.qbcp_qbce_watched_occ_find_entries_seen / 
                                                      (float)qdpll->stats.qbcp_qbce_watched_occ_find_entry_calls) : 0);
  fprintf (stderr, "QBCE watched-occ add/remove calls: %llu\n", qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_calls);
  fprintf (stderr, "QBCE watched-occ ad/remove lits seen: %llu ( %f per call)\n\n", qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_lits_seen, 
           qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_calls ? (qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_lits_seen / 
                                                      (float)qdpll->stats.qbcp_qbce_watched_occ_add_or_remove_calls) : 0);

  fprintf (stderr, "QBCE is-clause-sat cache accesses: %llu\n", qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses);
  fprintf (stderr, "QBCE is-clause-sat cache hits: %llu ( %f per access)\n", qdpll->stats.qbcp_qbce_is_clause_sat_cache_hits, 
           qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_is_clause_sat_cache_hits / 
                                                                  (float)qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "QBCE is-clause-sat found blocked: %llu ( %f per access)\n", qdpll->stats.qbcp_qbce_is_clause_sat_found_blocked, 
           qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_is_clause_sat_found_blocked / 
                                                                  (float)qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "QBCE is-clause-sat found sat: %llu ( %f per access)\n\n", qdpll->stats.qbcp_qbce_is_clause_sat_found_sat, 
           qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_is_clause_sat_found_sat / 
                                                                  (float)qdpll->stats.qbcp_qbce_is_clause_sat_cache_accesses) : 0);

  fprintf (stderr, "QBCE witness is-clause-sat cache accesses: %llu\n", qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses);
  fprintf (stderr, "QBCE witness is-clause-sat cache hits: %llu ( %f per access)\n", qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_hits, 
           qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_hits / 
                                                                  (float)qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "QBCE witness is-clause-sat found blocked: %llu ( %f per access)\n", qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_blocked, 
           qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_blocked / 
                                                                  (float)qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses) : 0);
  fprintf (stderr, "QBCE witness is-clause-sat found sat: %llu ( %f per access)\n\n", qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_sat, 
           qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses ? (qdpll->stats.qbcp_qbce_witness_is_clause_sat_found_sat / 
                                                                  (float)qdpll->stats.qbcp_qbce_witness_is_clause_sat_cache_accesses) : 0);

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  fprintf (stderr, "Cover-by-assignment elim-univ dynamically disabled: %s\n", 
          qdpll->state.elim_univ_dynamic_disabled ? "yes" : "no");
  unsigned long long int univ_tried = qdpll->stats.elim_univ_vars_total_univ_vars;
  fprintf (stderr, "Total cover-by-assignment elim-univ tried: %llu\n", 
           univ_tried);
  fprintf (stderr, "Total cover-by-assignment elim-univ eliminated: %llu ( %f success rate)\n", 
           qdpll->stats.elim_univ_vars_eliminated, univ_tried ? 
           (qdpll->stats.elim_univ_vars_eliminated / (float) univ_tried) : 0);
  fprintf (stderr, "Total cover-by-assignment elim-univ clauses seen: %llu which is %f of input CNF size %d\n", 
           qdpll->stats.elim_univ_vars_clauses_seen, qdpll->pcnf.clauses.cnt ? 
           (qdpll->stats.elim_univ_vars_clauses_seen / (float)qdpll->pcnf.clauses.cnt) : 0, qdpll->pcnf.clauses.cnt);
  float clauses_per_tried = univ_tried ? 
           (qdpll->stats.elim_univ_vars_clauses_seen / (float) univ_tried) : 0;
  fprintf (stderr, "Total cover-by-assignment elim-univ clauses seen per tried:  %f which is %f of input CNF size %d\n\n", 
           clauses_per_tried, 
           qdpll->pcnf.clauses.cnt ? (clauses_per_tried / qdpll->pcnf.clauses.cnt) : 0, qdpll->pcnf.clauses.cnt);
#endif

  fprintf (stderr, "Total trivial falsity disabled: %s\n", qdpll->state.trivial_falsity_disabled ? "yes" : "no");
  fprintf (stderr, "Total trivial falsity time: %f (per try: %f )\n", qdpll->state.trivial_falsity_time, 
           qdpll->state.trivial_falsity_tried ? (qdpll->state.trivial_falsity_time / qdpll->state.trivial_falsity_tried) : 0);
  fprintf (stderr, "Total trivial falsity tried: %d\n", qdpll->state.trivial_falsity_tried);
  fprintf (stderr, "Total trivial falsity detected: %llu\n", qdpll->stats.trivial_falsity_detected);
  fprintf (stderr, "Total trivial falsity effective empty: %u\n", qdpll->stats.trivial_falsity_empty_clauses_learned);
  fprintf (stderr, "Total trivial falsity effective unit: %u\n", qdpll->stats.trivial_falsity_unit_clauses_learned);
  fprintf (stderr, "Total trivial falsity effective binary: %u\n", qdpll->stats.trivial_falsity_binary_clauses_learned);
  fprintf (stderr, "Total trivial falsity effective ternary: %u\n", qdpll->stats.trivial_falsity_ternary_clauses_learned);
  fprintf (stderr, "Total trivial falsity propagations: %llu (per try: %f )\n", picosat_propagations (qdpll->trivial_falsity_solver), 
           qdpll->state.trivial_falsity_tried ? (picosat_propagations (qdpll->trivial_falsity_solver) / (float)qdpll->state.trivial_falsity_tried) : 0);
  fprintf (stderr, "Total trivial falsity decisions: %llu (per try: %f max per try: %llu )\n", picosat_decisions (qdpll->trivial_falsity_solver), 
           qdpll->state.trivial_falsity_tried ? (picosat_decisions (qdpll->trivial_falsity_solver) / (float)qdpll->state.trivial_falsity_tried) : 0, 
           qdpll->stats.trivial_falsity_max_decisions_per_call);
  fprintf (stderr, "Total trivial falsity assumptions (per detected): passed %llu ( %f ), failed %llu ( %f ), lits in clause %llu ( %f )\n", qdpll->stats.trivial_falsity_assumptions_passed, 
           qdpll->stats.trivial_falsity_detected ? (qdpll->stats.trivial_falsity_assumptions_passed / (float) qdpll->stats.trivial_falsity_detected) : 0, qdpll->stats.trivial_falsity_assumptions_failed, 
           qdpll->stats.trivial_falsity_detected ? (qdpll->stats.trivial_falsity_assumptions_failed / (float) qdpll->stats.trivial_falsity_detected) : 0, qdpll->stats.trivial_falsity_lits_in_falsity_clause, 
           qdpll->stats.trivial_falsity_detected ? (qdpll->stats.trivial_falsity_lits_in_falsity_clause / (float) qdpll->stats.trivial_falsity_detected) : 0);
  fprintf (stderr, "Total trivial falsity MUS assumptions time: %f\n", qdpll->stats.trivial_falsity_mus_assumptions_time);
  fprintf (stderr, "Total trivial falsity failed assumptions before MUS %llu after MUS %llu ( avg: %f )\n", 
           qdpll->stats.trivial_falsity_assumptions_failed_before_mus, 
           qdpll->stats.trivial_falsity_assumptions_failed_after_mus, 
           qdpll->stats.trivial_falsity_assumptions_failed_before_mus ? 
           (qdpll->stats.trivial_falsity_assumptions_failed_after_mus / 
            (float) qdpll->stats.trivial_falsity_assumptions_failed_before_mus) : 0);

  fprintf (stderr, "Total trivial falsity partial MUS remove existentials calls %llu removed %llu (avg. %f ) reduced-univs %llu (avg. %f ) sat-solver-calls %llu (avg. %f )\n", 
           qdpll->stats.trivial_falsity_remove_inner_existentials_calls, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_removed, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_calls ? 
           (qdpll->stats.trivial_falsity_remove_inner_existentials_removed / 
            (float) qdpll->stats.trivial_falsity_remove_inner_existentials_calls) : 0, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_reduced_univs, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_calls ? 
           (qdpll->stats.trivial_falsity_remove_inner_existentials_reduced_univs / 
            (float) qdpll->stats.trivial_falsity_remove_inner_existentials_calls) : 0, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_sat_calls, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_calls ? 
           (qdpll->stats.trivial_falsity_remove_inner_existentials_sat_calls / 
            (float) qdpll->stats.trivial_falsity_remove_inner_existentials_calls) : 0);

  fprintf (stderr, "Total trivial falsity partial MUS rounds %llu (avg. per call %f ) max %llu\n", 
    qdpll->stats.trivial_falsity_remove_inner_existentials_rounds, 
    qdpll->stats.trivial_falsity_remove_inner_existentials_calls ? 
    (qdpll->stats.trivial_falsity_remove_inner_existentials_rounds / 
     (float) qdpll->stats.trivial_falsity_remove_inner_existentials_calls) : 0, 
           qdpll->stats.trivial_falsity_remove_inner_existentials_max_rounds);

  fprintf (stderr, "Total trivial falsity unit clauses: %llu (avg per detected: %f )\n", 
           qdpll->stats.trivial_falsity_unit_clauses, qdpll->stats.trivial_falsity_detected ? 
           (qdpll->stats.trivial_falsity_unit_clauses / (float) qdpll->stats.trivial_falsity_detected) : 0);
  fprintf (stderr, "Total trivial falsity empty clauses: %llu (avg per detected: %f )\n", 
           qdpll->stats.trivial_falsity_conflicting_clauses, qdpll->stats.trivial_falsity_detected ? 
           (qdpll->stats.trivial_falsity_conflicting_clauses / (float) qdpll->stats.trivial_falsity_detected) : 0);
  fprintf (stderr, "Total trivial falsity deleted clauses: %llu (avg per detected: %f )\n\n", 
           qdpll->stats.trivial_falsity_deleted_clauses, qdpll->stats.trivial_falsity_detected ? 
           (qdpll->stats.trivial_falsity_deleted_clauses / (float) qdpll->stats.trivial_falsity_detected) : 0);


  fprintf (stderr, "Total trivial truth disabled: %s\n", qdpll->state.trivial_truth_disabled ? "yes" : "no");
  fprintf (stderr, "Total trivial truth time: %f (per try: %f )\n", qdpll->state.trivial_truth_time, 
           qdpll->state.trivial_truth_tried ? (qdpll->state.trivial_truth_time / qdpll->state.trivial_truth_tried) : 0);
  fprintf (stderr, "Total trivial truth tried: %d\n", qdpll->state.trivial_truth_tried);
  fprintf (stderr, "Total trivial truth detected: %llu\n", qdpll->stats.trivial_truth_detected);
  fprintf (stderr, "Total trivial truth propagations: %llu (per try: %f )\n", 
	   picosat_propagations (qdpll->trivial_truth_solver), 
           qdpll->state.trivial_truth_tried ? (picosat_propagations (qdpll->trivial_truth_solver) / 
					       (float)qdpll->state.trivial_truth_tried) : 0);
  fprintf (stderr, "Total trivial truth decisions: %llu (per try: %f max per try: %llu )\n", 
	   picosat_decisions (qdpll->trivial_truth_solver), 
           qdpll->state.trivial_truth_tried ? (picosat_decisions (qdpll->trivial_truth_solver) / 
					       (float)qdpll->state.trivial_truth_tried) : 0, 
           qdpll->stats.trivial_truth_max_decisions_per_call);

  fprintf (stderr, "Total trivial truth unit cubes: %llu (avg per detected: %f )\n", 
           qdpll->stats.trivial_truth_unit_cubes, qdpll->stats.trivial_truth_detected ? 
           (qdpll->stats.trivial_truth_unit_cubes / (float) qdpll->stats.trivial_truth_detected) : 0);
  fprintf (stderr, "Total trivial truth empty cubes: %llu (avg per detected: %f )\n", 
           qdpll->stats.trivial_truth_satisfied_cubes, qdpll->stats.trivial_truth_detected ? 
           (qdpll->stats.trivial_truth_satisfied_cubes / (float) qdpll->stats.trivial_truth_detected) : 0);
  fprintf (stderr, "Total trivial truth deleted cubes: %llu (avg per detected: %f )\n\n", 
           qdpll->stats.trivial_truth_deleted_cubes, qdpll->stats.trivial_truth_detected ? 
           (qdpll->stats.trivial_truth_deleted_cubes / (float) qdpll->stats.trivial_truth_detected) : 0);

  fprintf (stderr, "Total dynamic Nenofex calls disabled: %s\n", qdpll->state.dyn_nenofex_disabled ? "yes" : "no");
  fprintf (stderr, "Total dynamic Nenofex calls: %u\n", qdpll->state.dyn_nenofex_calls);
  fprintf (stderr, "Total dynamic Nenofex result sat: %u\n", qdpll->stats.dyn_nenofex_result_sat);
  fprintf (stderr, "Total dynamic Nenofex result unsat: %u\n", qdpll->stats.dyn_nenofex_result_unsat);
  fprintf (stderr, "Total dynamic Nenofex max. result unknown streak: %u\n", qdpll->stats.dyn_nenofex_max_result_unknown_streak);

  unsigned int nenofex_success = 
    qdpll->stats.dyn_nenofex_result_sat + qdpll->stats.dyn_nenofex_result_unsat;
  fprintf (stderr, "Total dynamic Nenofex success dlevels: %llu ( %f per success)\n", 
           qdpll->stats.dyn_nenofex_success_dlevels, nenofex_success ? 
           qdpll->stats.dyn_nenofex_success_dlevels / (float)nenofex_success : 0);

  fprintf (stderr, "Total dynamic Nenofex time: %f ( %f per call)\n", qdpll->state.dyn_nenofex_time, 
           qdpll->state.dyn_nenofex_calls ? qdpll->state.dyn_nenofex_time / qdpll->state.dyn_nenofex_calls : 0);
  fprintf (stderr, "Total dynamic Nenofex unit cubes: %llu (avg per detected: %f )\n", 
           qdpll->stats.dyn_nenofex_unit_cubes, qdpll->stats.dyn_nenofex_result_sat ? 
           (qdpll->stats.dyn_nenofex_unit_cubes / (float) qdpll->stats.dyn_nenofex_result_sat) : 0);
  fprintf (stderr, "Total dynamic Nenofex empty cubes: %llu (avg per detected: %f )\n", 
           qdpll->stats.dyn_nenofex_satisfied_cubes, qdpll->stats.dyn_nenofex_result_sat ? 
           (qdpll->stats.dyn_nenofex_satisfied_cubes / (float) qdpll->stats.dyn_nenofex_result_sat) : 0);
  fprintf (stderr, "Total dynamic Nenofex deleted cubes: %llu (avg per detected: %f )\n", 
           qdpll->stats.dyn_nenofex_deleted_cubes, qdpll->stats.dyn_nenofex_result_sat ? 
           (qdpll->stats.dyn_nenofex_deleted_cubes / (float) qdpll->stats.dyn_nenofex_result_sat) : 0);

  fprintf (stderr, "Total dynamic Nenofex unit clauses: %llu (avg per detected: %f )\n", 
           qdpll->stats.dyn_nenofex_unit_clauses, qdpll->stats.dyn_nenofex_result_unsat ? 
           (qdpll->stats.dyn_nenofex_unit_clauses / (float) qdpll->stats.dyn_nenofex_result_unsat) : 0);
  fprintf (stderr, "Total dynamic Nenofex empty clauses: %llu (avg per detected: %f )\n", 
           qdpll->stats.dyn_nenofex_conflicting_clauses, qdpll->stats.dyn_nenofex_result_unsat ? 
           (qdpll->stats.dyn_nenofex_conflicting_clauses / (float) qdpll->stats.dyn_nenofex_result_unsat) : 0);
  fprintf (stderr, "Total dynamic Nenofex deleted clauses: %llu (avg per detected: %f )\n\n", 
           qdpll->stats.dyn_nenofex_deleted_clauses, qdpll->stats.dyn_nenofex_result_unsat ? 
           (qdpll->stats.dyn_nenofex_deleted_clauses / (float) qdpll->stats.dyn_nenofex_result_unsat) : 0);

  fprintf (stderr, "---------------------------------------\n\n");
#endif

#if COMPUTE_TIMES
  fprintf (stderr, "\n---------------- TIME-STATS ----------------\n");

  fprintf (stderr, "Total solve time: \t%f ( %f ) \n",
           qdpll->time_stats.total_sat_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_sat_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total bcp time: \t%f ( %f )\n",
           qdpll->time_stats.total_bcp_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_bcp_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total s-learn time: \t%f ( %f )\n",
           qdpll->time_stats.total_sol_learn_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_sol_learn_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total c-learn time: \t%f ( %f )\n",
           qdpll->time_stats.total_conf_learn_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_conf_learn_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  qdpll->time_stats.total_learn_time =
    qdpll->time_stats.total_sol_learn_time +
    qdpll->time_stats.total_conf_learn_time;
  fprintf (stderr, "Total learn time: \t%f ( %f )\n",
           qdpll->time_stats.total_learn_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_learn_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total reduce time: \t%f ( %f )\n",
           qdpll->time_stats.total_reduce_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_reduce_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total ireason time: \t%f ( %f )\n",
           qdpll->time_stats.total_ireason_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_ireason_time /
                                               qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "Total greason time: \t%f ( %f )\n",
           qdpll->time_stats.total_greason_time,
           qdpll->time_stats.total_sat_time ? (qdpll->time_stats.
                                               total_greason_time /
                                              qdpll->time_stats.
                                               total_sat_time) : 0);
  fprintf (stderr, "---------------------------------------\n\n");
#endif
}


/* Reset internal solver state, unassign all variables, keep all added clauses
   and learned constraints. */
void
qdpll_reset (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");

  /* Reset limits. */
  qdpll->options.max_dec = 0;
  qdpll->options.max_secs = 0;
  qdpll->options.max_btracks = 0;
  qdpll->options.limit_set = 0;
  qdpll->state.solving_start_time = 0;

  if (qdpll->qdo_assignment_table)
    {
      assert (qdpll->qdo_table_bytes);
      qdpll_free (qdpll->mm, qdpll->qdo_assignment_table, qdpll->qdo_table_bytes);
      qdpll->qdo_table_bytes = 0;
      qdpll->qdo_assignment_table = 0;
    }

  VarID *p, *e;
  for (p = qdpll->qdo_dummy_assigned_vars.start, 
         e = qdpll->qdo_dummy_assigned_vars.top; p < e; p++)
    {
      Var *var = VARID2VARPTR (qdpll->pcnf.vars, *p);
      assert (var->assignment != QDPLL_ASSIGNMENT_UNDEF);
      assert (var->mode != QDPLL_VARMODE_UNDEF);
      assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
      var->assignment = QDPLL_ASSIGNMENT_UNDEF;
      var->mode = QDPLL_VARMODE_UNDEF;
      var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
    }
  QDPLL_RESET_STACK (qdpll->qdo_dummy_assigned_vars);

  qdpll->state.qdo_no_schedule_model_reconstruction = 0;

  qdpll->result = QDPLL_RESULT_UNKNOWN;
  qdpll->result_constraint = 0;
  if (qdpll->assumption_lits_constraint)
    {
      delete_constraint (qdpll, qdpll->assumption_lits_constraint);
      qdpll->assumption_lits_constraint = 0;
    }

  /* Must reset stack of clauses pending to be checked by QBCE. For each
     decision level, we apply QBCE until saturation under the current
     assignment, unless there is a conflict or empty formula detected
     earlier. Must also reset offsets of pairs on working queue. 
     NOTE: we must do this BEFORE rescheduling QBCE in function
     'reset_clean_up_assignments' below. */
  while (!QDPLL_EMPTY_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses))
    {
      QBCENonBlockedWitness pair = 
        QDPLL_POP_STACK (qdpll->qbcp_qbce_maybe_blocked_clauses);
      if (pair.offset.witness_in_witness_list != QDPLL_INVALID_WATCHER_POS)
        qbcp_qbce_reset_offset_in_working_queue (qdpll, pair);
    }

  reset_clean_up_assignments (qdpll);

  QDPLL_RESET_STACK(qdpll->user_given_assumptions); 
  qdpll->state.assumptions_given = 0;
  assert(sizeof_top_level (qdpll) == 0);
  reset_watchers (qdpll);

  /* Reset QBCE related data structures. */

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
  /* When resetting solver, make sure to enable elimination of universal
     literals from learned cubes again, as it may have been disabled dynamically
     in the previous call. */
  qdpll->state.elim_univ_dynamic_disabled = 0;
  qdpll->state.elim_univ_tried = 0;
  qdpll->state.elim_univ_eliminated = 0;
  qdpll->state.univ_vars_cur_collected = 0;
#endif

  qdpll->state.cnt_state_undetermined_after_qbcp = 0;

  /* Enable checks for generalized axioms again. */
  qdpll->state.trivial_falsity_disabled = 0;
  qdpll->state.trivial_truth_disabled = 0;
  qdpll->state.dyn_nenofex_disabled = 0;
}


/* Assign a variable as assumption. A later call of 'qdpll_sat(...)' solves
   the formula under the assumptions specified before. If 'id' is negative
   then variable with ID '-id' will be assigned false, otherwise variable with
   ID 'id' will be assigned true. */
void qdpll_assume (QDPLL * qdpll, LitID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL(qdpll->assumption_lits_constraint || 
                    qdpll->state.assumptions_given || 
                    count_assigned_vars(qdpll) != 0, 
                    "Solver must be in reset state -- call 'qdpll_reset()' before 'qdpll_assume()'!");
  /* Make sure to properly import previosuly added user prefix. See also
     comments at function 'add_aux'. */
  import_user_scopes (qdpll);
  QDPLL_ABORT_QDPLL(!qdpll_is_var_declared (qdpll, LIT2VARID(id)), 
                    "Variable is not declared!");
  QDPLL_PUSH_STACK(qdpll->mm, qdpll->user_given_assumptions, id);
  /* Reschedule blocked clauses found in preprocessing, if any. */
  if ((qdpll->options.qbce_preprocessing || qdpll->options.qbce_inprocessing || 
       !qdpll->options.no_qbce_dynamic) && 
      QDPLL_COUNT_STACK (qdpll->qbcp_qbce_blocked_clauses.start[0]))
    {
      Var *var = LIT2VARPTR(qdpll->pcnf.vars, id); 
      QDPLL_ABORT_QDPLL (var->is_internal, "Unexpected ID of internal variable!");
      if (QDPLL_VAR_EXISTS (var))
        qbcp_qbce_reschedule_from_exists_var (qdpll, var, id);
    }
}


/* Returns a zero-terminated array of LitIDs of variables which can savely be
   assigned as assumptions by function 'qdpll_assume'. The array may contain
   both existential (positive LitIDs) and universal variables (negative
   LitIDs) which are not necessarily from the leftmost quantifier set in the
   prefix.

   NOTE: the caller is responsible to release the memory of the array returned
   by this function. */
LitID * qdpll_get_assumption_candidates (QDPLL * qdpll)
{
  /* Make sure to properly import previosuly added user prefix. See also
     comments at function 'add_aux'. */
  import_user_scopes (qdpll);

  QDPLLDepManGeneric *dmg = qdpll->dm;
  if (!dmg->is_init (dmg))
    {
      set_up_formula (qdpll);
      dmg->init (dmg);
    }

  LitID *cands = dmg->get_candidates (dmg);

  /* In incremental mode: remove internal variables from candidate list. */
  if (qdpll->state.cnt_created_clause_groups > 0 || 
      QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0)
    remove_internals_from_lits (qdpll, cands);

  return cands;
}


/* Returns a zero-terminated array of LitIDs representing those assumptions
   (passed to the solver using 'qdpll_assume()') which were used by the solver to
   determine (un)satisfiability by the most recent call of 'qdpll_sat'.

   NOTE: the caller is responsible to release the memory of the array returned
   by this function. */
LitID * 
qdpll_get_relevant_assumptions (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  QDPLL_ABORT_QDPLL (qdpll->result == QDPLL_RESULT_UNKNOWN, 
                     "Formula is undecided!");
  QDPLL_ABORT_QDPLL (!qdpll->state.assumptions_given, "No assumptions given!");
  QDPLL_ABORT_QDPLL(!qdpll->assumption_lits_constraint, 
                    "Unexpected error: no assumption subset computed!");
  assert (qdpll->result == QDPLL_RESULT_SAT || qdpll->result == QDPLL_RESULT_UNSAT);
  assert (qdpll->assumption_lits_constraint && qdpll->state.assumptions_given);
  QDPLL_ABORT_QDPLL(!(qdpll->assumption_lits_constraint && qdpll->state.assumptions_given), 
                    "Unexpected error: cannot retrieve relevant assumptions.");
  unsigned int size = (qdpll->assumption_lits_constraint->num_lits + 1) * sizeof (LitID);
  /* Do not use internal memory manager here because the user has to free the memory. */
  LitID *rel_assumptions = malloc (size);
  memset (rel_assumptions, 0, size);
  LitID *p, *e, *t;
  for (p = qdpll->assumption_lits_constraint->lits, 
         e = p + qdpll->assumption_lits_constraint->num_lits, t = rel_assumptions; 
       p < e; p++, t++)
    {
      LitID a_lit = *p;
      /* If 'assumption_lits_constraint' is a clause: the formula was found
         unsatisfiable under the assumptions; must return negated value of
         literal in clause, which represents the assumed value. Otherwise, the
         formula was found satisfiable under the assumptions and
         'assumption_lits_constraint' is a cube; we can return the literal */
      *t = qdpll->assumption_lits_constraint->is_cube ? a_lit : -a_lit;
    }
  assert (t == rel_assumptions + qdpll->assumption_lits_constraint->num_lits);
  assert (!*t);

  /* In incremental mode: remove internal variables from relevant assumptions. */
  if (qdpll->assumption_lits_constraint->num_lits && 
      (qdpll->state.cnt_created_clause_groups > 0 || 
       QDPLL_COUNT_STACK(qdpll->state.popped_off_internal_vars) != 0))
    remove_internals_from_lits (qdpll, rel_assumptions);

  return rel_assumptions;
}

/* Reset collected statistics. */
void qdpll_reset_stats (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  qdpll->state.num_backtracks = qdpll->state.num_restarts = 
    qdpll->state.num_decisions = 0;
#if COMPUTE_STATS
  memset (&(qdpll->stats), 0,
          sizeof (qdpll->stats));
#endif
#if COMPUTE_TIMES
  memset (&(qdpll->time_stats), 0,
          sizeof (qdpll->time_stats));
#endif
}

/* Discard all learned constraints and cover sets. */
void qdpll_reset_learned_constraints (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "pointer to solver object is null!");
  /* Discard all learned cubes. */
  check_resize_learnt_constraints_aux (qdpll, &qdpll->pcnf.learnt_cubes, 
                                       UINT_MAX, QDPLL_QTYPE_FORALL);
  /* Discard all learned clauses. */
  check_resize_learnt_constraints_aux (qdpll, &qdpll->pcnf.learnt_clauses, 
                                       UINT_MAX, QDPLL_QTYPE_EXISTS);
  /* Discard all collected cover sets. */
  discard_all_collected_cover_sets (qdpll);
}

/* -------------------- END: PUBLIC FUNCTIONS --------------------*/
