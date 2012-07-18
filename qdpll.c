/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).  
 Copyright 2010, 2011, 2012 Florian Lonsing and Aina Niemetz, Johannes Kepler 
 University, Linz, Austria and Vienna University of Technology, Vienna, Austria.

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
assert_full_prefix_integrity (QDPLL * qdpll)
{
  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  assert (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.first));

  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
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
          Var *var = qdpll->pcnf.vars + v;
          /* NOTE: marks need not be cleared since they are used for empty-formula watcher */
          assert (var->scope == s);
          assert (var->id == v);
          assert (!QDPLL_VAR_ASSIGNED (var) || var->mode == QDPLL_VARMODE_UNIT
                  || var->mode == QDPLL_VARMODE_PURE);
          assert (!QDPLL_VAR_MARKED (var));
          assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
          assert (QDPLL_VAR_HAS_OCCS (var));

          BLitsOcc *bp, *be;
          for (bp = var->neg_occ_clauses.start, be = var->neg_occ_clauses.top;
               bp < be; bp++)
            assert (constraint_has_lit (BLIT_STRIP_PTR (bp->constraint), -v));
          for (bp = var->pos_occ_clauses.start, be = var->pos_occ_clauses.top;
               bp < be; bp++)
            assert (constraint_has_lit (BLIT_STRIP_PTR (bp->constraint), v));
        }
    }
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

static void
assert_full_cnf_integrity_for_clauses (QDPLL * qdpll,
                                       ConstraintList * clause_list)
{
  Constraint *c;
  for (c = clause_list->first; c; c = c->link.next)
    {
      assert (!c->is_cube);
      LitID *p1, *p2, *e, lit1, lit2;
      for (p1 = c->lits, e = p1 + c->num_lits; p1 < e; p1++)
        {
          lit1 = *p1;
          assert (lit1);
          Var *v1 = LIT2VARPTR (qdpll->pcnf.vars, lit1);

          assert (QDPLL_COUNT_STACK (v1->neg_occ_clauses) ==
                  count_occs (-v1->id, &v1->neg_occ_clauses));
          assert (QDPLL_COUNT_STACK (v1->pos_occ_clauses) ==
                  count_occs (v1->id, &v1->pos_occ_clauses));

          if (QDPLL_LIT_NEG (lit1))
            assert (occs_have_constraint (lit1, &v1->neg_occ_clauses, c));
          else
            assert (occs_have_constraint (lit1, &v1->pos_occ_clauses, c));

          /* NOTE: the following assertion will fail if learnt
             clauses contain two complementary universals. */
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
              /* NOTE: this could fail if also units are done */
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
              /* NOTE: this could fail if also units are done */
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
      assert (prev_var->scope->nesting <= pvar->scope->nesting);
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
assert_lits_no_holes (QDPLL * qdpll, LitID * lit_start, LitID * lit_end)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = lit_start, e = lit_end; p < e; p++)
    assert (*p);
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
  assert_peek_taut_lit_irreducible_aux (qdpll, taut_var, lit_stack->start,
                                        lit_stack->top);
  Constraint *antecedent = pivot->antecedent;
  assert (antecedent);
  assert_peek_taut_lit_irreducible_aux (qdpll, taut_var, antecedent->lits,
                                        antecedent->lits +
                                        antecedent->num_lits);
}


/* -------------------- END: ASSERTION-ONLY CODE -------------------- */



/* -------------------- START: TRACING-ONLY CODE -------------------- */

// TODO preamble!!

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
//print_qrp_constraint (QDPLL *qdpll, 
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
//print_bqrp_constraint (QDPLL *qdpll, 
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
//print_qrp_scope (QDPLL *qdpll, Scope *scope)
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
//print_bqrp_scope (QDPLL *qdpll, Scope *scope)
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
    return 0;
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


/* NOTE: could also set priority outside. */
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
  assert (QDPLL_VAR_HAS_OCCS (var));
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
   NOTE: destroys heap condition! 
*/
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


/* TODO: use watchers as in 'is_clause_satisfied'. */
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
      if (is_clause_empty (qdpll, c))
        return 1;
    }
  for (c = qdpll->pcnf.learnt_clauses.first; c; c = c->link.next)
    {
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
      if (!is_clause_satisfied (qdpll, c))
        return 0;
    }
  /* NOTE: checking learnt clauses is actually not needed since they
     are all implied by original clauses. We only check that here. */
  for (c = qdpll->pcnf.learnt_clauses.first; c; c = c->link.next)
    {
      if (!is_clause_satisfied (qdpll, c)
          && (qdpll->options.no_spure_literals
              || !has_constraint_spurious_pure_lit (qdpll, c)))
        return 0;
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
  //#ifndef NDEBUG
  //VarID old_list_offset = QDPLL_COUNT_STACK (*notify_list);
  //#endif
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
  assert (is_constraint_empty_watcher (qdpll, watched_clause));
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

   TODO: optimize check for satisfied/empty clauses.

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
              assert (is_clause_satisfied
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
              assert (is_clause_satisfied
                      (qdpll,
                       BLIT_STRIP_PTR (v->pos_occ_clauses.start[0].
                                       constraint)));
              occs = &(v->pos_occ_clauses);
              next_occs = &(v->pos_occ_cubes);
            }
        }

#ifndef NDEBUG
      LitID *old_top = notify_list->top;
#endif
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
                push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_TRUE,
                                        QDPLL_VARMODE_PURE);
              else
                push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_FALSE,
                                        QDPLL_VARMODE_PURE);
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
                push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_FALSE,
                                        QDPLL_VARMODE_PURE);
              else
                push_assigned_variable (qdpll, v, QDPLL_ASSIGNMENT_TRUE,
                                        QDPLL_VARMODE_PURE);
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
  if (!c->learnt)
    {
      assert (!c->is_cube);
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

/* NOTE/TODO: this function turned out to be quite superfluous... */
static Constraint *
handle_detected_unit_constraint (QDPLL * qdpll, LitID lit, Var * var,
                                 Constraint * constraint)
{
  assert (!QDPLL_VAR_ASSIGNED (var));
  assert (!QDPLL_VAR_MARKED_PROPAGATED (var));

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
      if (constraint->is_cube)
        {
          qdpll->stats.total_unit_lcubes++;
        }
      else
        {
          qdpll->stats.total_unit_lclauses++;
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

#if 0
static Clause *
NEW_update_literal_watchers (QDPLL * qdpll, Var * propagated_var,
                             Clause * clause)
{

}
#endif

/* Called after watcher became false. Try to set up watcher invariant by 
   finding new pair of watched literals. Returns null if conflict occurred, 
   otherwise sentinel for entry deletion. Detected unit literals will be pushed immediately.
*/
static Constraint *
update_literal_watchers (QDPLL * qdpll, Var * propagated_var,
                         BLitsOcc * blit_ptr)
{
  /* NOTE: need the 'blit_ptr' only for updating the blocking literal
     if the constraint is disabled. */
  BLitsOcc blit = *blit_ptr;
  Constraint *clause = BLIT_STRIP_PTR (blit.constraint);
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

  /* NOTE: for update of left watcher: could also update right watcher by default... 
     implementation could be simpler then but what about performance? 
     Update of right watcher is often redundant in these situations! */

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



/* NOTE: almost same code as for updating watchers, could we re-use? */
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
  Var *vars = qdpll->pcnf.vars;
  const int is_cube = c->is_cube;

  //REMARK: could also use this code pattern for watcher update,
  //which is MUCH cleaner BUT also possibly wastes work since we
  //always search full lits from end to start.  
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
        assert (c->learnt);
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


/* Initialize literal watchers to two rightmost literals in clause.
   NOTE: because we interpret enqueued units/pure literals as active
   immediately, the watchers can be false as well. These situations are
   handled during watcher update then.  
*/
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


/* Remove scopes which contain no variable. 
   Typically called after no-occ variables have been eliminated.
   Runtime is worst-case quadratic in the number of scopes.
*/
static void
cleanup_empty_scopes (QDPLL * qdpll)
{
  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;

      assert (s->nesting != QDPLL_DEFAULT_SCOPE_NESTING
              || QDPLL_SCOPE_EXISTS (s));

      /* Should keep one outermost existential scope as default scope. */
      if (!QDPLL_COUNT_STACK (s->vars)
          && s->nesting != QDPLL_DEFAULT_SCOPE_NESTING)
        {                       /* Unlink and delete scope. */
          UNLINK (qdpll->pcnf.scopes, s, link);
          delete_scope (qdpll, s);
          /* Save next scope 'n' for continuing in next loop iteration. */
          s = n;
          for (; n; n = n->link.next)
            n->nesting--;
          n = s;
        }
    }
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


/* Remove variables without occurrences. This disturbs variable ordering in scopes. */
static void
cleanup_no_occ_variables (QDPLL * qdpll)
{
  Var *vars = qdpll->pcnf.vars;

  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      VarIDStack *scope_vars = &s->vars;
      VarID *p, *end, *last;
      for (p = scope_vars->start, end = scope_vars->top, last = end - 1;
           p < end; p++)
        {
          assert (*p > 0);
          Var *v = VARID2VARPTR (vars, *p);
          if (!QDPLL_VAR_HAS_OCCS (v))
            {
              /* Variable must not be on priority queue. */
              assert (v->priority_pos == QDPLL_INVALID_PQUEUE_POS);
              reset_variable (qdpll, v);
              *p-- = *last--;
              end--;
              scope_vars->top--;
            }
        }
    }
}


/* Maintain prefix properties.
   Should be called before solving starts.
   This matters mostly for the dependency manager, not for the solver itself.
   Runtime is worst-case quadratic in the number of scopes.
*/
static void
merge_adjacent_same_type_scopes (QDPLL * qdpll)
{
  QDPLLMemMan *mm = qdpll->mm;

  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
      assert (s->nesting == QDPLL_DEFAULT_SCOPE_NESTING
              || QDPLL_COUNT_STACK (s->vars));
      assert (!n || QDPLL_COUNT_STACK (n->vars));

      if (n && s->type == n->type)
        {                       /* Adjacent scopes have same type -> merge. */
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

          for (n = s->link.next; n; n = n->link.next)
            n->nesting--;
          n = s;
        }
    }
}


/* Cleanup formula. */
void
clean_up_formula (QDPLL * qdpll)
{
  cleanup_no_occ_variables (qdpll);
  cleanup_empty_scopes (qdpll);
  merge_adjacent_same_type_scopes (qdpll);
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
}


static QDPLLSolverState
set_up_watchers (QDPLL * qdpll)
{
  assert (qdpll->state.decision_level == 0);
  /* Handle empty formula. */
  if (qdpll->pcnf.clauses.cnt == 0)
    return QDPLL_SOLVER_STATE_SAT;
  if (!qdpll->options.no_pure_literals)
    init_clause_watchers (qdpll);
  QDPLLSolverState state = init_literal_watchers (qdpll);
  return state;
}


/* Clean up formula and do initialization tasks:
   Remove no-occ variables and empty scopes, 
   merge scopes of same type into one scope.
*/
static void
set_up_formula (QDPLL * qdpll)
{
  clean_up_formula (qdpll);
}


/* Set variable ID and scope and add to scope. */
static void
declare_and_init_variable (QDPLL * qdpll, Scope * scope, VarID id)
{
  assert (id > 0);
  assert (id < qdpll->pcnf.size_vars);

  QDPLLMemMan *mm = qdpll->mm;
  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);

  qdpll->pcnf.used_vars++;

  /* Init variable */
  assert (!var->id);
  var->id = id;
  assert (!var->scope);
  var->scope = scope;
  assert (!var->priority_pos);
  var->priority_pos = QDPLL_INVALID_PQUEUE_POS;
  assert (!var->priority);
  var->priority = 1;
  assert (!var->decision_level);
  var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
  assert (!var->trail_pos);
  var->trail_pos = QDPLL_INVALID_TRAIL_POS;

  assert (!QDPLL_VAR_HAS_POS_OCCS (var));
  assert (!QDPLL_VAR_HAS_NEG_OCCS (var));
  assert (!QDPLL_VAR_HAS_POS_OCC_CUBES (var));
  assert (!QDPLL_VAR_HAS_NEG_OCC_CUBES (var));

  /* Add to scope */
  QDPLL_PUSH_STACK (mm, scope->vars, id);

  /* Inform DepMan that new variable has been declared and initialized. */
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  dm->notify_init_variable (dm, id);

  if (id > qdpll->pcnf.max_declared_var_id)
    qdpll->pcnf.max_declared_var_id = id;
}


static int
compare_lits_by_variable_nesting (QDPLL * qdpll, int is_cube, LitID lit1,
                                  LitID lit2)
{
  Var *vars = qdpll->pcnf.vars;
  VarID var_id1 = LIT2VARID (lit1);
  VarID var_id2 = LIT2VARID (lit2);
  Var *var1 = VARID2VARPTR (vars, var_id1);
  Var *var2 = VARID2VARPTR (vars, var_id2);

  unsigned int nesting1 = var1->scope->nesting;
  unsigned int nesting2 = var2->scope->nesting;

  if (nesting1 < nesting2)
    return -1;
  else if (nesting1 > nesting2)
    return 1;
  else
    {
      if (var_id1 < var_id2)
        return -1;
      else if (var_id1 > var_id2)
        return 1;
      else
        return 0;
    }
}


static int
compare_lits_by_variable_nesting_ignore_ids (QDPLL * qdpll, int is_cube,
                                             LitID lit1, LitID lit2)
{
  Var *vars = qdpll->pcnf.vars;
  VarID var_id1 = LIT2VARID (lit1);
  VarID var_id2 = LIT2VARID (lit2);
  Var *var1 = VARID2VARPTR (vars, var_id1);
  Var *var2 = VARID2VARPTR (vars, var_id2);

  unsigned int nesting1 = var1->scope->nesting;
  unsigned int nesting2 = var2->scope->nesting;

  if (nesting1 < nesting2)
    return -1;
  else if (nesting1 > nesting2)
    return 1;
  else
    return 0;
}


static void
unmark_clause_variables (QDPLL * qdpll, Constraint * clause)
{
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *end, lit;
  for (p = clause->lits, end = p + clause->num_lits; p < end; p++)
    {                           /* Unmark variables */
      lit = *p;
      QDPLL_VAR_UNMARK (LIT2VARPTR (vars, lit));
    }
}


/* Apply simple existential/universal reduction. */
static void
top_level_reduce_constraint (QDPLL * qdpll, Constraint * c,
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
      if (v->scope->type != type)
        c->num_lits--;
      else
        break;
    }

  assert (c->num_lits == 0 ||
          LIT2VARPTR (vars, c->lits[c->num_lits - 1])->scope->type == type);
}



/* Check clause for multiple, complementary literals and universal-reduction.
   Returns 'NULL' if clause is not tautological, 
   otherwise returns pointer to tautological clause. 
*/
static Constraint *
cleanup_clause (QDPLL * qdpll, Constraint * clause)
{
  assert (!clause->is_cube);
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *end, *last, lit;
  for (p = clause->lits, end = p + clause->num_lits, last = end - 1;
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
        {                       /* Clause is tautological */
          unmark_clause_variables (qdpll, clause);
          return clause;
        }
      else
        {                       /* Clause contains multiple literals */
          assert ((QDPLL_VAR_POS_MARKED (var) && lit > 0) ||
                  (QDPLL_VAR_NEG_MARKED (var) && lit < 0));
          *p-- = *last;
          /* Clean old slot of moved literal. */
          *last-- = 0;
          end--;
          clause->num_lits--;
        }
    }

  unmark_clause_variables (qdpll, clause);
  QDPLL_SORT (qdpll, int, compare_lits_by_variable_nesting, clause->lits,
              clause->num_lits, 0);
  /* Apply universal reduction. */
  top_level_reduce_constraint (qdpll, clause, QDPLL_QTYPE_EXISTS);

  return 0;
}


static void increase_var_activity (QDPLL * qdpll, Var * var);


/* Push clause on clause stack, update occ_lists */
static void
import_clause (QDPLL * qdpll, Constraint * clause)
{
  assert (!clause->is_cube);
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LINK_LAST (qdpll->pcnf.clauses, clause, link);
  assert (qdpll->pcnf.clauses.cnt ==
          count_constraints (&(qdpll->pcnf.clauses)));
  LitID *p, *end;
  for (p = clause->lits, end = p + clause->num_lits; p < end; p++)
    {
      LitID lit = *p;
      assert ((VarID) LIT2VARID (lit) < qdpll->pcnf.size_vars);
      Var *var = LIT2VARPTR (vars, lit);
      /* FIX: Increase variable priority. */
      increase_var_activity (qdpll, var);
      /* Need not mark ptr in blit here. */
      BLitsOcc blit = { lit, clause };
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
  result->dep_init_level = qdpll->num_deps_init;
  result->num_lits = num_lits;
  result->rwatcher_pos = result->lwatcher_pos = QDPLL_INVALID_WATCHER_POS;
  return result;
}


static void
delete_constraint (QDPLL * qdpll, Constraint * constraint)
{
  QDPLLMemMan *mm = qdpll->mm;
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

  if (qdpll->state.scope_opened)
    {                           /* Import scope's variables */
      Scope *scope = qdpll->pcnf.scopes.last;

      /* Must not add to default scope */
      assert (scope->nesting > QDPLL_DEFAULT_SCOPE_NESTING);

      while (sp < se)
        {
          id = *sp++;
          assert (id != 0);
          if (id < 0)
            return "negative variable ID in scope!";
          qdpll_adjust_vars (qdpll, id);
          Var *vars = qdpll->pcnf.vars;
          if (vars[id].id != 0)
            return "variable already quantified!";
          declare_and_init_variable (qdpll, scope, id);
        }

      if (qdpll->options.trace)
        qdpll->trace_scope (scope);

      qdpll->state.scope_opened = 0;
    }
  else
    {
      /* Import clause's literals */
      /* TODO OPTIMIZATION: now we traverse aux. stack and copy 
         literals to newly allocated clause. Then we cleanup
         clause. Altogether we visit all literals three times, i.e. when
         reading input, when copying to clause and when cleaning
         clause. It should be easy to get rid of one visit, at least! */
      unsigned int num_lits = QDPLL_COUNT_STACK (*add_stack);
      Constraint *clause = create_constraint (qdpll, num_lits, 0);

      /* First, add lits to clause, do NOT yet update occ-stacks. 
         NOTE: if clause is redundant, then might get vars which have no occs
       */
      LitID *p = clause->lits;
      while (sp < se)
        {
          id = *sp++;
          assert (id != 0);
          VarID var_id = LIT2VARID (id);
          qdpll_adjust_vars (qdpll, var_id);
          Var *var = qdpll->pcnf.vars + var_id;

          if (var->id == 0)
            {                   /* Declare var; (Q)DIMACS backward compatibility */
              Scope *scope = qdpll->pcnf.scopes.first;
              assert (QDPLL_SCOPE_EXISTS (scope));
              assert (scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
              declare_and_init_variable (qdpll, scope, var_id);
            }
          *p++ = id;            /* Add lits to clause */
        }

      /* Next, sort and clean up clause, then update occ-stacks */
      if (!cleanup_clause (qdpll, clause))
        {
          import_clause (qdpll, clause);
          if (qdpll->options.trace)
            /* Print all literals - even if clause has been reduced previously
               (else an additional reduction step must be introduced). */
            qdpll->trace_constraint (clause->id,
                                     clause->lits, clause->size_lits, 0, 0);
        }
      else                      /* Clause is tautological -> delete */
        delete_constraint (qdpll, clause);
    }

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
push_assigned_variable (QDPLL * qdpll, Var * var, QDPLLAssignment assignment,
                        QDPLLVarMode mode)
{
  assert (mode > 0 && mode <= 4);
  assert (mode != QDPLL_VARMODE_UNDEF);
  assert (assignment != QDPLL_ASSIGNMENT_UNDEF);
  assert (var->assignment == QDPLL_ASSIGNMENT_UNDEF);
  assert (var->mode == QDPLL_VARMODE_UNDEF);
  assert (!QDPLL_VAR_ASSIGNED (var));
  assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
  assert (var->decision_level == QDPLL_INVALID_DECISION_LEVEL);

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

  assert (!(QDPLL_SCOPE_EXISTS (var->scope) && mode == QDPLL_VARMODE_UNIT)
          || (var->antecedent && !var->antecedent->is_cube));
  assert (!(var->antecedent && !var->antecedent->is_cube)
          || (QDPLL_SCOPE_EXISTS (var->scope) && mode == QDPLL_VARMODE_UNIT));
  assert (!(QDPLL_SCOPE_FORALL (var->scope) && mode == QDPLL_VARMODE_UNIT)
          || (var->antecedent && var->antecedent->is_cube));
  assert (!(var->antecedent && var->antecedent->is_cube)
          || (QDPLL_SCOPE_FORALL (var->scope) && mode == QDPLL_VARMODE_UNIT));
  assert (!var->antecedent || var->antecedent->is_reason);

  if (mode < 3)
    {
      assert (mode == QDPLL_VARMODE_UNIT || mode == QDPLL_VARMODE_PURE);
      var->decision_level = qdpll->state.decision_level;
    }
  else
    {
      assert (mode == QDPLL_VARMODE_LBRANCH || mode == QDPLL_VARMODE_RBRANCH);
      assert ((unsigned int) QDPLL_COUNT_STACK (qdpll->dec_vars) ==
              qdpll->state.decision_level);
      var->decision_level = ++qdpll->state.decision_level;
      QDPLL_PUSH_STACK (qdpll->mm, qdpll->dec_vars, var->id);
      assert (qdpll->dec_vars.start[qdpll->state.decision_level - 1] ==
              var->id);
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
                                     int check_prop)
{
  assert (!check_prop);
  if (QDPLL_VAR_ASSIGNED (var))
    return 0;

  LitID lit = occ_clauses == &(var->neg_occ_clauses) ? -var->id : var->id;

  BLitsOcc *bp, *be;
  for (bp = occ_clauses->start, be = occ_clauses->top; bp < be; bp++)
    {
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
  if (c->dep_init_level < qdpll->num_deps_init)
    qdpll->stats.total_mtf_dirty_deps_constraints++;
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
  qdpll->options.var_act_inc *= qdpll->var_act_decay;
}


static void
increase_var_activity (QDPLL * qdpll, Var * var)
{
  assert (1 + var->scope->nesting);
  var->priority +=
    (qdpll->options.var_act_inc *
     (1 + (qdpll->options.var_act_bias * (double) var->scope->nesting) / 10));
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
      qdpll->options.var_act_inc *= 1e-100;
    }

  if (var->priority_pos != QDPLL_INVALID_PQUEUE_POS)
    var_pqueue_increase_key (qdpll, var->id);
}


static void
cover_by_clauses_collect_lits_sorted (QDPLL * qdpll, QDPLLMemMan * mm,
                                      LitIDStack * lit_stack);
static void
cover_by_clauses_collect_lit (QDPLL * qdpll, QDPLLMemMan * mm,
                              LitIDStack * lit_stack, Var * var, LitID lit);

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
      assert (!(LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var)));
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
                              LitIDStack * lit_stack, Var * var, LitID lit)
{
  assert (var);
  assert (lit);
  assert (qdpll->pcnf.scopes.last != var->scope);
  assert ((QDPLL_LIT_NEG (lit) && QDPLL_VAR_ASSIGNED_FALSE (var)) ||
          (QDPLL_LIT_POS (lit) && QDPLL_VAR_ASSIGNED_TRUE (var)));
  assert (!LEARN_VAR_MARKED (var));
  if (QDPLL_LIT_POS (lit))
    LEARN_VAR_POS_MARK (var);
  else
    LEARN_VAR_NEG_MARK (var);
  LitIDStack *cover_lits = &(var->scope->cover_lits);
  QDPLL_PUSH_STACK (mm, *cover_lits, lit);
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
  /* Re-collect all marked literals by traversing all scopes from
     outer- to innermost. Marked literals can then be collected in scope
     order, thus explicit sorting can be avoided. */
  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      LitID *p, *e, lit;
      if (s == qdpll->pcnf.scopes.last)
        {
          assert (QDPLL_SCOPE_EXISTS (s));
          assert (QDPLL_EMPTY_STACK (s->cover_lits));
#ifndef NDEBUG
          do
            {
              VarID *p, *e;
              for (p = s->vars.start, e = s->vars.top; p < e; p++)
                {
                  Var *v = VARID2VARPTR (vars, *p);
                  assert (!LEARN_VAR_MARKED (v));
                }
            }
          while (0);
#endif
          /* No literal is marked in innermost scope, since that
             literals would be immediately removed by type-reduce. */
          break;
        }

      for (p = s->cover_lits.start, e = s->cover_lits.top; p < e; p++)
        {
          Var *v = LIT2VARPTR (vars, *p);
#ifndef NDEBUG
          assert (LEARN_VAR_MARKED (v));
          assert ((QDPLL_VAR_ASSIGNED_TRUE (v) && LEARN_VAR_POS_MARKED (v)) ||
                  (QDPLL_VAR_ASSIGNED_FALSE (v) && LEARN_VAR_NEG_MARKED (v)));
#endif
          lit = *p;
          update_stop_crit_data (qdpll, vars, lit, QDPLL_QTYPE_FORALL);
          QDPLL_PUSH_STACK (mm, *lit_stack, lit);
        }
      QDPLL_RESET_STACK (s->cover_lits);
    }
#ifndef NDEBUG
  assert_lits_sorted (qdpll, lit_stack->start, lit_stack->top);
#endif
}


/* Generate cover in linear time, i.e. traverse original clauses exactly once. 
   Maybe this is worse than generating covers from assigned vars. */
static int
cover_by_clauses (QDPLL * qdpll, LitIDStack * lit_stack,
                  LitIDStack * lit_stack_tmp)
{
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  assert (QDPLL_COUNT_STACK (*lit_stack) == 0);
#ifndef NDEBUG
  do
    {
      Scope *s;
      for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
        assert (QDPLL_EMPTY_STACK (s->cover_lits));
    }
  while (0);
#endif
#if COMPUTE_STATS
  qdpll->stats.total_sdcl_covers++;
  /* Abusing stack for stats-computation. */
  assert (QDPLL_COUNT_STACK (qdpll->wreason_a) == 0);
#endif
  const Scope *last_scope = qdpll->pcnf.scopes.last;
  assert (QDPLL_SCOPE_EXISTS (last_scope));
  Constraint *c;

  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      assert (!c->learnt);
      assert (!c->is_cube);
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
              /* Skip clauses that are already covered by collected
                 literal or covered by innermost existential variable ->
                 never collect such literals since they will be reduced
                 anyway. */
              if (LEARN_VAR_MARKED (lit_var) || lit_var->scope == last_scope)
                {
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
        cover_by_clauses_collect_lit (qdpll, mm, lit_stack, max_e_true_var,
                                      max_e_true_lit);
      else
        cover_by_clauses_collect_lit (qdpll, mm, lit_stack, min_a_true_var,
                                      min_a_true_lit);
    SKIP:;
    }

#if COMPUTE_STATS
  Var **p, **e;
  for (p = qdpll->wreason_a.start, e = qdpll->wreason_a.top; p < e; p++)
    {
      assert ((*p)->mark_stats_type_reduce_lits);
      (*p)->mark_stats_type_reduce_lits = 0;
    }
  qdpll->stats.total_type_reduce_by_deps +=
    QDPLL_COUNT_STACK (qdpll->wreason_a);
  QDPLL_RESET_STACK (qdpll->wreason_a);
#endif

  cover_by_clauses_collect_lits_sorted (qdpll, mm, lit_stack);

  /* for resolution proof extraction we need to know, if any lits from the 
     innermost scope where reduced */
  return QDPLL_COUNT_STACK (*lit_stack_tmp);
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
  if ((res_cons))
    {
      assert (type != QDPLL_QTYPE_EXISTS || (res_cons && !res_cons->is_cube));
      assert (type == QDPLL_QTYPE_EXISTS || (res_cons && res_cons->is_cube));
      assert (res_cons->dep_init_level <= qdpll->num_deps_init);

      /* An original clause was found as initial reason. */
      if (res_cons->num_lits < res_cons->size_lits)
        {
          assert (!qdpll->orig_wreason);
          qdpll->orig_wreason = res_cons;
        }

      learnt_constraint_mtf (qdpll, res_cons);
      /* Push and mark literals of reason clause onto 'lit-stack',
         which is the working reason. */
      p = res_cons->lits;
      e = p + res_cons->num_lits;
      /* Can happen that input formula contains clause with universal
         literals only. Initial reason will then be empty. */
      assert (qdpll->state.decision_level == 0 || p < e);
      for (; p < e; p++)
        {
          lit = *p;
          var = LIT2VARPTR (vars, lit);
          /* Increase activity of variable in conflicting clause. */
          increase_var_activity (qdpll, var);
          assert (!LEARN_VAR_MARKED (var));
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

      /* Find cover set. */
      nlits = QDPLL_COUNT_STACK (**lit_stack);
      if (cover_by_clauses (qdpll, stack, &tmp) && qdpll->options.trace)
        qdpll->trace_full_cover_set (qdpll,
                                     (cid = ++(qdpll->cur_constraint_id)),
                                     tmp.start, QDPLL_COUNT_STACK (tmp),
                                     (*lit_stack)->start,
                                     QDPLL_COUNT_STACK (**lit_stack));

      if (qdpll->options.trace && nlits - (QDPLL_COUNT_STACK (**lit_stack)))
        qdpll->trace_constraint (++(qdpll->cur_constraint_id),
                                 (*lit_stack)->start,
                                 QDPLL_COUNT_STACK (**lit_stack), cid, 0);

      nlits = QDPLL_COUNT_STACK (**lit_stack);
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

  /* BUG FIX: we do NOT force to resolve out top-level literals. Just
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
          increase_var_activity (qdpll, var);
        }
      else if (LEARN_VAR_POS_MARKED (var))
        {
          /* EXPECTED DEAD-CODE. Otherwise would get constraints with
             complementary literals. */
          abort ();
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
          increase_var_activity (qdpll, var);
        }
      else if (LEARN_VAR_NEG_MARKED (var))
        {
          /* EXPECTED DEAD-CODE. Otherwise would get constraints with
             complementary literals. */
          abort ();
        }
    }
}


/* Perform q-resolution.*/
static ConstraintID
resolve_and_reduce (QDPLL * qdpll, ConstraintID ant1_id,
                    LitIDStack ** lit_stack, LitIDStack ** lit_stack_tmp,
                    Var * var, const QDPLLQuantifierType type)
{

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
  assert_lits_no_holes (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_stop_crit_data (qdpll, *lit_stack, type);
#endif
  if (qdpll->options.verbosity > 1)
    {
      const char prefix = type == QDPLL_QTYPE_EXISTS ? 'C' : 'S';
      const char *type_str = type == QDPLL_QTYPE_EXISTS ? "clause" : "cube";
      fprintf (stderr, "\n%cDCL: pivot variable: %d\n", prefix, var->id);
      fprintf (stderr, "%cDCL: working %s: ", prefix, type_str);
      if (!qdpll->orig_wreason)
        print_lits (qdpll, (*lit_stack)->start,
                    QDPLL_COUNT_STACK (**lit_stack), 0);
      else
        print_lits (qdpll, qdpll->orig_wreason->lits,
                    qdpll->orig_wreason->num_lits,
                    qdpll->orig_wreason->size_lits);

      fprintf (stderr, "%cDCL: antecedent: ", prefix);
      if (!qdpll->orig_antecedent)
        print_lits (qdpll, other_lits_start,
                    other_lits_end - other_lits_start, 0);
      else
        print_lits (qdpll, qdpll->orig_antecedent->lits,
                    qdpll->orig_antecedent->num_lits,
                    qdpll->orig_antecedent->size_lits);
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
      if (compare_lits_by_variable_nesting_ignore_ids
          (qdpll, type == QDPLL_QTYPE_FORALL, lit1, lit2) <= 0)
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
  assert_lits_no_holes (qdpll, (*lit_stack)->start, (*lit_stack)->top);
#endif

  qdpll->dm->reduce_lits (qdpll->dm, lit_stack, lit_stack_tmp, type, 1);

  if (qdpll->options.trace)
    qdpll->trace_constraint (res_id, (*lit_stack)->start,
                             QDPLL_COUNT_STACK (**lit_stack), ant1_id,
                             var->antecedent->id);

  qdpll->orig_wreason = qdpll->orig_antecedent = 0;

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
#ifndef NDEBUG
#if 0
          assert_peek_taut_lit_irreducible (qdpll, lit_stack, var, lit_var);
#endif
#endif
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

  if ((blocking = peek_tautology (qdpll, lit_stack, pivot)))
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

  if (QDPLL_EMPTY_STACK (**lit_stack))
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
  assert (!working_clause_is_tautologous (qdpll, *lit_stack, type));
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

      /* An original clause was found as antecedent */
      if (var->antecedent->num_lits < var->antecedent->size_lits)
        {
          assert (!qdpll->orig_antecedent);
          qdpll->orig_antecedent = var->antecedent;
        }

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


static unsigned int
generate_and_add_reason (QDPLL * qdpll, const QDPLLQuantifierType type)
{
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LitIDStack *lit_stack = &(qdpll->add_stack);
  LitIDStack *lit_stack_tmp = &(qdpll->add_stack_tmp);
  LitID *p;

  assert (qdpll->cnt_hi_dl_type_lits == 0);
  assert (qdpll->hi_dl_type_var == 0);
  assert (qdpll->hi_type_dl == 0);
  assert (QDPLL_EMPTY_STACK (qdpll->smaller_type_lits));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_a));
  assert (QDPLL_EMPTY_STACK (qdpll->wreason_e));
  assert (QDPLL_COUNT_STACK (*lit_stack) == 0);
  assert (QDPLL_COUNT_STACK (*lit_stack_tmp) == 0);
  assert (!qdpll->orig_wreason);
  assert (!qdpll->orig_antecedent);
#ifndef NDEBUG
#if QDPLL_ASSERT_LEARN_VARS_UNMARKED
  assert_learn_vars_unmarked (qdpll);
#endif
#endif

  get_initial_reason (qdpll, &lit_stack, &lit_stack_tmp, type);
  assert (qdpll->state.decision_level == 0 || type == QDPLL_QTYPE_FORALL ||
          QDPLL_COUNT_STACK (*lit_stack) != 0);

#ifndef NDEBUG
  if (QDPLL_COUNT_STACK (*lit_stack) > 0)
    assert_stop_crit_data (qdpll, lit_stack, type);
#endif

  if (qdpll->options.verbosity > 1)
    {
      if (type == QDPLL_QTYPE_EXISTS)
        fprintf (stderr, "CDCL: conflicting clause (%u): ",
                 qdpll->result_constraint->id);
      else
        {
          fprintf (stderr, "SDCL: initial cube");
          if (qdpll->options.trace)
            fprintf (stderr, " (%u)", qdpll->cur_constraint_id);
          fprintf (stderr, ": ");
        }

      if (!qdpll->orig_wreason)
        print_lits (qdpll, lit_stack->start, QDPLL_COUNT_STACK (*lit_stack),
                    0);
      else
        print_lits (qdpll, qdpll->orig_wreason->lits,
                    qdpll->orig_wreason->num_lits,
                    qdpll->orig_wreason->size_lits);
    }

  /* Now lit-stack contains literals of either
     conflicting clause or cover-set/satisfied cube. */

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

  /* Unmark variables by traversing lit-stack, i.e. final working
     reason. */
  Var *var;
  LitID lit;
  for (p = lit_stack->start; p < lit_stack->top; p++)
    {
      lit = *p;
      var = LIT2VARPTR (vars, lit);
      assert (!success
              || !(LEARN_VAR_POS_MARKED (var) && LEARN_VAR_NEG_MARKED (var)));
      LEARN_VAR_UNMARK (var);
    }

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
          qdpll->stats.total_learnt_cubes_size +=
            QDPLL_COUNT_STACK (*lit_stack);
        }
      else
        {
          qdpll->stats.total_learnt_clauses++;
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
  /* NOTE: we call learning procedure even if solver is at
     top-level. This is necessary to allow logging of resolution
     proofs. */
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
  /* NOTE: we call learning procedure even if solver is at
     top-level. This is necessary to allow logging of resolution
     proofs. */
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
    }

  var->mode = QDPLL_VARMODE_UNDEF;
  var->assignment = QDPLL_ASSIGNMENT_UNDEF;
  var->decision_level = QDPLL_INVALID_DECISION_LEVEL;
  var->trail_pos = QDPLL_INVALID_TRAIL_POS;
  if (var->antecedent)
    {
      assert (var->antecedent->is_reason);
      var->antecedent->is_reason = 0;
      var->antecedent = 0;
    }

  /* BUG FIX: must put candidate variables back on pqueue. */
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

#if COMPUTE_STATS
#if COMPUTE_STATS_BTLEVELS_SIZE
  unsigned int target_level = backtrack_level - 1;
  unsigned int i;
  if (target_level <= 0)
    qdpll->stats.btlevels[0]++;
  for (i = 1; i < COMPUTE_STATS_BTLEVELS_SIZE - 1; i++)
    {
      if (target_level <= (1U << (i - 1)))
        qdpll->stats.btlevels[i]++;
    }
  /* Last entry sums up all backtrack cases. */
  qdpll->stats.btlevels[COMPUTE_STATS_BTLEVELS_SIZE - 1]++;
  assert (qdpll->state.num_backtracks ==
          qdpll->stats.btlevels[COMPUTE_STATS_BTLEVELS_SIZE - 1]);
  /* Linear stats partition: */
  if (target_level <= 0)
    qdpll->stats.btlevels_lin[0]++;
  for (i = 1; i < COMPUTE_STATS_BTLEVELS_SIZE - 1; i++)
    {
      if (target_level <= (5 * i))
        qdpll->stats.btlevels_lin[i]++;

    }
  /* Last entry sums up all backtrack cases. */
  qdpll->stats.btlevels_lin[COMPUTE_STATS_BTLEVELS_SIZE - 1]++;
  assert (qdpll->state.num_backtracks ==
          qdpll->stats.btlevels_lin[COMPUTE_STATS_BTLEVELS_SIZE - 1]);
#endif
#endif

  VarID *p, *e, *old_bcp_ptr;
  Var *vars = qdpll->pcnf.vars;
  old_bcp_ptr = qdpll->old_bcp_ptr;

  /* NOTE: must start at 'top', not at 'bcp_ptr' since we could stop bcp early. */
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
        backtrack_undo_assignment (qdpll, assigned_var,
                                   ((p < old_bcp_ptr)));
      else
        {
          assert (var_decision_level < backtrack_level);
          break;
        }
    }

  qdpll->state.decision_level = backtrack_level - 1;
  assert (qdpll->state.decision_level != QDPLL_INVALID_DECISION_LEVEL);
  qdpll->old_bcp_ptr = qdpll->bcp_ptr = qdpll->assigned_vars_top = p + 1;
}


static Var *
select_decision_variable (QDPLL * qdpll)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  Var *decision_var, *candidate_var, *vars = qdpll->pcnf.vars;
  VarID candidate, decision_var_id;

  /* NOTE: can happen that variable has no active occs left
     -> assigning is possible but does not change solver state and wastes work... */

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

  /* NOTE: try to keep priority queue clean: no non-candidates, no assigned_variables,... */

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
      else
        {
          assert (qdpll->options.dh == QDPLL_DH_QTYPE);
          return qtype_dec_heuristic (qdpll, decision_var);
        }
    }
}


/* Before literal watchers are updated: check if the blocking literal
   in 'blit' disables the constraint in 'blit'. If so, then need not
   update watchers -> return 0. Otherwise return the stripped pointer
   to the constraint. */
/* NOTE: used for unit and pure lit
   detection; OPTIMIZATION: when using spure-literals then will never
   see cubes here, could also used separate functions. This seems to
   be a hot spot. */
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
  /* NOTE: do NOT deref constraint pointer here, since this is exactly
     what we want to avoid by blocking literals! */
  assert (blit_occ.blit);
  assert (blit_occ.constraint);
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
    {
      /* Notify watching variables. */
      notify_clause_watching_variables (qdpll, clause_notify_list);
    }

  /* Check clauses for units and conflicts. */
  BLitsOcc *p, *e;
  Constraint *c, *sentinel;
  for (p = lit_notify_list->start, e = lit_notify_list->top; p < e; p++)
    {
      if (!(c = check_disabling_blocking_lit (qdpll, *p, 0)))
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
              if (c->is_cube)
                {
                  qdpll->stats.total_sat_lcubes++;
                }
              else
                {
                  qdpll->stats.total_empty_lclauses++;
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

  /* Loop breaks as soon as conflict or empty formula detected. */
  while (state == QDPLL_SOLVER_STATE_UNDEF &&
         (bcp_ptr = qdpll->bcp_ptr) < qdpll->assigned_vars_top)
    {
      VarID var_id = *bcp_ptr;
      Var *var = VARID2VARPTR (vars, var_id);

#if COMPUTE_STATS
      qdpll->stats.propagations++;
      qdpll->stats.total_prop_dlevels += var->decision_level;
#endif

      assert (var->mode != QDPLL_VARMODE_UNDEF);
      assert (QDPLL_VAR_ASSIGNED (var));
      assert (var->decision_level != QDPLL_INVALID_DECISION_LEVEL);
      assert (!QDPLL_VAR_MARKED_PROPAGATED (var));

      if (QDPLL_VAR_ASSIGNED_TRUE (var))
        {
          state = propagate_variable_assigned (qdpll, var,
                                               &
                                               (var->
                                                pos_notify_clause_watchers),
                                               &(var->
                                                 pos_notify_lit_watchers));
        }
      else
        {
          assert (QDPLL_VAR_ASSIGNED_FALSE (var));
          state =
            propagate_variable_assigned (qdpll, var,
                                         &(var->neg_notify_clause_watchers),
                                         &(var->neg_notify_lit_watchers));
        }

      qdpll->bcp_ptr++;

      /* If all variables are
         propagated and no conflict was found, we can be sure that the
         formula is SAT. We set the state explicitly here since this is
         has not been done yet. */
      assert (!qdpll->options.no_sdcl || state != QDPLL_SOLVER_STATE_SAT);
      if (state == QDPLL_SOLVER_STATE_UNDEF &&
          qdpll->bcp_ptr == qdpll->assigned_vars_top &&
          qdpll->pcnf.used_vars ==
          (unsigned int) (qdpll->assigned_vars_top - qdpll->assigned_vars))
        state = QDPLL_SOLVER_STATE_SAT;
    }

#ifndef NDEBUG
#if QDPLL_ASSERT_BCP_WATCHERS_INTEGRITY
  if (state == QDPLL_SOLVER_STATE_UNDEF)
    {
      assert_all_unit_literals_and_literal_watchers_integrity (qdpll);
      assert_all_pure_literals_and_clause_watchers_integrity (qdpll);
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
cleanup_constraint (QDPLL * qdpll, Constraint * c)
{
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


/* Delete all marked constraints, clean up occ-lists. NOTE: this is
   only needed when we do not allow spurious pure literals, i.e. when
   learnt constraints can appear on occ-lists. We can no longer remove
   deleted constraints in O(1) by unlinking because for blocking literals
   we traded linked-occ-lists for contiguous occ-stacks. */
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
          cleanup_constraint (qdpll, c);
        }
    }
  assert (del == check_del);
}


static void
check_resize_learnt_constraints (QDPLL * qdpll,
                                 const QDPLLQuantifierType type)
{
  assert (qdpll->state.lclauses_size);
  assert (qdpll->state.lcubes_size);

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

  unsigned int del_threshold = 0;

  /* Try to delete half of learnt constraints, starting from back of
     lists which is supposed to contain 'less important' constraints. */
  unsigned int try_delete = type == QDPLL_QTYPE_EXISTS ?
    qdpll->pcnf.learnt_clauses.cnt * qdpll->options.lclauses_delfactor :
    qdpll->pcnf.learnt_cubes.cnt * qdpll->options.lcubes_delfactor;
  unsigned int del = 0;
  assert (del < try_delete);
  const int no_spure_literals = qdpll->options.no_spure_literals;
  Constraint *prev, *result_constraint = qdpll->result_constraint;
  for (c = constraints->last; c && (del < try_delete); c = prev)
    {
      assert (c->learnt);
      prev = c->link.prev;

      if (!c->is_reason && !c->is_watched && c != result_constraint)
        {
          if (!no_spure_literals)
            cleanup_constraint (qdpll, c);
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

  assert (type != QDPLL_QTYPE_EXISTS ||
          qdpll->state.lclauses_size == qdpll->pcnf.learnt_clauses.cnt + del);
  assert (type != QDPLL_QTYPE_FORALL ||
          qdpll->state.lcubes_size == qdpll->pcnf.learnt_cubes.cnt + del);

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
  else
    assert (0);

  fprintf (stderr, "--seed=%d\n", qdpll->options.seed);

  if (qdpll->options.depman_simple)
    fprintf (stderr, "--dep-man=simple\n");
  if (qdpll->options.depman_qdag)
    fprintf (stderr, "--dep-man=qdag\n");
  fprintf (stderr, "--max-dec=%d\n", qdpll->options.max_dec);
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
      /* Must make sure that conflict/solution is fixed after restart. */
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


/* Solver's core loop. */
static QDPLLResult
solve (QDPLL * qdpll)
{
  if (qdpll->options.depman_simple)
    fprintf (stderr,
             "NOTE: using the original quantifier prefix of the formula for dependency analysis. Try '--dep-man=qdag' instead.\n");

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

  qdpll->state.lclauses_size = qdpll->options.lclauses_init_size;
  qdpll->state.lcubes_size = qdpll->options.lcubes_init_size;

  assert (qdpll->state.decision_level == 0);
  assert (sizeof_top_level (qdpll) == 0);

  if (!qdpll->dm->is_init (qdpll->dm))
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "Initializing dependencies.\n");
#if COMPUTE_STATS
      qdpll->stats.total_dep_man_init_calls++;
#endif
      qdpll->dm->init (qdpll->dm);
      /* Workaround: see 'solve ()'. */
      assert (qdpll->num_deps_init == 1);
      qdpll->num_deps_init = 0;
      qdpll->num_deps_init++;
    }

  state = set_up_watchers (qdpll);
  /*TODO at this point: if the original formula was decided right away
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
        fprintf (stderr, "SDCL: formula is empty.\n");

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
      state = bcp (qdpll);
      qdpll->state.restarting = 0;
 
     if (state == QDPLL_SOLVER_STATE_UNSAT)
        {
          /* Conflict: analyze conflict and backtrack. */
          assert (qdpll->result_constraint
                  && !qdpll->result_constraint->is_cube);
          assert (is_clause_empty (qdpll, qdpll->result_constraint));
          assert (!is_clause_satisfied (qdpll, qdpll->result_constraint));

          check_resize_learnt_constraints (qdpll, QDPLL_QTYPE_EXISTS);

#if QDPLL_ASSERT_SOLVE_STATE
          assert (is_formula_false (qdpll));
          assert (!is_formula_true (qdpll));
#endif
          backtrack_level = analyze_conflict (qdpll);
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
                  backtrack (qdpll, backtrack_level);
                  push_forced_assignment (qdpll);
                }
            }

          /* Conflict must be fixed now. */
          assert (!is_clause_empty (qdpll, qdpll->result_constraint));
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
          assert (is_formula_true (qdpll));
#endif
          backtrack_level = analyze_solution (qdpll);
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


/* -------------------- START: PUBLIC FUNCTIONS --------------------*/


QDPLL *
qdpll_create ()
{
  QDPLLMemMan *mm = qdpll_create_mem_man ();
  QDPLL *qdpll = (QDPLL *) qdpll_malloc (mm, sizeof (QDPLL));
  qdpll->mm = mm;
  Scope *default_scope = (Scope *) qdpll_malloc (mm, sizeof (Scope));
  default_scope->type = QDPLL_QTYPE_EXISTS;
  assert (default_scope->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  LINK_LAST (qdpll->pcnf.scopes, default_scope, link);
  qdpll->pcnf.size_vars = DEFAULT_VARS_SIZE;
  qdpll->pcnf.vars =
    (Var *) qdpll_malloc (mm, DEFAULT_VARS_SIZE * sizeof (Var));

  /* Set default options. */

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
  qdpll->num_deps_init = 1;

  /* Must also set seed when new seed is configured. */
  srand (qdpll->options.seed);

  return qdpll;
}


void
qdpll_delete (QDPLL * qdpll)
{
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  QDPLLMemMan *mm = qdpll->mm;

  QDPLL_DELETE_STACK (mm, qdpll->add_stack);
  QDPLL_DELETE_STACK (mm, qdpll->add_stack_tmp);
  QDPLL_DELETE_STACK (mm, qdpll->wreason_a);
  QDPLL_DELETE_STACK (mm, qdpll->wreason_e);
  QDPLL_DELETE_STACK (mm, qdpll->dec_vars);
  QDPLL_DELETE_STACK (mm, qdpll->smaller_type_lits);
  /* Delete scopes. */
  Scope *s, *n;
  for (s = qdpll->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
      delete_scope (qdpll, s);
    }

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
  ConstraintList *constraints = &(qdpll->pcnf.clauses);
  Constraint *c, *nc;
  for (c = constraints->first; c; c = nc)
    {
      nc = c->link.next;
      assert (!c->is_cube);
      assert (!c->learnt);
      delete_constraint (qdpll, c);
    }

  /* Delete learnt clauses. */
  constraints = &(qdpll->pcnf.learnt_clauses);
  for (c = constraints->first; c; c = nc)
    {
      nc = c->link.next;
      assert (!c->is_cube);
      assert (c->learnt);
      delete_constraint (qdpll, c);
    }

  /* Delete learnt cubes. */
  constraints = &(qdpll->pcnf.learnt_cubes);
  for (c = constraints->first; c; c = nc)
    {
      nc = c->link.next;
      assert (c->is_cube);
      assert (c->learnt);
      delete_constraint (qdpll, c);
    }

  qdpll_free (mm, qdpll->var_pqueue, qdpll->size_var_pqueue * sizeof (VarID));
  qdpll_free (mm, qdpll->assigned_vars,
              size_assigned_vars (qdpll) * sizeof (VarID));

  assert (qdpll->dm);
  assert ((qdpll->options.depman_simple && !qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && !qdpll->options.depman_qdag));
  /* Delete dependency manager. 
     IMPORTANT NOTE: all heap-memory managed by DepMan must already have been deleted before! */
  qdpll_qdag_dep_man_delete ((QDPLLDepManQDAG *) qdpll->dm);

  qdpll_free (mm, qdpll, sizeof (QDPLL));
  qdpll_delete_mem_man (mm);
}


/* Configure solver instance via configuration string. 
   Returns null pointer on success and error string otherwise. */
/* NOTE: calling this function is safe before a call of 'qdpll_sat()'. Any
   other calling policy might result in undefined behaviour. */
char *
qdpll_configure (QDPLL * qdpll, char *configure_str)
{
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
          qdpll->options.var_act_bias = atoi (configure_str);;
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
        qdpll->options.max_dec = atoi (configure_str);
      else
        result = "Expecting number after '--max-dec='";
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


void
qdpll_adjust_vars (QDPLL * qdpll, VarID num)
{
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  QDPLL_ABORT_QDPLL (num == 0, "'num' must not be zero!");
  VarID size_vars = qdpll->pcnf.size_vars;
  /* Index 0 is never used in variable table, hence increase 'num' */
  if (size_vars < ++num)
    {
      qdpll->pcnf.vars = (Var *) qdpll_realloc (qdpll->mm, qdpll->pcnf.vars,
                                                size_vars * sizeof (Var),
                                                num * sizeof (Var));
      qdpll->pcnf.size_vars = num;
    }
}


unsigned int
qdpll_new_scope (QDPLL * qdpll, QDPLLQuantifierType qtype)
{
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  QDPLL_ABORT_QDPLL ((qtype != QDPLL_QTYPE_EXISTS &&
                      qtype != QDPLL_QTYPE_FORALL), "invalid 'qtype'!");
  QDPLL_ABORT_QDPLL (qdpll->state.scope_opened,
                     "there is already a new, open scope!");
  /* There must be at least a default scope. */
  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.last);
  assert (qdpll->pcnf.scopes.first != qdpll->pcnf.scopes.last ||
          (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.first) &&
           qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING));

  qdpll->state.scope_opened = 1;
  unsigned int nesting = qdpll->pcnf.scopes.last->nesting + 1;
  assert (nesting > 0);
  Scope *scope = (Scope *) qdpll_malloc (qdpll->mm, sizeof (Scope));
  scope->nesting = nesting;
  scope->type = qtype;
  LINK_LAST (qdpll->pcnf.scopes, scope, link);
  return nesting;
}


/* NOTE: semantics of 'qdpll_add' must support DIMACS as well as QDIMACS format.
   For DIMACS, all variables must be added to the default, existential scope, 
   which could be done e.g. before solving starts.
   For QDIMACS, scopes are closed - as clauses are in (Q)DIMACS - by adding '0'. */
void
qdpll_add (QDPLL * qdpll, LitID id)
{
  QDPLL_ABORT_QDPLL (!qdpll, "'qdpll' is null!");
  const char *err_msg;

  QDPLLMemMan *mm = qdpll->mm;
  LitIDStack *add_stack = &(qdpll->add_stack);

  if (id == 0)
    {
      /* '0' closes a scope or clause */
      err_msg = import_added_ids (qdpll);
      QDPLL_ABORT_QDPLL (err_msg, err_msg);
      assert (!qdpll->state.scope_opened);
    }
  else
    QDPLL_PUSH_STACK (mm, *add_stack, id);
}


QDPLLResult
qdpll_sat (QDPLL * qdpll)
{
#if COMPUTE_TIMES
  qdpll->time_stats.sat_time_start = time_stamp ();
#endif
  if (qdpll->options.verbosity > 0)
    print_config (qdpll);

  /* Reset any previous result. */
  qdpll->result = QDPLL_RESULT_UNKNOWN;

  QDPLLMemMan *mm = qdpll->mm;
  assert ((qdpll->options.depman_simple && !qdpll->options.depman_qdag) ||
          (!qdpll->options.depman_simple && qdpll->options.depman_qdag)
          || (!qdpll->options.depman_simple && !qdpll->options.depman_qdag));

  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
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


/* Get assignment of variable.  
   NOTE/TODO: we do NOT check whether the
   formula has been decided, this is the caller's responsibility. */
QDPLLAssignment
qdpll_get_value (QDPLL * qdpll, VarID id)
{
  assert (id);
  assert (id < qdpll->pcnf.size_vars);
  Var *var = VARID2VARPTR (qdpll->pcnf.vars, id);
  assert (var->assignment == QDPLL_ASSIGNMENT_TRUE ||
          var->assignment == QDPLL_ASSIGNMENT_FALSE ||
          var->assignment == QDPLL_ASSIGNMENT_UNDEF);
  return var->assignment;
}


void
qdpll_print (QDPLL * qdpll, FILE * out)
{
  clean_up_formula (qdpll);
#ifndef NDEBUG
#if QDPLL_ASSERT_FULL_FORMULA_INTEGRITY
  assert_full_formula_integrity (qdpll);
#endif
#endif
  assert (qdpll->pcnf.clauses.cnt ==
          count_constraints (&(qdpll->pcnf.clauses)));

  fprintf (out, "p cnf %d %d\n", qdpll->pcnf.max_declared_var_id,
           qdpll->pcnf.clauses.cnt);

  assert (qdpll->pcnf.scopes.first);
  assert (qdpll->pcnf.scopes.first->nesting == QDPLL_DEFAULT_SCOPE_NESTING);
  assert (QDPLL_SCOPE_EXISTS (qdpll->pcnf.scopes.first));

  Scope *s;
  for (s = qdpll->pcnf.scopes.first; s; s = s->link.next)
    {
      if (QDPLL_COUNT_STACK (s->vars) == 0)
        continue;

      if (QDPLL_SCOPE_EXISTS (s))
        fprintf (out, "e");
      else
        fprintf (out, "a");

      VarID *p, *e;
      for (p = s->vars.start, e = s->vars.top; p < e; p++)
        fprintf (out, " %u", *p);
      fprintf (out, " 0\n");
    }

  Constraint *c;
  for (c = qdpll->pcnf.clauses.first; c; c = c->link.next)
    {
      assert (!c->is_cube);
      if (c->num_lits > 0)
        {
          int *p = c->lits, *e;
          fprintf (out, "%d", *p);
          for (p++, e = c->lits + c->num_lits; p < e; p++)
            fprintf (out, " %d", *p);
          fprintf (out, " 0\n");
        }
      else
        {
          /* For empty clause, print out two complementary unit
             clauses to be QDIMACS-compliant. Using id 1 here. */
          /* TODO: fix this to use a declared variable. */
          fprintf (out, "%d 0\n", 1);
          fprintf (out, "%d 0\n", -1);
        }
    }
}


/* Print QDIMACS-compliant output to stdout as defined at: 

     http://www.qbflib.org/qdimacs.html 

   NOTE: it can happen that not all variables in the outermost block are
   assigned. In this case, the values of unassigned variables in general
   CANNOT be selected arbitrarily. Consider the following example of an
   unsatisfiable QBF:

   p cnf 4 3
   a 1 2 0
   e 3 4 0
   -1 3 0
   -3 4 0
   2 -4 0

   It is easy to see that setting variable 1 from the outermost block to true
   implies 3, which implies 4 and finally the clause (2 -4) is falsified because
   literal 2 is deleted by universal reduction. This conflicting clause already
   explains unsatisfiability of the QBF because we made only one assumption on
   the universal variable 1. In terms of Q-resolution proofs, we can derive the
   empty clause as follows (2 -4),(-3 4) -> (2,-3) and (2,-3),(-1,3) -> {}.

   Since the outermost block is universal and the QBF is unsatisfiable, we
   output values for variables 1 and 2. For variable 1 we print the value
   "true" because this was our assumption. However, variable 2 was not
   assigned explicitly to determine the result. Setting it to true in the
   output would satisfy the clause (2 -4) and furthermore the QBF would no
   longer be unsatisfiable. 

   CONSEQUENTLY: this function does not print values for variables which were
   not assigned by the solver. */
void
qdpll_print_qdimacs_output (QDPLL * qdpll)
{
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
           qdpll->pcnf.max_declared_var_id, qdpll->pcnf.clauses.cnt);

  /* Must properly handle default scope. */
  Scope *outer = qdpll->pcnf.scopes.first;
  assert (outer);
  assert (outer->type == QDPLL_QTYPE_EXISTS);
  if (QDPLL_COUNT_STACK (outer->vars) == 0 && outer->link.next)
    {
      outer = outer->link.next;
      assert (QDPLL_COUNT_STACK (outer->vars) != 0);
      assert (outer->nesting != QDPLL_DEFAULT_SCOPE_NESTING);
    }

  if ((result == QDPLL_RESULT_SAT && outer->type == QDPLL_QTYPE_EXISTS) ||
      (result == QDPLL_RESULT_UNSAT && outer->type == QDPLL_QTYPE_FORALL))
    {

      Var *vars = qdpll->pcnf.vars;
      VarID *p, *e;
      for (p = outer->vars.start, e = outer->vars.top; p < e; p++)
        {
          assert (*p);
          Var *var = VARID2VARPTR (vars, *p);
          assert (var->id);

          /* assert (var->assignment != QDPLL_ASSIGNMENT_UNDEF);
             QDPLL_ABORT_QDPLL (var->assignment == QDPLL_ASSIGNMENT_UNDEF,
             "variable unassigned!"); */

          if (var->assignment != QDPLL_ASSIGNMENT_UNDEF)
            fprintf (stdout, "V %d 0\n",
                     var->assignment == QDPLL_ASSIGNMENT_TRUE ?
                     var->id : -(var->id));
        }
    }
}


void
qdpll_init_deps (QDPLL * qdpll)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);

  /* NOTE: we should in general clean up if clauses, scopes etc. have been added. */
  clean_up_formula (qdpll);

  if (!dm->is_init (dm))
    {
      if (qdpll->options.verbosity > 1)
        fprintf (stderr, "Initializing dependencies.\n");
#if COMPUTE_STATS
      qdpll->stats.total_dep_man_init_calls++;
#endif
      dm->init (dm);
      qdpll->num_deps_init++;
    }
}

/* Returns non-zero if variable 'id2' depends on variable 'id1', 
   i.e. if id1 < id2, with respect to the current dependency scheme. */
int 
qdpll_var_depends (QDPLL * qdpll, VarID x, VarID y)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");
  QDPLL_ABORT_QDPLL (x <= 0, "variable ID must be greater than 0!");
  QDPLL_ABORT_QDPLL (x > qdpll->pcnf.max_declared_var_id,
                     "variable ID larger than largest declared ID!");
  QDPLL_ABORT_QDPLL (y <= 0, "variable ID must be greater than 0!");
  QDPLL_ABORT_QDPLL (y > qdpll->pcnf.max_declared_var_id,
                     "variable ID larger than largest declared ID!");

  return dm->depends(dm, x, y);
}


/* Note: could also return a collection of variable IDs. */
void
qdpll_print_deps (QDPLL * qdpll, VarID id)
{
  QDPLL_ABORT_QDPLL (qdpll->pcnf.max_declared_var_id >= qdpll->pcnf.size_vars,
                     "largest declared ID larger than size of variables!");
  QDPLL_ABORT_QDPLL (id <= 0, "'id' must be greater than 0!");
  QDPLL_ABORT_QDPLL (id > qdpll->pcnf.max_declared_var_id,
                     "'id' larger than largest declared ID!");
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");

  dm->print_deps (dm, id);
}


VarID
qdpll_get_max_declared_var_id (QDPLL * qdpll)
{
  return qdpll->pcnf.max_declared_var_id;
}


VarID
qdpll_new_var (QDPLL * qdpll, VarID id)
{
  Var *vars = qdpll->pcnf.vars;
  Var *var = VARID2VARPTR (vars, id);
  Scope *s = var->scope;
  VarID max = qdpll_get_max_declared_var_id (qdpll);
  VarID new_id = max + 1;
  qdpll_adjust_vars (qdpll, new_id);
  declare_and_init_variable (qdpll, s, new_id);
  return new_id;
}


/* Dump dependency graph to 'stdout' in DOT format. */
void
qdpll_dump_dep_graph (QDPLL * qdpll)
{
  QDPLLDepManGeneric *dm = qdpll->dm;
  assert (dm);
  QDPLL_ABORT_QDPLL (!dm->is_init (dm),
                     "dependency manager is not initialized!");

  dm->dump_dep_graph (dm);
}


void
qdpll_print_stats (QDPLL * qdpll)
{
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
           qdpll->stats.total_sdcl_covers);

  fprintf (stderr, "Total learnt cubes mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_cubes_mtfs);
  fprintf (stderr, "Total learnt clause mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_clauses_mtfs);
  fprintf (stderr, "Total learnt constr. mtfs:\t\t%llu\n",
           qdpll->stats.total_learnt_clauses_mtfs +
           qdpll->stats.total_learnt_cubes_mtfs);
  fprintf (stderr, "Total mtf d.deps constr.:\t\t%llu ( %f )\n\n",
           qdpll->stats.total_mtf_dirty_deps_constraints,
           qdpll->stats.total_learnt_mtf_calls ?
           qdpll->stats.total_mtf_dirty_deps_constraints /
           (float) (qdpll->stats.total_learnt_mtf_calls) : 0);

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
           qdpll->stats.total_type_reduce_by_deps);
  fprintf (stderr, "Avg. type-red. lits per call:\t%f\n\n",
           qdpll->stats.total_type_reduce_calls ?
           qdpll->stats.total_type_reduce_by_deps /
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
  fprintf (stderr, "Total empty lclauses: %llu\n",
           qdpll->stats.total_empty_lclauses);

  fprintf (stderr, "Total const min lits reducible: %llu\n",
           qdpll->stats.constr_min_lits_reducible);
  fprintf (stderr, "Avg. const min lits reducible: %f\n\n",
           qdpll->stats.constr_min_lits_seen ?
           qdpll->stats.constr_min_lits_reducible /
           (float) qdpll->stats.constr_min_lits_seen : 0);

#if COMPUTE_STATS_BTLEVELS_SIZE
  fprintf (stderr, "Cumulative backtrack level stats:\n");
  fprintf (stderr, "<= %4d: %lld\n", 0, qdpll->stats.btlevels[0]);
  unsigned int i;
  for (i = 1; i < COMPUTE_STATS_BTLEVELS_SIZE - 1; i++)
    fprintf (stderr, "<= %4d: %lld\n", 1 << (i - 1),
             qdpll->stats.btlevels[i]);
  fprintf (stderr, "total: %lld\n",
           qdpll->stats.btlevels[COMPUTE_STATS_BTLEVELS_SIZE - 1]);

  fprintf (stderr, "<= %4d: %lld\n", 0, qdpll->stats.btlevels_lin[0]);
  for (i = 1; i < COMPUTE_STATS_BTLEVELS_SIZE - 1; i++)
    fprintf (stderr, "<= %4d: %lld\n", 5 * i, qdpll->stats.btlevels_lin[i]);
  fprintf (stderr, "\n");
#endif

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


/* Reset internal solver state, keep clauses and variables. */
void
qdpll_reset (QDPLL * qdpll)
{
  qdpll->dm->reset (qdpll->dm);
  qdpll->result = QDPLL_RESULT_UNKNOWN;
  backtrack (qdpll, 1);
}


/* -------------------- END: PUBLIC FUNCTIONS --------------------*/
