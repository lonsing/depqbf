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
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include "qdpll_internals.h"
#include "qdpll_pcnf.h"
#include "qdpll_exit.h"
#include "qdpll_dep_man_generic.h"
#include "qdpll_dep_man_qdag.h"
#include "qdpll_config.h"


#define QDPLL_ABORT_DEPMAN(cond,msg)					\
  do {									\
    if (cond)								\
      {									\
        fprintf (stderr, "[qdpll_depman] %s at line %d: %s\n", __func__, \
                 __LINE__,msg);						\
        fflush (stderr);                                                \
        abort();                                                        \
      }									\
  } while (0)


struct QDPLLDepManQDAG
{
  /* DO NOT ADD MEMBERS BEFORE 'dmg'! */
  QDPLLDepManGeneric dmg;
  QDPLLMemMan *mm;
  QDPLLPCNF *pcnf;
  QDAGVarList candidates;        /* anchor of decision candidates list. */
  struct
  {
    unsigned int init:1;
  } state;
#if COMPUTE_STATS
  struct
  {
    /* Cumulated statistics. */
    unsigned long long int num_decision_points;
    unsigned long long int num_total_active_cands_at_dp;
    unsigned long long int num_total_active_vars_at_dp;
    long double num_total_ratio_active_cands_per_active_vars;
    unsigned long long int num_total_notinact_calls;
    unsigned long long int num_total_notinact_exists_calls;
    unsigned long long int num_total_notinact_forall_calls;
    /* Costs: any derefs of edges, classes or variables. */
    unsigned long long int num_total_notinact_costs;
    unsigned long long int num_max_notinact_costs;

    unsigned long long int num_total_notact_calls;
    unsigned long long int num_total_notact_exists_calls;
    unsigned long long int num_total_notact_forall_calls;
    /* Costs: any deref of edges, classes or variables. */
    unsigned long long int num_total_notact_costs;
    unsigned long long int num_max_notact_costs;

    /* Get-candidate costs correspond to calls: always unlink one. */
    unsigned long long int num_total_get_cand_costs;
    unsigned long long int num_total_get_cand_costs_at_last_dp;
    unsigned long long int num_max_get_cand_costs;

    /* Costs for dependency checks. */
    unsigned long long int num_total_depends_calls;
    unsigned long long int num_total_depends_costs;
    unsigned long long int num_max_depends_costs;

    /* Ad-hoc statistics. */
    unsigned long long int num_cur_inactive;
    unsigned long long int num_cur_active_cands;
  } stats;
#endif
};


/* Link-unlink macros for pointerless list and link fields of variables. */
#define VAR_LINK(vars, anchor, element, link)				\
  do {									\
    assert (!(element)->link.prev);					\
    assert (!(element)->link.next);					\
    if ((anchor).last)							\
      {									\
        assert (!VARID2VARPTR((vars), (anchor).last)->link.next);	\
        assert ((anchor).first);                                        \
        assert (!VARID2VARPTR((vars), (anchor).first)->link.prev);	\
        VARID2VARPTR((vars), (anchor).last)->link.next = (element)->id;	\
      }									\
    else                                                                \
      {									\
        assert (!(anchor).first);					\
        (anchor).first = (element)->id;					\
      }									\
    (element)->link.prev = (anchor).last;				\
    (element)->link.next = 0;						\
    (anchor).last = (element)->id;					\
  } while (0)

#define VAR_UNLINK(vars, anchor, element, link)				\
  do {									\
    if ((element)->link.prev)						\
      {									\
        assert ((anchor).first);                                        \
        assert ((anchor).last);						\
        assert (VARID2VARPTR((vars), (element)->link.prev)->link.next == \
                (element)->id);						\
        VARID2VARPTR((vars), (element)->link.prev)->link.next =		\
          (element)->link.next;						\
      }									\
    else                                                                \
      {									\
        assert ((anchor).first == (element)->id);			\
        (anchor).first = (element)->link.next;				\
      }									\
    if ((element)->link.next)						\
      {									\
        assert ((anchor).first);                                        \
        assert ((anchor).last);						\
        assert (VARID2VARPTR((vars), (element)->link.next)->link.prev == \
                (element)->id);						\
        VARID2VARPTR((vars), (element)->link.next)->link.prev =		\
          (element)->link.prev;						\
      }									\
    else                                                                \
      {									\
        assert ((anchor).last == (element)->id);                        \
        (anchor).last = (element)->link.prev;				\
      }									\
    (element)->link.prev = (element)->link.next = 0;			\
  } while (0)


#define GETQDAG(type) qdag
#define GETPART(type) partition

/* -------------------- START: UNION-FIND -------------------- */

#define UF_IS_REP(var,ufoffset,type) ((var)->GETQDAG((type)).uf[(ufoffset)].par == ((var)->id))
#define UF_IS_SINGLETON_SET(var,ufoffset,type) (UF_IS_REP((var),(ufoffset),(type)) && \
                                                (var)->GETQDAG((type)).uf[(ufoffset)].members.list.first == \
                                                (var)->GETQDAG((type)).uf[(ufoffset)].members.list.last && \
                                                (var)->GETQDAG((type)).uf[(ufoffset)].members.list.last == \
                                           (var->id))
static void
uf_make_set (Var * v, const unsigned int ufoffset)
{
  assert (!v->GETQDAG (type).uf[ufoffset].par);
  assert (!v->GETQDAG (type).uf[ufoffset].members.list.first);
  assert (!v->GETQDAG (type).uf[ufoffset].members.list.last);
  v->GETQDAG (type).uf[ufoffset].par = v->id;
  v->GETQDAG (type).uf[ufoffset].members.list.first =
    v->GETQDAG (type).uf[ufoffset].members.list.last = v->id;
}

static Var *
uf_find (Var * vars, Var * v, const unsigned int ufoffset,
         const QDPLLDepManType type)
{
  assert (v->id);
  Var *rep, *par;

  for (rep = v, par = VARID2VARPTR (vars, v->GETQDAG (type).uf[ufoffset].par);
       rep != par;
       rep = par, par =
       VARID2VARPTR (vars, par->GETQDAG (type).uf[ufoffset].par))
    ;

  Var *p;
  for (p = v, par = VARID2VARPTR (vars, v->GETQDAG (type).uf[ufoffset].par);
       p != par;
       p = par, par =
       VARID2VARPTR (vars, par->GETQDAG (type).uf[ufoffset].par))
    p->GETQDAG (type).uf[ufoffset].par = rep->id;

  assert (rep->id);
  return rep;
}


#define UF_MERGE_MEMBERS_NN(vars, v1,v2,ufoffset,type)			\
  do {									\
    assert (!UF_IS_SINGLETON_SET((v1),(ufoffset),(type)) || UF_IS_SINGLETON_SET((v2),(ufoffset),(type))); \
    assert (!VARID2VARPTR((vars), (v1)->GETQDAG(type).uf[ufoffset].members.list.last)->        \
            GETQDAG(type).uf[ufoffset].members.link.next);		\
    VARID2VARPTR((vars), (v1)->GETQDAG(type).uf[ufoffset].members.list.last)-> \
      GETQDAG(type).uf[ufoffset].members.link.next = (v2)->GETQDAG(type).uf[ufoffset].members.list.first; \
    assert (!VARID2VARPTR((vars), (v2)->GETQDAG(type).uf[ufoffset].members.list.first)-> \
            GETQDAG(type).uf[ufoffset].members.link.prev);		\
    VARID2VARPTR((vars), (v2)->GETQDAG(type).uf[ufoffset].members.list.first)->	\
      GETQDAG(type).uf[ufoffset].members.link.prev = (v1)->GETQDAG(type).uf[ufoffset].members.list.last; \
    (v1)->GETQDAG(type).uf[ufoffset].members.list.last = (v2->id);	\
    assert (!VARID2VARPTR((vars), (v2)->GETQDAG(type).uf[ufoffset].members.list.last)->	\
            GETQDAG(type).uf[ufoffset].members.link.next);                                        \
    VARID2VARPTR((vars), (v2)->GETQDAG(type).uf[ufoffset].members.list.last)->                \
      GETQDAG(type).uf[ufoffset].members.link.next = (v2->id);                                \
    (v2)->GETQDAG(type).uf[ufoffset].members.link.prev = (v2)->GETQDAG(type).uf[ufoffset].members.list.last;        \
    (v2)->GETQDAG(type).uf[ufoffset].members.link.next = 0;                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.first);                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.last);                                \
    assert (!(v2)->GETQDAG(type).uf[ufoffset].members.link.next);                                \
  } while (0)

#define UF_MERGE_MEMBERS_N1(vars,v1,v2,ufoffset,type)                        \
  do {                                                                        \
    assert (!UF_IS_SINGLETON_SET((v1),(ufoffset),(type)) || UF_IS_SINGLETON_SET((v2),(ufoffset),(type))); \
    assert ((v2)->GETQDAG(type).uf[ufoffset].members.list.first == (v2->id) &&                \
            (v2)->GETQDAG(type).uf[ufoffset].members.list.last == (v2->id));                \
    VARID2VARPTR((vars), (v1)->GETQDAG(type).uf[ufoffset].members.list.last)->                \
      GETQDAG(type).uf[ufoffset].members.link.next = (v2->id);                                \
    (v2)->GETQDAG(type).uf[ufoffset].members.link.prev = (v1)->GETQDAG(type).uf[ufoffset].members.list.last;        \
    (v2)->GETQDAG(type).uf[ufoffset].members.link.next = 0;                                \
    (v1)->GETQDAG(type).uf[ufoffset].members.list.last = (v2->id);                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.first);                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.last);                                \
    assert (!(v2)->GETQDAG(type).uf[ufoffset].members.link.next);                                \
  } while (0)

#define UF_MERGE_MEMBERS_11(vars, v1,v2,ufoffset,type)                        \
  do {                                                                        \
    (v1)->GETQDAG(type).uf[ufoffset].members.list.first =                                        \
      (v1)->GETQDAG(type).uf[ufoffset].members.list.last = (v2)->id;                        \
    (v2)->GETQDAG(type).uf[ufoffset].members.link.prev =                                        \
      (v2)->GETQDAG(type).uf[ufoffset].members.link.next = 0;                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.first);                                \
    assert ((v1)->GETQDAG(type).uf[ufoffset].members.list.last);                                \
    assert (!(v2)->GETQDAG(type).uf[ufoffset].members.link.next);                                \
  } while (0)

static void
uf_link (Var * vars, Var * v1, Var * v2, const unsigned int ufoffset)
{
  assert (UF_IS_REP (v1, ufoffset, type));
  assert (UF_IS_REP (v2, ufoffset, type));
  assert (!UF_IS_SINGLETON_SET (v1, ufoffset, type)
          || v1->GETQDAG (type).uf[ufoffset].rank == 0);
  assert (!UF_IS_SINGLETON_SET (v2, ufoffset, type)
          || v2->GETQDAG (type).uf[ufoffset].rank == 0);
  assert (!UF_IS_SINGLETON_SET (v1, ufoffset, type)
          || !UF_IS_SINGLETON_SET (v2, ufoffset, type)
          || (v2->GETQDAG (type).uf[ufoffset].rank ==
              v1->GETQDAG (type).uf[ufoffset].rank
              && v1->GETQDAG (type).uf[ufoffset].rank == 0));
  assert (UF_IS_SINGLETON_SET (v1, ufoffset, type)
          || !UF_IS_SINGLETON_SET (v2, ufoffset, type)
          || v2->GETQDAG (type).uf[ufoffset].rank <
          v1->GETQDAG (type).uf[ufoffset].rank);
  assert (!UF_IS_SINGLETON_SET (v1, ufoffset, type)
          || UF_IS_SINGLETON_SET (v2, ufoffset, type)
          || v2->GETQDAG (type).uf[ufoffset].rank >
          v1->GETQDAG (type).uf[ufoffset].rank);
  assert (v1->GETQDAG (type).uf[ufoffset].class_link.prev
          || v1->GETQDAG (type).uf[ufoffset].class_link.next);
  assert (v2->GETQDAG (type).uf[ufoffset].class_link.prev
          || v2->GETQDAG (type).uf[ufoffset].class_link.next);

  if (v1->GETQDAG (type).uf[ufoffset].rank >
      v2->GETQDAG (type).uf[ufoffset].rank)
    {
      assert (!UF_IS_SINGLETON_SET (v1, ufoffset, type));
      if (UF_IS_SINGLETON_SET (v2, ufoffset, type))
        UF_MERGE_MEMBERS_N1 (vars, v1, v2, ufoffset, type);
      else
        UF_MERGE_MEMBERS_NN (vars, v1, v2, ufoffset, type);
      v2->GETQDAG (type).uf[ufoffset].par = v1->id;
      assert (!UF_IS_REP (v2, ufoffset, type));
      VAR_UNLINK (vars, v2->scope->GETPART (type).classes[ufoffset], v2,
                  GETQDAG (type).uf[ufoffset].class_link);
    }
  else
    {
      if (v1->GETQDAG (type).uf[ufoffset].rank ==
          v2->GETQDAG (type).uf[ufoffset].rank)
        {
          assert ((UF_IS_SINGLETON_SET (v1, ufoffset, type)
                   && UF_IS_SINGLETON_SET (v2, ufoffset, type))
                  || (!UF_IS_SINGLETON_SET (v1, ufoffset, type)
                      && !UF_IS_SINGLETON_SET (v2, ufoffset, type)));
          assert (v1->GETQDAG (type).uf[ufoffset].rank != 0
                  || (UF_IS_SINGLETON_SET (v1, ufoffset, type)
                      && UF_IS_SINGLETON_SET (v2, ufoffset, type)));
          assert ((!UF_IS_SINGLETON_SET (v1, ufoffset, type)
                   || !UF_IS_SINGLETON_SET (v2, ufoffset, type))
                  || v1->GETQDAG (type).uf[ufoffset].rank == 0);
          v2->GETQDAG (type).uf[ufoffset].rank++;
          if (UF_IS_SINGLETON_SET (v1, ufoffset, type)
              && UF_IS_SINGLETON_SET (v2, ufoffset, type))
            UF_MERGE_MEMBERS_11 (vars, v2, v1, ufoffset, type);
          else
            UF_MERGE_MEMBERS_NN (vars, v2, v1, ufoffset, type);
        }
      else
        {
          assert (!UF_IS_SINGLETON_SET (v2, ufoffset, type));
          if (UF_IS_SINGLETON_SET (v1, ufoffset, type))
            UF_MERGE_MEMBERS_N1 (vars, v2, v1, ufoffset, type);
          else
            UF_MERGE_MEMBERS_NN (vars, v2, v1, ufoffset, type);
        }
      v1->GETQDAG (type).uf[ufoffset].par = v2->id;
      assert (!UF_IS_REP (v1, ufoffset, type));
      VAR_UNLINK (vars, v1->scope->GETPART (type).classes[ufoffset], v1,
                  GETQDAG (type).uf[ufoffset].class_link);
    }
}


static void
uf_unite (Var * vars, Var * v1, Var * v2, const unsigned int ufoffset,
          const QDPLLDepManType type)
{
  assert (v1->scope == v2->scope);
  assert (v1->GETQDAG (type).uf[ufoffset].par);
  assert (v2->GETQDAG (type).uf[ufoffset].par);

  Var *rep1, *rep2;
  rep1 = uf_find (vars, v1, ufoffset, type);
  rep2 = uf_find (vars, v2, ufoffset, type);

  if (rep1 != rep2)
    uf_link (vars, rep1, rep2, ufoffset);
}

/* -------------------- END: UNION-FIND -------------------- */



/* -------------------- START: EDGE PRIORITY-QUEUE -------------------- */

static void
pq_init (QDPLLMemMan * mm, EdgePriorityQueue * pq, unsigned int init_capacity)
{
  unsigned int bytes;

  if (init_capacity == 0)
    init_capacity = 1;

  bytes = init_capacity * sizeof (Edge *);
  pq->elems_start = pq->elems_top = (Edge **) qdpll_malloc (mm, bytes);
  pq->elems_end = pq->elems_start + init_capacity;
}


static unsigned int
pq_size (EdgePriorityQueue * pq)
{
  return pq->elems_end - pq->elems_start;
}


static void
pq_delete (QDPLLMemMan * mm, EdgePriorityQueue * pq)
{
  qdpll_free (mm, pq->elems_start, pq_size (pq) * sizeof (Edge *));
}


static unsigned int
pq_count (EdgePriorityQueue * pq)
{
  return pq->elems_top - pq->elems_start;
}


static unsigned int
get_left_child_pos (unsigned int cur_pos)
{
  return 2 * cur_pos + 1;
}


static unsigned int
get_right_child_pos (unsigned int cur_pos)
{
  return 2 * (cur_pos + 1);
}


static unsigned int
get_parent_pos (unsigned int cur_pos)
{
  unsigned int result;
  result = (cur_pos - 1) / 2;
  assert (cur_pos == get_right_child_pos (result) ||
          cur_pos == get_left_child_pos (result));
  return result;
}


static int
compare (EdgePriorityQueue * pq, unsigned int pos_a, unsigned int pos_b)
{
  assert (pos_a < pq_count (pq));
  assert (pos_b < pq_count (pq));

  int result;

  Edge **start = pq->elems_start;

  Edge **elem_a = start + pos_a;
  Edge **elem_b = start + pos_b;

  unsigned int elem_a_priority = (*elem_a)->priority;
  unsigned int elem_b_priority = (*elem_b)->priority;

  if (elem_a_priority < elem_b_priority)
    result = -1;
  else if (elem_a_priority == elem_b_priority)
    result = 0;
  else
    result = 1;

  return result;
}


static void
swap (EdgePriorityQueue * pq, unsigned int pos_a, unsigned int pos_b)
{
  assert (pos_a != pos_b);
  assert (pos_a < pq_count (pq));
  assert (pos_b < pq_count (pq));

  Edge *tmp, **start;

  start = pq->elems_start;

  Edge **elem_a, **elem_b;

  elem_a = start + pos_a;
  tmp = *elem_a;
  elem_b = start + pos_b;

  assert ((*elem_b)->pos == pos_b);
  assert ((*elem_a)->pos == pos_a);
  assert (tmp->pos == pos_a);

  *elem_a = *elem_b;
  (*elem_a)->pos = pos_a;

  *elem_b = tmp;
  (*elem_b)->pos = pos_b;
}


static void
up_heap (EdgePriorityQueue * pq, unsigned int cur_pos)
{

#ifndef NDEBUG
  unsigned int count = pq_count (pq);
  assert (cur_pos < count);
#endif

  while (cur_pos > 0)
    {
      unsigned int parent_pos = get_parent_pos (cur_pos);

      if (compare (pq, cur_pos, parent_pos) >= 0)
        break;

      swap (pq, cur_pos, parent_pos);
      cur_pos = parent_pos;
    }                           /* end: while top not reached */
}


static void
down_heap (EdgePriorityQueue * pq, unsigned int cur_pos)
{
  unsigned int child_pos, left_child_pos, right_child_pos;
  unsigned int count = pq_count (pq);

  for (;;)
    {
      left_child_pos = get_left_child_pos (cur_pos);

      if (left_child_pos >= count)
        break;                  /* has no left child */

      right_child_pos = get_right_child_pos (cur_pos);

      if (right_child_pos < count &&
          compare (pq, left_child_pos, right_child_pos) > 0)
        child_pos = right_child_pos;
      else
        child_pos = left_child_pos;

      if (compare (pq, cur_pos, child_pos) > 0)
        {
          swap (pq, cur_pos, child_pos);
          cur_pos = child_pos;
        }
      else
        break;
    }
}


static void
assert_pq_condition (EdgePriorityQueue * pq)
{
  Edge **start = pq->elems_start;

  unsigned int pos, no_children, left_child_pos, right_child_pos;
  no_children = pq_count (pq) / 2;

  for (pos = 0; pos < pq_count (pq); pos++)
    {
      Edge **cur, **left, **right;

      cur = start + pos;
      assert ((*cur)->pos == pos);

      left_child_pos = get_left_child_pos (pos);
      right_child_pos = get_right_child_pos (pos);

      if (pos < no_children)
        {
          assert (left_child_pos < pq_count (pq));

          left = start + left_child_pos;

          if (right_child_pos < pq_count (pq))
            right = start + right_child_pos;

          assert ((*cur)->priority <= (*left)->priority);
          assert (right_child_pos >= pq_count (pq) ||
                  (*cur)->priority <= (*right)->priority);
        }
      else                      /* has no children */
        {
          assert (right_child_pos >= pq_count (pq));
          assert (left_child_pos >= pq_count (pq));
        }
    }
}


static void
pq_enlarge (QDPLLMemMan * mm, EdgePriorityQueue * pq)
{
  unsigned int old_size = pq_size (pq);
  unsigned int new_size = old_size ? 2 * old_size : 1;
  Edge **new = (Edge **) qdpll_malloc (mm, new_size * sizeof (Edge *));
  memcpy (new, pq->elems_start, old_size * sizeof (Edge *));
  qdpll_free (mm, pq->elems_start, old_size * sizeof (Edge *));
  pq->elems_start = new;
  pq->elems_top = pq->elems_start + old_size;
  pq->elems_end = pq->elems_start + new_size;
}


void
pq_insert (QDPLLMemMan * mm, EdgePriorityQueue * pq, Edge * edge,
           unsigned int priority)
{
  if (pq->elems_top == pq->elems_end)
    pq_enlarge (mm, pq);

  *pq->elems_top++ = edge;
  edge->priority = priority;
  edge->pos = pq_count (pq) - 1;

  up_heap (pq, edge->pos);

#ifndef NDEBUG
#if QDAG_PQ_ASSERT_HEAP_CONDITION_INSERT
  assert_pq_condition (pq);
#endif
#endif
}


Edge *
pq_remove_min (EdgePriorityQueue * pq)
{
  Edge **start = pq->elems_start;
  Edge *result = 0;

  if (start == pq->elems_top)
    return 0;

  Edge **last;
  last = --(pq->elems_top);

  assert (start != pq->elems_top || pq_count (pq) == 0);

  result = *start;

  *start = *last;
  (*start)->pos = 0;

  down_heap (pq, 0);

#ifndef NDEBUG
#if QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN
  assert_pq_condition (pq);
#endif
#endif

  return result;
}


/* Remove one element in constant time, e.g. for clearing queue 
   ATTENTION: DESTROYS heap condition! */
Edge *
pq_remove_one (EdgePriorityQueue * pq)
{
  Edge **start = pq->elems_start;
  Edge *result = 0;

  if (start == pq->elems_top)
    return 0;

  Edge **last;
  last = --(pq->elems_top);

  assert (start != pq->elems_top || pq_count (pq) == 0);

  result = *start;

  *start = *last;
  (*start)->pos = 0;

  return result;
}


Edge *
pq_access_min (EdgePriorityQueue * pq)
{
  Edge **start = pq->elems_start;

  if (start == pq->elems_top)
    return 0;
  else
    return *start;
}


/* Removes elem at index 'elem_pos' and maintains heap condition. */
static Edge *
pq_remove_elem (EdgePriorityQueue * pq, int elem_pos)
{
  assert (elem_pos >= 0);
  assert ((unsigned int) elem_pos < pq_count (pq));

#ifndef NDEBUG
#if QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM
  assert_pq_condition (pq);
#endif
#endif

  Edge *last, *del;
  Edge **pos = pq->elems_start + elem_pos;

  del = *pos;
  assert (del->pos == (unsigned int) elem_pos);
  del->pos = -1;

  --(pq->elems_top);
  last = *pq->elems_top;

  if (del != last)
    {
      *pos = last;
      last->pos = elem_pos;
      up_heap (pq, elem_pos);
      down_heap (pq, elem_pos);
    }

#ifndef NDEBUG
#if QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM
  assert_pq_condition (pq);
#endif
#endif

  return del;
}

/* -------------------- END: EDGE PRIORITY-QUEUE -------------------- */


/* -------------------- START: EDGE-HASHTABLE -------------------- */
static void
et_init (QDPLLMemMan * mm, EdgeTable * et, unsigned int size)
{
  size = size == 0 ? 1 : size;
  size_t bytes = size * sizeof (Edge *);
  et->table = (Edge **) qdpll_malloc (mm, bytes);
  et->size = size;
}


static void
et_delete (QDPLLMemMan * mm, EdgeTable * et)
{
  qdpll_free (mm, et->table, et->size * sizeof (Edge *));
}


static unsigned int
et_hash (VarID var)
{
  return var * 1183477;
}


static Edge **
et_findpos (EdgeTable * t, VarID var)
{
  assert (t);
  unsigned int h = et_hash (var);
  h &= (t->size - 1);

  Edge **p, *d;
  for (p = t->table + h; (d = *p) && d->head_var != var; p = &d->chain_next)
    ;

  return p;
}


static Edge *
et_lookup (EdgeTable * t, VarID var)
{
  assert (t);
  return *et_findpos (t, var);
}


static void
et_enlarge (QDPLLMemMan * mm, EdgeTable * t)
{
  assert (t);
  unsigned int old_size = t->size;
  unsigned int new_size = old_size ? old_size * 2 : 1;
  size_t bytes = new_size * sizeof (Edge *);
  Edge **new_table = (Edge **) qdpll_malloc (mm, bytes);

  Edge *p, *n;
  unsigned int i;
  for (i = 0; i < old_size; i++)
    for (p = t->table[i]; p; p = n)
      {
        n = p->chain_next;
        unsigned int h = et_hash (p->head_var);
        h &= (new_size - 1);
        p->chain_next = new_table[h];
        new_table[h] = p;
      }

  qdpll_free (mm, t->table, old_size * sizeof (Edge *));
  t->table = new_table;
  t->size = new_size;
}


static void
et_insert (QDPLLMemMan * mm, EdgeTable * t, Edge * d)
{
  assert (t);
  assert (!d->chain_next);

  if (t->count == t->size)
    et_enlarge (mm, t);

  Edge **p = et_findpos (t, d->head_var);
  assert (!*p);

  *p = d;
  t->count++;
}


static Edge *
et_remove (EdgeTable * t, VarID var)
{
  assert (t);
  Edge **p = et_findpos (t, var);
  Edge *result = *p;
  assert (result);
  *p = result->chain_next;
  result->chain_next = 0;
  t->count--;
  return result;
}

/* -------------------- END: EDGE-HASHTABLE -------------------- */


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


/* -------------------- START: ASSERTION-ONLY CODE -------------------- */

static void
assert_graph_check_edges_pq (Var * vars, Var * v, EdgePriorityQueue * edge_pq)
{
  Edge **d, **end;
  end = edge_pq->elems_top;
  for (d = edge_pq->elems_start; d < end; d++)
    {
      assert ((*d)->tail_var);
      assert ((*d)->head_var);
      assert ((*d)->head_var == v->id);
      Var *tv = VARID2VARPTR (vars, (*d)->tail_var);
      assert (edge_pq != &(v->GETQDAG (type).dedge_pq)
              || tv->scope->type != v->scope->type);
      assert (edge_pq == &(v->GETQDAG (type).dedge_pq)
              || tv->scope->type == v->scope->type);
      assert (tv->scope->nesting < v->scope->nesting);
      assert ((*d)->priority == tv->scope->nesting);
    }
}

static void
assert_graph_check_edges (Var * vars, Var * v, EdgeTable * edge_table)
{
  unsigned int i, end = edge_table->size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = edge_table->table[i]; d; d = d->chain_next)
      {
        assert (d->tail_var);
        assert (d->head_var);
        assert (d->tail_var == v->id);
        Var *hv = VARID2VARPTR (vars, d->head_var);
        assert (edge_table != &(v->GETQDAG (type).dedges)
                || hv->scope->type != v->scope->type);
        assert (edge_table == &(v->GETQDAG (type).dedges)
                || hv->scope->type == v->scope->type);
        assert (hv->scope->nesting > v->scope->nesting);
        assert (d->priority == v->scope->nesting);
      }
}


static void
assert_graph_integrity (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      VarID vid;
      Var *v;
      if (QDPLL_SCOPE_EXISTS (s))
        {
          for (vid = s->GETPART (type).classes[0].first; vid;
               vid = v->GETQDAG (type).uf[0].class_link.next)
            {
              v = VARID2VARPTR (vars, vid);

              assert (UF_IS_REP (v, 0, type));

              if (!UF_IS_SINGLETON_SET (v, 0, type))
                {
                  VarID mid;
                  Var *m;
                  for (mid = v->GETQDAG (type).uf[0].members.list.first; mid;
                       mid = m->GETQDAG (type).uf[0].members.link.next)
                    {
                      m = VARID2VARPTR (vars, mid);
                      assert (!UF_IS_REP (m, 0, type));
                      assert (!m->GETQDAG (type).cedges.cpar);
                      assert (!m->GETQDAG (type).cedges.cchilds.first
                              && !m->GETQDAG (type).cedges.cchilds.last);
                      assert (!m->GETQDAG (type).cedges.csibs.next
                              && !m->GETQDAG (type).cedges.csibs.prev);
                      assert (pq_count (&(m->GETQDAG (type).dedge_pq)) == 0);
                      assert (pq_count (&(m->GETQDAG (type).sedge_pq)) == 0);
                      assert_graph_check_edges (vars, m,
                                                &(m->GETQDAG (type).dedges));
                      assert_graph_check_edges (vars, m,
                                                &(m->GETQDAG (type).sedges));
                    }
                }
              else
                {
                  assert (v->GETQDAG (type).uf[0].members.list.first ==
                          v->GETQDAG (type).uf[0].members.list.last);
                  assert (v->GETQDAG (type).uf[0].members.list.first == vid);
                }

              assert (!v->GETQDAG (type).cedges.cpar
                      ||
                      UF_IS_REP (VARID2VARPTR
                                 (vars, v->GETQDAG (type).cedges.cpar), 0,
                                 type));
              assert (!v->GETQDAG (type).cedges.cpar
                      ||
                      (VARID2VARPTR
                       (vars,
                        v->GETQDAG (type).cedges.cpar)->scope->type ==
                       v->scope->type && QDPLL_SCOPE_EXISTS (v->scope)));
              assert (!v->GETQDAG (type).cedges.cpar
                      || VARID2VARPTR (vars,
                                       v->GETQDAG (type).cedges.cpar)->
                      scope->nesting < v->scope->nesting);
              assert (!v->GETQDAG (type).cedges.cpar
                      || (VARID2VARPTR (vars, v->GETQDAG (type).cedges.cpar)->
                          GETQDAG (type).cedges.cchilds.first
                          && VARID2VARPTR (vars,
                                           v->GETQDAG (type).cedges.
                                           cpar)->GETQDAG (type).cedges.
                          cchilds.last));

              VarID cid;
              Var *c;
              for (cid = v->GETQDAG (type).cedges.cchilds.first; cid;
                   cid = c->GETQDAG (type).cedges.csibs.next)
                {
                  c = VARID2VARPTR (vars, cid);
                  assert (UF_IS_REP (c, 0, type));
                  assert (v->scope->type == c->scope->type
                          && QDPLL_SCOPE_EXISTS (v->scope));
                  assert (v->scope->nesting < c->scope->nesting);
                  assert (vid == c->GETQDAG (type).cedges.cpar);
                }

              assert_pq_condition (&(v->GETQDAG (type).dedge_pq));

              if (v->GETQDAG (type).cedges.cpar
                  && pq_access_min (&(v->GETQDAG (type).dedge_pq)))
                {
                  assert (pq_access_min
                          (&(v->GETQDAG (type).dedge_pq))->priority >
                          VARID2VARPTR (vars,
                                        v->GETQDAG (type).cedges.cpar)->
                          scope->nesting);
                }

              assert_pq_condition (&(v->GETQDAG (type).sedge_pq));

              if (v->GETQDAG (type).cedges.cpar
                  && pq_access_min (&(v->GETQDAG (type).sedge_pq)))
                {
                  assert (pq_access_min
                          (&(v->GETQDAG (type).sedge_pq))->priority ==
                          VARID2VARPTR (vars,
                                        v->GETQDAG (type).cedges.cpar)->
                          scope->nesting);
                  Edge **d, **end = v->GETQDAG (type).sedge_pq.elems_top;
                  for (d = v->GETQDAG (type).sedge_pq.elems_start; d < end;
                       d++)
                    assert ((*d)->priority ==
                            VARID2VARPTR (vars,
                                          v->GETQDAG (type).cedges.cpar)->
                            scope->nesting);
                }

              assert_graph_check_edges (vars, v, &(v->GETQDAG (type).dedges));
              assert_graph_check_edges (vars, v, &(v->GETQDAG (type).sedges));
              assert_graph_check_edges_pq (vars, v,
                                           &(v->GETQDAG (type).dedge_pq));
              assert_graph_check_edges_pq (vars, v,
                                           &(v->GETQDAG (type).sedge_pq));
            }
        }
      else
        {
          assert (QDPLL_SCOPE_FORALL (s));
          for (vid = s->GETPART (type).classes[0].first; vid;
               vid = v->GETQDAG (type).uf[0].class_link.next)
            {
              v = VARID2VARPTR (vars, vid);
              assert (!v->GETQDAG (type).cedges.cpar);
              assert (!v->GETQDAG (type).cedges.csibs.next
                      && !v->GETQDAG (type).cedges.csibs.prev);
              assert (!v->GETQDAG (type).cedges.cchilds.first
                      && !v->GETQDAG (type).cedges.cchilds.last);

              assert (pq_count (&(v->GETQDAG (type).sedge_pq)) == 0);
              assert (v->GETQDAG (type).sedges.count == 0);
              assert_graph_check_edges (vars, v, &(v->GETQDAG (type).dedges));
              assert_graph_check_edges_pq (vars, v,
                                           &(v->GETQDAG (type).dedge_pq));

              if (!UF_IS_SINGLETON_SET (v, 0, type))
                {
                  VarID mid;
                  Var *m;
                  for (mid = v->GETQDAG (type).uf[0].members.list.first; mid;
                       mid = m->GETQDAG (type).uf[0].members.link.next)
                    {
                      m = VARID2VARPTR (vars, mid);
                      assert (!UF_IS_REP (m, 0, type));
                      assert (!m->GETQDAG (type).cedges.cpar);
                      assert (!m->GETQDAG (type).cedges.cchilds.first
                              && !m->GETQDAG (type).cedges.cchilds.last);
                      assert (!m->GETQDAG (type).cedges.csibs.next
                              && !m->GETQDAG (type).cedges.csibs.prev);
                      assert (pq_count (&(m->GETQDAG (type).dedge_pq)) == 0);
                      assert (pq_count (&(m->GETQDAG (type).sedge_pq)) == 0);
                      assert (m->GETQDAG (type).sedges.count == 0);
                      assert (m->GETQDAG (type).dedges.count == 0);
                    }
                }
              else
                {
                  assert (v->GETQDAG (type).uf[0].members.list.first ==
                          v->GETQDAG (type).uf[0].members.list.last);
                  assert (v->GETQDAG (type).uf[0].members.list.first == vid);
                }
            }
        }
    }
}


static void
assert_insert_c_edge_cchilds (Var * vars, Var * from, Var * to)
{
  assert (QDPLL_SCOPE_EXISTS (from->scope));
  assert (QDPLL_SCOPE_EXISTS (to->scope));
  Var *m;
  VarID mid;
  if (UF_IS_REP (from, 0, type))
    {
      assert (UF_IS_REP (to, 0, type) || !to->GETQDAG (type).cedges.cpar);
      assert (UF_IS_REP (to, 0, type)
              || (!to->GETQDAG (type).cedges.cchilds.first
                  && !to->GETQDAG (type).cedges.cchilds.last));

      if (!UF_IS_SINGLETON_SET (from, 0, type))
        for (mid = from->GETQDAG (type).uf[0].members.list.first; mid;
             mid = m->GETQDAG (type).uf[0].members.link.next)
          {
            m = VARID2VARPTR (vars, mid);
            assert (!UF_IS_REP (m, 0, type));
            assert (!m->GETQDAG (type).cedges.cpar);
            assert (!m->GETQDAG (type).cedges.cchilds.first
                    && !m->GETQDAG (type).cedges.cchilds.last);
          }
    }
  else
    {
      assert (!from->GETQDAG (type).cedges.cpar);
      assert (!from->GETQDAG (type).cedges.cchilds.first
              && !from->GETQDAG (type).cedges.cchilds.last);
    }

  if (UF_IS_REP (to, 0, type))
    {
      assert (UF_IS_REP (from, 0, type) || !from->GETQDAG (type).cedges.cpar);
      assert (UF_IS_REP (from, 0, type)
              || (!from->GETQDAG (type).cedges.cchilds.first
                  && !from->GETQDAG (type).cedges.cchilds.last));

      if (!UF_IS_SINGLETON_SET (to, 0, type))
        for (mid = to->GETQDAG (type).uf[0].members.list.first; mid;
             mid = m->GETQDAG (type).uf[0].members.link.next)
          {
            m = VARID2VARPTR (vars, mid);
            assert (!UF_IS_REP (m, 0, type));
            assert (!m->GETQDAG (type).cedges.cpar);
            assert (!m->GETQDAG (type).cedges.cchilds.first
                    && !m->GETQDAG (type).cedges.cchilds.last);
          }
    }
  else
    {
      assert (!to->GETQDAG (type).cedges.cpar);
      assert (!to->GETQDAG (type).cedges.cchilds.first
              && !to->GETQDAG (type).cedges.cchilds.last);
    }
}


static void
assert_c_edges_integrity (Var * vars, Var * start)
{
  assert (QDPLL_SCOPE_EXISTS (start->scope));
  Var *prev, *cur;
  VarID prev_id, cur_id;
  for (cur_id = prev_id = start->id; cur_id;
       cur_id = cur->GETQDAG (type).cedges.cpar)
    {
      cur = VARID2VARPTR (vars, cur_id);
      prev = VARID2VARPTR (vars, prev_id);
      assert (UF_IS_REP (cur, 0, type));
      assert (!
              (cur->GETQDAG (type).cedges.cpar
               && pq_access_min (&(cur->GETQDAG (type).dedge_pq)))
              || pq_access_min (&(cur->GETQDAG (type).dedge_pq))->priority >
              VARID2VARPTR (vars,
                            cur->GETQDAG (type).cedges.cpar)->scope->nesting);
      assert (!
              (cur->GETQDAG (type).cedges.cpar
               && pq_access_min (&(cur->GETQDAG (type).sedge_pq)))
              || pq_access_min (&(cur->GETQDAG (type).sedge_pq))->priority ==
              VARID2VARPTR (vars,
                            cur->GETQDAG (type).cedges.cpar)->scope->nesting);
      assert (prev == cur || cur->scope->nesting < prev->scope->nesting);
      assert (cur->scope->type == prev->scope->type);
      prev = cur;
    }
}

static void
collect_deps_from_cnf_check_clause (QDPLLDepManQDAG * dm,
                                    VarPtrStack * deps,
                                    VarPtrStack * con,
                                    QDPLLQuantifierType var_type,
                                    unsigned int var_nesting, Constraint * c);

static void
collect_deps_from_cnf (QDPLLDepManQDAG * dm, VarPtrStack * deps, Var * v);

static void
collect_deps_from_graph_forall (QDPLLDepManQDAG * dm, VarPtrStack * deps,
                                Var * v);

static void
collect_deps_from_graph_exists (QDPLLDepManQDAG * dm, VarPtrStack * deps,
                                Var * v);

static void
collect_deps_from_graph (QDPLLDepManQDAG * dm, VarPtrStack * deps, Var * v);

static int qsort_compare_deps_by_id (const void *dep1, const void *dep2);

static void unmark_dependency_marks (VarPtrStack * deps);

/* Check whether dependencies collected from graph match dependencies 
   collected by trivial approach (searching clauses in QBF). */
static void
assert_xcheck_dependencies (QDPLLDepManQDAG * dm)
{
  VarPtrStack deps_from_cnf;
  VarPtrStack deps_from_graph;
  QDPLL_INIT_STACK (deps_from_cnf);
  QDPLL_INIT_STACK (deps_from_graph);
  Var *vars = dm->pcnf->vars;

  /* Check that qdag-marks are all set to 0. */
  Var *p, *e;
  for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
    {
      assert (!p->GETQDAG (type).mark0);
      assert (!p->GETQDAG (type).mark1);
    }

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      VarID *p, *e;
      for (p = s->vars.start, e = s->vars.top; p < e; p++)
        {
          Var *v = VARID2VARPTR (vars, *p);
          assert (!QDPLL_VAR_MARKED_PROPAGATED (v));
          collect_deps_from_cnf (dm, &deps_from_cnf, v);
          unmark_dependency_marks (&deps_from_cnf);
          /* Note: connection marks have been reset already. */
          qsort (deps_from_cnf.start, QDPLL_COUNT_STACK (deps_from_cnf),
                 sizeof (*deps_from_cnf.start), qsort_compare_deps_by_id);

          collect_deps_from_graph (dm, &deps_from_graph, v);
          /* Note: connection marks have been reset already. */
          unmark_dependency_marks (&deps_from_graph);
          qsort (deps_from_graph.start, QDPLL_COUNT_STACK (deps_from_graph),
                 sizeof (*deps_from_graph.start), qsort_compare_deps_by_id);

          unsigned int cnt_deps_from_cnf = QDPLL_COUNT_STACK (deps_from_cnf);
          unsigned int cnt_deps_from_graph =
            QDPLL_COUNT_STACK (deps_from_graph);
          assert (cnt_deps_from_cnf == cnt_deps_from_graph);

          /* Traverse sorted stacks in parallel and compare collected dependencies. */
          Var **p1, **prev1, **p2, **prev2, **e1, **e2;
          for (p1 = prev1 = deps_from_cnf.start, e1 = deps_from_cnf.top,
               p2 = prev2 = deps_from_graph.start, e2 = deps_from_graph.top;
               p1 < e1; p1++, p2++)
            {
              assert (p2 < e2);
              assert ((*prev1)->id <= (*p1)->id);
              assert ((*prev2)->id <= (*p2)->id);
              assert (*p1 == *p2);
              prev1 = p1;
              prev2 = p2;
            }

          QDPLL_RESET_STACK (deps_from_cnf);
          QDPLL_RESET_STACK (deps_from_graph);
        }
    }

  QDPLL_DELETE_STACK (dm->mm, deps_from_cnf);
  QDPLL_DELETE_STACK (dm->mm, deps_from_graph);


  /* Check that qdag-marks are all set to 0. */
  for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
    {
      assert (!p->GETQDAG (type).mark0);
      assert (!p->GETQDAG (type).mark1);
    }
}


static void
assert_candidate_list (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;
  Var *c;
  VarID cid;
  for (cid = dm->candidates.first; cid;
       cid = c->GETQDAG (type).cand_link.next)
    {
      c = VARID2VARPTR (vars, cid);
      assert (c->GETQDAG (type).mark_is_candidate);
    }
}


static int referenced_by_active_existential_var (Var * vars, Var * var);


#ifndef NDEBUG

/* Similar to 'mark_non_candidates_from_exists', but uses other mark. */
static void
assert_mark_non_candidates_from_exists (QDPLLDepManQDAG * dm, Scope * scope)
{
  assert (QDPLL_SCOPE_EXISTS (scope));
  const QDPLLDepManType type = dm->dmg.type;
  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  VarPtrStack succ;
  QDPLL_INIT_STACK (succ);

  VarID *p, *e;
  for (p = scope->vars.start, e = scope->vars.top; p < e; p++)
    {
      Var *v = VARID2VARPTR (vars, *p);
      Var *v_rep = uf_find (vars, v, 1, type);

      unsigned int i, end = v_rep->GETQDAG (type).sedges.size;
      Edge *s;
      for (i = 0; i < end; i++)
        for (s = v_rep->GETQDAG (type).sedges.table[i]; s; s = s->chain_next)
          {
            Var *svar = VARID2VARPTR (vars, s->head_var);
            assert (s->tail_var == v_rep->id);
            assert (QDPLL_SCOPE_EXISTS (svar->scope));
            assert (v_rep->scope->nesting < svar->scope->nesting);
            assert (UF_IS_REP (svar, 0, type));
            QDPLL_PUSH_STACK (mm, succ, svar);
          }

      while (!QDPLL_EMPTY_STACK (succ))
        {
          Var *s = QDPLL_POP_STACK (succ);
          assert (QDPLL_SCOPE_EXISTS (s->scope));
          assert (UF_IS_REP (s, 0, type));

          Edge **p, **e;
          for (p = s->GETQDAG (type).dedge_pq.elems_start, e =
               s->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
            {
              Var *dvar = VARID2VARPTR (vars, (*p)->tail_var);
              assert (QDPLL_SCOPE_FORALL (dvar->scope));
              assert (v->scope->nesting < dvar->scope->nesting);
              assert (UF_IS_REP (dvar, 0, type));

              if (!dvar->GETQDAG (type).mark_is_candidate_debug
                  && referenced_by_active_existential_var (vars, dvar))
                {
                  dvar->GETQDAG (type).mark_is_candidate_debug = 1;

                  if (!UF_IS_SINGLETON_SET (dvar, 0, type))
                    {
                      Var *m;
                      VarID mid;
                      for (mid =
                           dvar->GETQDAG (type).uf[0].members.list.first; mid;
                           mid = m->GETQDAG (type).uf[0].members.link.next)
                        {
                          m = VARID2VARPTR (vars, mid);
                          assert (!m->GETQDAG (type).mark_is_candidate_debug);
                          m->GETQDAG (type).mark_is_candidate_debug = 1;
                        }
                    }
                }
            }

          Var *c;
          VarID cid;
          for (cid = s->GETQDAG (type).cedges.cchilds.first; cid;
               cid = c->GETQDAG (type).cedges.csibs.next)
            {
              c = VARID2VARPTR (vars, cid);
              QDPLL_PUSH_STACK (mm, succ, c);
            }
        }
    }

  QDPLL_DELETE_STACK (mm, succ);
}

static unsigned int count_non_propagated_in_class (Var * vars, Var * v,
                                                   const unsigned int offset);

/* Similar to 'mark_non_candidates_from_forall', but uses other mark. */
static void
assert_mark_non_candidates_from_forall (QDPLLDepManQDAG * dm, Scope * s)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;
  VarPtrStack forest_succ;
  QDPLL_INIT_STACK (forest_succ);
  assert (QDPLL_SCOPE_FORALL (s));

  Var *v;
  VarID vid;
  for (vid = s->GETPART (type).classes[0].first; vid;
       vid = v->GETQDAG (type).uf[0].class_link.next)
    {
      v = VARID2VARPTR (vars, vid);
      assert (UF_IS_REP (v, 0, type));
      assert (QDPLL_SCOPE_FORALL (v->scope));

      /* If class is fully propagated (and hence assigned), then skip. */
      if (count_non_propagated_in_class (vars, v, 0) == 0)
        continue;

      /* Mark and push d-edges on traversal stack. */
      unsigned int i, end = v->GETQDAG (type).dedges.size;
      Edge *d;
      for (i = 0; i < end; i++)
        for (d = v->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
          {
            Var *dvar = VARID2VARPTR (vars, d->head_var);
            assert (QDPLL_SCOPE_EXISTS (dvar->scope));
            assert (UF_IS_REP (dvar, 0, type));
            assert (v->scope->nesting < dvar->scope->nesting);

            if (!dvar->GETQDAG (type).mark_is_candidate_debug)
              {
                dvar->GETQDAG (type).mark_is_candidate_debug = 1;
                QDPLL_PUSH_STACK (mm, forest_succ, dvar);
              }
          }

      while (!QDPLL_EMPTY_STACK (forest_succ))
        {
          Var *succ = QDPLL_POP_STACK (forest_succ);
          assert (QDPLL_SCOPE_EXISTS (succ->scope));
          assert (v->scope->nesting < succ->scope->nesting);
          assert (UF_IS_REP (succ, 0, type));
          assert (succ->GETQDAG (type).mark_is_candidate_debug);

          if (!UF_IS_SINGLETON_SET (succ, 0, type))
            {
              /* Mark class members. */
              Var *m;
              VarID mid;
              for (mid = succ->GETQDAG (type).uf[0].members.list.first; mid;
                   mid = m->GETQDAG (type).uf[0].members.link.next)
                {
                  m = VARID2VARPTR (vars, mid);
                  m->GETQDAG (type).mark_is_candidate_debug = 1;
                }
            }

          /* Mark and push all c-children not yet marked. */
          Var *c;
          VarID cid;
          for (cid = succ->GETQDAG (type).cedges.cchilds.first; cid;
               cid = c->GETQDAG (type).cedges.csibs.next)
            {
              c = VARID2VARPTR (vars, cid);
              if (!c->GETQDAG (type).mark_is_candidate_debug)
                {
                  c->GETQDAG (type).mark_is_candidate_debug = 1;
                  QDPLL_PUSH_STACK (mm, forest_succ, c);
                }
            }
        }
    }

  QDPLL_DELETE_STACK (mm, forest_succ);
}


static void
assert_candidate_marks_by_remarking (QDPLLDepManQDAG * dm)
{
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;

  Var *p, *e;
  for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
    assert (!p->GETQDAG (type).mark_is_candidate_debug);

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      if (QDPLL_SCOPE_EXISTS (s))
        assert_mark_non_candidates_from_exists (dm, s);
      else
        {
          assert (QDPLL_SCOPE_FORALL (s));
          assert_mark_non_candidates_from_forall (dm, s);
        }
    }

  /* Compare marks for all variables. */
  for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
    {
      if (p->id)
        {
          assert (!p->GETQDAG (type).mark_is_candidate_debug
                  || !p->GETQDAG (type).mark_is_candidate);
          assert (p->GETQDAG (type).mark_is_candidate
                  || p->GETQDAG (type).mark_is_candidate_debug);
          p->GETQDAG (type).mark_is_candidate_debug = 0;
        }
    }
}

static unsigned int count_direct_active_refs_by_sedge (Var * vars, Var * var);

static void
assert_inactive_sedge_frontier_by_ancestors (QDPLLDepManQDAG * dm, Var * var)
{
  assert (var);
  assert (QDPLL_SCOPE_EXISTS (var->scope));
  assert (UF_IS_REP (var, 0, type));
  Var *vars = dm->pcnf->vars;

  VarID parid = var->id;
  Var *par;
  while (parid)
    {
      par = VARID2VARPTR (vars, parid);
      assert (QDPLL_SCOPE_EXISTS (par->scope));
      assert (UF_IS_REP (par, 0, type));
      assert (par->GETQDAG (type).cnt.exists.inactive_sedge_frontier);
      assert (par->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
              0);
      assert (count_direct_active_refs_by_sedge (vars, par) == 0);

      Edge **p, **e;
      for (p = par->GETQDAG (type).dedge_pq.elems_start,
           e = par->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
        {
          Var *u = VARID2VARPTR (vars, (*p)->tail_var);
          assert (QDPLL_SCOPE_FORALL (u->scope));
          assert (UF_IS_REP (u, 0, type));
        }

      parid = par->GETQDAG (type).cedges.cpar;
    }
}

static int qdpll_dep_man_depends (QDPLLDepManGeneric * dmg, VarID x, VarID y);

static void
assert_check_deps_by_functions_in_clause (QDPLLDepManQDAG * dm,
                                          Constraint * c)
{
  assert (!c->is_cube);
  Var *vars = dm->pcnf->vars;

  LitID *p, *tmp, *e = c->lits + c->num_lits - 1;
  for (p = c->lits; p <= e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      if (QDPLL_VAR_MARKED_PROPAGATED (var)
          && var->decision_level <= 0)
        continue;
      for (tmp = c->lits; tmp <= e; tmp++)
        {
          LitID lit_tmp = *tmp;
          Var *var_tmp = LIT2VARPTR (vars, lit_tmp);
          assert (!(QDPLL_VAR_MARKED_PROPAGATED (var_tmp)
                   && var_tmp->decision_level <= 0));
          if (QDPLL_VAR_MARKED_PROPAGATED (var_tmp)
              && var_tmp->decision_level <= 0)
            continue;
          if (tmp <= p || var->scope->type == var_tmp->scope->type)
            assert (!qdpll_dep_man_depends
                    ((QDPLLDepManGeneric *) dm, var->id, var_tmp->id));
          else
            assert (qdpll_dep_man_depends
                    ((QDPLLDepManGeneric *) dm, var->id, var_tmp->id));
        }
    }
}


static void
assert_check_dependencies_by_functions (QDPLLDepManQDAG * dm)
{
  Constraint *c;
  for (c = dm->pcnf->clauses.first; c; c = c->link.next)
    {
      assert (!c->is_cube);
      assert (!c->learnt);
      if (c->num_lits > 1)
        assert_check_deps_by_functions_in_clause (dm, c);
    }
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
assert_lits_no_holes (LitID * lit_start, LitID * lit_end)
{
  LitID *p, *e;
  for (p = lit_start, e = lit_end; p < e; p++)
    assert (*p);
}

static unsigned int
count_direct_active_refs_by_exist_var (Var * vars, Var * v);

/* Function is very similar to the one for checking references to
   existential classes from universal classes. We could use use one
   common function if we merged existential classes in the same way as we
   do with universal one, i.e. by d-edge sets. But this would require to
   maintain a separate partition different from the one based on variable
   connections. */
static int
referenced_by_active_existential_var (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_FORALL (v->scope));
  assert (UF_IS_REP (v, 0, type));
  assert (count_direct_active_refs_by_exist_var (vars, v) ==
          v->GETQDAG (type).cnt.forall.active_direct_refs_by_exist_var);

  if (v->GETQDAG (type).cnt.forall.active_direct_refs_by_exist_var != 0)
    return 1;

  /* Check if 'v' is indirectly referenced by removed transitive edge. */
  unsigned int i, end = v->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = v->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
      {
        Var *dvar = VARID2VARPTR (vars, d->head_var);
        assert (QDPLL_SCOPE_EXISTS (dvar->scope));
        assert (UF_IS_REP (dvar, 0, type));

        Var *par;
        VarID parid = dvar->id;

        while (parid)
          {
            par = VARID2VARPTR (vars, parid);
            assert (QDPLL_SCOPE_EXISTS (dvar->scope));
            assert (UF_IS_REP (dvar, 0, type));

            /* Check s-edges of 'par'. */
            Edge **p, **e;
            for (p = par->GETQDAG (type).sedge_pq.elems_start,
                 e = par->GETQDAG (type).sedge_pq.elems_top; p < e; p++)
              {
                Edge *s = *p;
                Var *svar = VARID2VARPTR (vars, s->tail_var);
                assert (QDPLL_SCOPE_EXISTS (svar->scope));
                assert (UF_IS_REP (svar, 1, type));
                if (count_non_propagated_in_class (vars, svar, 1) != 0)
                  return 1;
              }

            parid = par->GETQDAG (type).cedges.cpar;
          }
      }

  return 0;
}


static int
is_lit_on_lit_stack (LitIDStack * stack, LitID lit)
{
  LitID *p, *e;
  for (p = stack->start, e = stack->top; p < e; p++)
    {
      assert (*p);
      if (*p == lit)
        return 1;
    }
  return 0;
}

#endif

/* -------------------- END: ASSERTION-ONLY CODE -------------------- */


/* -------------------- START: INTERNAL FUNCTIONS -------------------- */

static int
compare_lits_by_variable_nesting (QDPLL * qdpll, LitID lit1, LitID lit2)
{
  /* We should never call this function in this module since sorting is too
     costly. */
  QDPLL_ABORT_DEPMAN (1, "reached expected dead code!");

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


static void
delete_edge (QDPLLMemMan * mm, Edge * d)
{
  qdpll_free (mm, d, sizeof (Edge));
}


static Edge *
create_edge (QDPLLMemMan * mm)
{
  Edge *result;
  size_t bytes = sizeof (Edge);
  result = (Edge *) qdpll_malloc (mm, bytes);
  return result;
}

#define HAS_EDGE(from, to, table) (et_lookup (&((from)->table), to))

/* Re-link all c-children of 'oldpar' to 'newpar', set pointers appropriately.
   This is required when existential classes are merged during insertion of c-edges. */
static void
fix_cchilds (Var * vars, Var * oldpar, Var * newpar, Var * oldparpar)
{
  Var *c;
  VarID cid, nid;
  for (cid = (oldpar)->GETQDAG (type).cedges.cchilds.first; cid; cid = nid)
    {
      c = VARID2VARPTR (vars, cid);
      nid = c->GETQDAG (type).cedges.csibs.next;
      VAR_UNLINK (vars, oldpar->GETQDAG (type).cedges.cchilds, c,
                  GETQDAG (type).cedges.csibs);
      VAR_LINK (vars, newpar->GETQDAG (type).cedges.cchilds, c,
                GETQDAG (type).cedges.csibs);
      c->GETQDAG (type).cedges.cpar = newpar->id;
    }
  if (oldparpar)
    {
      VAR_UNLINK (vars, oldparpar->GETQDAG (type).cedges.cchilds, oldpar,
                  GETQDAG (type).cedges.csibs);
      oldpar->GETQDAG (type).cedges.cpar = 0;
    }
}


#define SWAP(v1, v2)                                  \
  do {                                                \
    Var *tmp;                                         \
    tmp = v1;                                         \
    v1 = v2;                                          \
    v2 = tmp;                                         \
  } while (0)


#define FIX_EDGE_PQS(vars, from, to, table, pq)                       \
  do {                                                                \
    assert (from->id != to);                                          \
    Edge *e;                                                          \
    Var *tail_var;                                                    \
    while ((e = pq_remove_one (&(from)->pq)))                          \
      {                                                                \
        tail_var = VARID2VARPTR(vars, e->tail_var);                    \
        et_remove (&(tail_var->table), from->id);                      \
        assert (tail_var->scope->nesting == e->priority);              \
        assert (e->head_var == from->id);                               \
        assert (e->priority < from->scope->nesting);                    \
        assert (e->priority < VARID2VARPTR(vars, (to))->scope->nesting); \
                                                                        \
        if (!HAS_EDGE(tail_var, to, table))                             \
          {                                                             \
            e->head_var = to;                                           \
            pq_insert (mm, &(VARID2VARPTR(vars, (to))->pq), e, e->priority); \
            et_insert(mm, &(tail_var->table), e);                       \
          }                                                             \
        else                                                            \
          {                                                             \
            delete_edge(mm, e);                                         \
          }                                                             \
      }                                                                 \
  } while (0)


#define UPSHIFT_EDGES(vars, v, table, pq)                               \
  do {                                                                  \
    assert (UF_IS_REP (v,0,type));                                      \
    Edge *e;                                                            \
    Var *cpar, *cur, *prev, *edge_from, *v_tmp = v;                        \
    VarID cparid;                                                       \
    unsigned int en;                                                    \
    while ((cparid = v_tmp->GETQDAG(type).cedges.cpar) &&               \
           (cpar = VARID2VARPTR(vars, cparid)))                         \
      {                                                                 \
        assert (!(e = pq_access_min(&(v_tmp->pq)))                      \
                || (en = VARID2VARPTR(vars, e->tail_var)->scope->nesting) == e->priority); \
                                                                        \
        while ((e = pq_access_min (&(v_tmp->pq))) &&                    \
               (en = e->priority) < cpar->scope->nesting)               \
          {                                                             \
            e = pq_remove_min (&(v_tmp->pq));                           \
            edge_from = VARID2VARPTR(vars, e->tail_var);                \
            assert (v_tmp == VARID2VARPTR(vars, e->head_var));          \
            assert (edge_from->scope->nesting == en);                   \
            et_remove (&(edge_from->table), v_tmp->id);                 \
                                                                        \
            cur = prev = cpar;                                          \
                                                                        \
            while ((cparid = cur->GETQDAG(type).cedges.cpar) &&         \
                   (cur = VARID2VARPTR(vars, cparid)) &&                \
                   en < cur->scope->nesting)                            \
              {                                                         \
                prev = cur;                                             \
              }                                                         \
                                                                        \
            if (!HAS_EDGE (edge_from, prev->id, table))                 \
              {                                                         \
                e->head_var = prev->id;                                 \
                pq_insert (mm, &(prev->pq), e, en);                        \
                et_insert (mm, &(edge_from->table), e);                 \
              }                                                         \
            else                                                        \
              {                        /* delete d-edge (is already removed from pq) */ \
                delete_edge (mm, e);                                    \
              }                                                         \
          }                                                             \
                                                                        \
        v_tmp = cpar;                                                   \
      }                                                                 \
  } while (0)


static Var *
balance (Var * vars, Var * v1, Var ** v2)
{
  Var *p, *b, *prev;
  prev = b = *v2;
  const unsigned int nesting = v1->scope->nesting;
  assert (nesting <= b->scope->nesting);
  VarID cpar;

  while ((cpar = b->GETQDAG (type).cedges.cpar)
         && (p = VARID2VARPTR (vars, cpar)) && p->scope->nesting >= nesting)
    {
      prev = b;
      b = p;
    }

  *v2 = b;

  assert (v1);
  assert (*v2);
  assert ((v1)->scope->nesting <= (*v2)->scope->nesting);
  assert (!(*v2)->GETQDAG (type).cedges.cpar ||
          VARID2VARPTR (vars,
                        (*v2)->GETQDAG (type).cedges.cpar)->scope->nesting <
          (v1)->scope->nesting);

  assert (prev == *v2 || prev->scope->nesting > (*v2)->scope->nesting);

  return prev;
}


static void
insert_edge_aux (QDPLLMemMan * mm, Var * from, Var * to)
{
  assert (UF_IS_REP (to, 0, type));
  EdgeTable *et;
  EdgePriorityQueue *pq;
  if (QDPLL_SCOPE_FORALL (from->scope))
    {
      /* Inserting a d-edge. */
      et = &(from->GETQDAG (type).dedges);
      pq = &(to->GETQDAG (type).dedge_pq);
    }
  else
    {
      /* Inserting an s-edge. */
      et = &(from->GETQDAG (type).sedges);
      pq = &(to->GETQDAG (type).sedge_pq);
    }

  if (!et_lookup (et, to->id))
    {
      Edge *edge;
      edge = create_edge (mm);
      edge->tail_var = from->id;
      edge->head_var = to->id;
      pq_insert (mm, pq, edge, from->scope->nesting);
      et_insert (mm, et, edge);
    }
}


/* Insertion of either d-edge or s-edge from variable 'from' to variable 'to'. 
   Edges in c-forest are handled in function 'insert_c_edge'.*/
static void
insert_edge (QDPLLDepManQDAG * dm, Var * from, Var * to)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;
  assert (QDPLL_SCOPE_EXISTS (to->scope));
  assert (UF_IS_REP (to, 0, type));
  assert (!QDPLL_SCOPE_FORALL (from->scope)
          || dm->dmg.type == QDPLL_DEPMAN_TYPE_SIMPLE
          || (UF_IS_REP (from, 0, type)
              && UF_IS_SINGLETON_SET (from, 0, type)));
  assert (!QDPLL_SCOPE_FORALL (from->scope)
          || from->scope->type != to->scope->type);
  assert (from->scope->nesting < to->scope->nesting);

  if (QDPLL_SCOPE_FORALL (from->scope))
    balance (vars, from, &to);
  else
    to = balance (vars, from, &to);

  assert (!QDPLL_SCOPE_FORALL (from->scope)
          || from->scope->type != to->scope->type);
  assert (from->scope->nesting < to->scope->nesting);

  insert_edge_aux (mm, from, to);
}


static void
insert_c_edge (QDPLLDepManQDAG * dm, Var * from, Var * to,
               const QDPLLDepManType type)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;
#ifndef NDEBUG
  assert (UF_IS_REP (from, 0, type));
  assert (UF_IS_REP (to, 0, type));
  assert (QDPLL_SCOPE_EXISTS (from->scope));
  assert (QDPLL_SCOPE_EXISTS (to->scope));
  assert (from->scope->type == to->scope->type);
  assert (from->scope->nesting <= to->scope->nesting);
  Var *old_to = to;
#if QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_BEFORE
  assert_c_edges_integrity (vars, to);
  assert_c_edges_integrity (vars, from);
#endif
#endif
  Var *start_to;

  /* check if 'from' is predecessor of 'to' */
  balance (vars, from, &to);
  if (from == to)
    return;

  start_to = to;

  VarID next_to_id, tmp1_id;
  Var *next_to, *tmp1;
  while (from)
    {
      assert (from->scope->nesting <= to->scope->nesting);
      assert (UF_IS_REP (from, 0, type));
      assert (UF_IS_REP (to, 0, type));
      assert (from->scope->type == to->scope->type);

      balance (vars, from, &to);
      assert (from->scope->nesting <= to->scope->nesting);

      if (from == to)
        break;

#ifndef NDEBUG
#if QDAG_ASSERT_INSERT_C_EDGE_CCHILDS
      assert_insert_c_edge_cchilds (vars, from, to);
#endif
#endif

      next_to = (next_to_id = to->GETQDAG (type).cedges.cpar) ?
        VARID2VARPTR (vars, next_to_id) : 0;

      if (from->scope == to->scope)
        {
          tmp1 = (tmp1_id = from->GETQDAG (type).cedges.cpar) ?
            VARID2VARPTR (vars, tmp1_id) : 0;

          uf_unite (vars, from, to, 0, type);
          assert ((!UF_IS_REP (from, 0, type) && UF_IS_REP (to, 0, type)) ||
                  (UF_IS_REP (from, 0, type) && !UF_IS_REP (to, 0, type)));

          if (UF_IS_REP (from, 0, type))
            {
              fix_cchilds (vars, to, from, next_to);
              FIX_EDGE_PQS (vars, to, from->id, GETQDAG (type).dedges,
                            GETQDAG (type).dedge_pq);
              FIX_EDGE_PQS (vars, to, from->id, GETQDAG (type).sedges,
                            GETQDAG (type).sedge_pq);
            }
          else
            {
              assert (UF_IS_REP (to, 0, type));
              fix_cchilds (vars, from, to, tmp1);
              FIX_EDGE_PQS (vars, from, to->id, GETQDAG (type).dedges,
                            GETQDAG (type).dedge_pq);
              FIX_EDGE_PQS (vars, from, to->id, GETQDAG (type).sedges,
                            GETQDAG (type).sedge_pq);
              next_to = tmp1;
              SWAP (from, to);
            }
        }
      else
        {
          assert (from->scope->nesting < to->scope->nesting);
          if (next_to)
            {
              assert (VARID2VARPTR (vars, to->GETQDAG (type).cedges.cpar) ==
                      next_to);
              VAR_UNLINK (vars, next_to->GETQDAG (type).cedges.cchilds, to,
                          GETQDAG (type).cedges.csibs);
            }
          else
            assert (!to->GETQDAG (type).cedges.csibs.next
                    && !to->GETQDAG (type).cedges.csibs.prev);
          to->GETQDAG (type).cedges.cpar = from->id;
          VAR_LINK (vars, from->GETQDAG (type).cedges.cchilds, to,
                    GETQDAG (type).cedges.csibs);
        }

#ifndef NDEBUG
#if QDAG_ASSERT_INSERT_C_EDGE_CCHILDS
      assert_insert_c_edge_cchilds (vars, from, to);
#endif
#endif

      to = from;
      from = next_to;
    }

  assert (start_to->GETQDAG (type).uf[0].par);
  start_to = uf_find (vars, start_to, 0, type);
  UPSHIFT_EDGES (vars, start_to, GETQDAG (type).dedges,
                 GETQDAG (type).dedge_pq);
  UPSHIFT_EDGES (vars, start_to, GETQDAG (type).sedges,
                 GETQDAG (type).sedge_pq);
#ifndef NDEBUG
#if QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_AFTER
  assert_c_edges_integrity (vars, uf_find (vars, old_to, 0, type));
#endif
#endif
}

static LitID *
find_next_lit_from_other_scope (Var * vars, LitID * lits, LitID * lit)
{
  assert (lit);
  assert (lits <= lit);

  Var *var = 0;
  Scope *s = LIT2VARPTR (vars, (*lit))->scope;
  for (lit = lit - 1;
       lits <= lit &&
       ((var = LIT2VARPTR (vars, (*lit)))->scope == s ||
        (QDPLL_VAR_MARKED_PROPAGATED (var)
         && var->decision_level <= 0)); lit--);

  return lit;
}

static void
extract_dependencies_from_lits (QDPLLDepManQDAG * dm, LitID * lits,
                                unsigned int num_lits)
{
  const QDPLLDepManType type = dm->dmg.type;
  Var *vars = dm->pcnf->vars;

  /* Unit/empty clauses do not generate dependencies, can return immediately. */
  if (num_lits <= 1)
    return;

  LitID *leftlit_p, *rightlit_p, *tmp_p, *last_e_p = 0, *prev_p = 0;

  /* Start at last (biggest) literal of clause. */
  rightlit_p = lits + num_lits - 1;
  assert (lits <= rightlit_p);
  assert (QDPLL_SCOPE_EXISTS (LIT2VARPTR (vars, *rightlit_p)->scope));
  assert (lits <= rightlit_p);
  assert (QDPLL_SCOPE_EXISTS (LIT2VARPTR (vars, *rightlit_p)->scope));
  assert (!(QDPLL_VAR_MARKED_PROPAGATED (LIT2VARPTR (vars, *rightlit_p)) &&
            LIT2VARPTR (vars, *rightlit_p)->decision_level <= 0));

  /* Extraction loop. */
  while (lits <= rightlit_p)
    {
      leftlit_p =
        find_next_lit_from_other_scope (vars, lits, rightlit_p);
      assert (leftlit_p < rightlit_p);
      assert (lits <= leftlit_p || leftlit_p == lits - 1);
      assert (leftlit_p < lits
              || (LIT2VARPTR (vars, *leftlit_p)->scope->nesting <
                  LIT2VARPTR (vars, *rightlit_p)->scope->nesting &&
                  !(QDPLL_VAR_MARKED_PROPAGATED
                    (LIT2VARPTR (vars, *leftlit_p))
                    && LIT2VARPTR (vars,
                                   *leftlit_p)->decision_level <= 0)));

      if (QDPLL_SCOPE_EXISTS (LIT2VARPTR (vars, *rightlit_p)->scope))
        {
          tmp_p = rightlit_p - 1;
          /* Unite adjacent existential literals from same scope. */
          while (leftlit_p < tmp_p)
            {
              assert (lits <= tmp_p);
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED (LIT2VARPTR (vars, *tmp_p))
                       && LIT2VARPTR (vars,
                                      *tmp_p)->decision_level <= 0));
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED
                       (LIT2VARPTR (vars, *rightlit_p))
                       && LIT2VARPTR (vars,
                                      *rightlit_p)->decision_level <= 0));
              Var *rep_tmp =
                uf_find (vars, LIT2VARPTR (vars, *tmp_p), 0, type);
              Var *rep_right =
                uf_find (vars, LIT2VARPTR (vars, *rightlit_p), 0, type);
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED (rep_tmp)
                       && rep_tmp->decision_level <= 0));
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED (rep_right)
                       && rep_right->decision_level <= 0));

#ifndef NDEBUG
#if QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_BEFORE
              assert_insert_c_edge_cchilds (vars, LIT2VARPTR (vars, *tmp_p),
                                            LIT2VARPTR (vars, *rightlit_p));
              assert_insert_c_edge_cchilds (vars, rep_tmp, rep_right);
#endif
#endif
              insert_c_edge (dm, rep_tmp, rep_right, type);

#ifndef NDEBUG
#if QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_AFTER
              assert_insert_c_edge_cchilds (vars,
                                            uf_find (vars, rep_tmp, 0, type),
                                            uf_find (vars, rep_right, 0,
                                                     type));
#endif
#endif
              rightlit_p = tmp_p--;
            }
        }
      else
        {
          rightlit_p = leftlit_p + 1;
        }

      assert (rightlit_p == leftlit_p + 1);
      assert (!last_e_p
              || !(QDPLL_VAR_MARKED_PROPAGATED (LIT2VARPTR (vars, *last_e_p))
                   && LIT2VARPTR (vars,
                                  *last_e_p)->decision_level <= 0));
      assert (!last_e_p
              ||
              !(QDPLL_VAR_MARKED_PROPAGATED
                (uf_find (vars, LIT2VARPTR (vars, *last_e_p), 0, type))
                && uf_find (vars,
                            LIT2VARPTR (vars,
                                        *last_e_p), 0,
                            type)->decision_level <= 0));

      /* POSSIBLE OPTIMIZATION: suffices to balance once, can then re-use insert-position for all vars from same scope */

      if (QDPLL_SCOPE_EXISTS (LIT2VARPTR (vars, *rightlit_p)->scope))
        {
          assert (!
                  (QDPLL_VAR_MARKED_PROPAGATED
                   (LIT2VARPTR (vars, *rightlit_p))
                   && LIT2VARPTR (vars,
                                  *rightlit_p)->decision_level <= 0));
          if (last_e_p)
            {
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED
                       (uf_find
                        (vars, LIT2VARPTR (vars, *rightlit_p), 0, type))
                       && uf_find (vars, LIT2VARPTR (vars, *rightlit_p), 0,
                                   type)->decision_level <= 0));
              insert_c_edge (dm,
                             uf_find (vars, LIT2VARPTR (vars, *rightlit_p), 0,
                                      type), uf_find (vars, LIT2VARPTR (vars,
                                                                        *last_e_p),
                                                      0, type), type);

              tmp_p = rightlit_p;
              assert (tmp_p < prev_p);
              do
                {
                  assert (!
                          (QDPLL_VAR_MARKED_PROPAGATED
                           (LIT2VARPTR (vars, *tmp_p))
                           && LIT2VARPTR (vars,
                                          *tmp_p)->decision_level <= 0));
                  insert_edge (dm, LIT2VARPTR (vars, *tmp_p), uf_find (vars, LIT2VARPTR (vars, *last_e_p), 0, type));
                  tmp_p++;
                }
              while (tmp_p < prev_p);

            }
          last_e_p = rightlit_p;
        }
      else
        {
          assert (QDPLL_SCOPE_FORALL (LIT2VARPTR (vars, *rightlit_p)->scope));
          assert (last_e_p);
          tmp_p = rightlit_p;
          assert (tmp_p < prev_p);
          do
            {
              assert (!
                      (QDPLL_VAR_MARKED_PROPAGATED (LIT2VARPTR (vars, *tmp_p))
                       && LIT2VARPTR (vars,
                                      *tmp_p)->decision_level <= 0));
              insert_edge (dm, LIT2VARPTR (vars, *tmp_p), uf_find (vars, LIT2VARPTR (vars, *last_e_p), 0, type));
              tmp_p++;
            }
          while (tmp_p < prev_p);
        }

      prev_p = rightlit_p;
      rightlit_p = leftlit_p;
    }
}


/* New code for removing transitive dependencies. Apply explicit search if 
   suspected transtive dependencies are reachable. */
static int
remove_transitivities (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;
  int removed_edges = 0;
  VarPtrStack stack;
  VarPtrStack marks;
  QDPLL_INIT_STACK (stack);
  QDPLL_INIT_STACK (marks);

#ifndef NDEBUG
#if QDAG_ASSERT_REMOVE_TRANSITIVITIES_VARS_UNMARKED
  /* Check that qdag-marks are all set to 0. */
  do
    {
      Var *p, *e;
      for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
        {
          assert (!p->GETQDAG (type).mark0);
          assert (!p->GETQDAG (type).mark1);
        }
    }
  while (0);
#endif
#endif

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      if (QDPLL_SCOPE_FORALL (s))
        continue;
      assert (QDPLL_SCOPE_EXISTS (s));

      /* Check all existential variables. */
      VarID *vidp, *vide, vid;
      for (vidp = s->vars.start, vide = s->vars.top; vidp < vide; vidp++)
        {
          vid = *vidp;
          Var *v = VARID2VARPTR (vars, vid);
          assert (QDPLL_SCOPE_EXISTS (v->scope));
          /* Check if dependency 'vtd_tmp_var' of variable 'v' is reachable from 
             other dependencies of 'v' by following dependency pointers. 
             If so, then remove 'vtd_tmp_var', which is transitive in this case. */
          Edge *vtd_tmp, *vtd_tmp_next;
          Var *vtd_tmp_var;
          VarID vtd_tmp_varid;
          unsigned int i, end;
          end = v->GETQDAG (type).dedges.size;
          for (i = 0; i < end; i++)
            for (vtd_tmp = v->GETQDAG (type).dedges.table[i]; vtd_tmp;
                 vtd_tmp = vtd_tmp_next)
              {
                vtd_tmp_next = vtd_tmp->chain_next;
                assert (VARID2VARPTR (vars, vtd_tmp->tail_var) == v);
                vtd_tmp_varid = vtd_tmp->head_var;
                vtd_tmp_var = VARID2VARPTR (vars, vtd_tmp_varid);
                unsigned int vtd_tmp_var_nesting =
                  vtd_tmp_var->scope->nesting;
                assert (UF_IS_REP (vtd_tmp_var, 0, type));
                assert (QDPLL_SCOPE_FORALL (vtd_tmp_var->scope));

                /* Push other dependencies of 'v' on traversal stack. */
                Edge *d;
                unsigned int j;
                for (j = 0; j < end; j++)
                  for (d = v->GETQDAG (type).dedges.table[j]; d;
                       d = d->chain_next)
                    {
                      if (d == vtd_tmp)
                        continue;

                      Var *dvar = VARID2VARPTR (vars, d->head_var);
                      assert (QDPLL_SCOPE_FORALL (dvar->scope));
                      assert (UF_IS_REP (dvar, 0, type));
                      /* Note: suffices to push dependencies of 
                         representative of universal class. */

                      /* Ignore variables larger than 'vtd_tmp_var', 
                         can not reach 'vtd_tmp_var' from such variables. */
                      if (dvar->scope->nesting < vtd_tmp_var_nesting)
                        {
                          QDPLL_PUSH_STACK (mm, stack, dvar);
                          assert (!dvar->GETQDAG (type).mark0);
                          dvar->GETQDAG (type).mark0 = 1;
                          QDPLL_PUSH_STACK (mm, marks, dvar);
                        }
                    }

                /* Follow dependency pointers on stack, 
                   check if 'vtd_tmp_var' is reachable. */
                while (!QDPLL_EMPTY_STACK (stack))
                  {
                    Var *tmp = QDPLL_POP_STACK (stack);
                    assert (tmp->GETQDAG (type).mark0);
                    assert (QDPLL_SCOPE_EXISTS (tmp->scope)
                            || UF_IS_REP (tmp, 0, type));
                    assert (tmp->scope->nesting < vtd_tmp_var_nesting);

                    if (QDPLL_SCOPE_EXISTS (tmp->scope)
                        && HAS_EDGE (tmp, vtd_tmp_varid,
                                     GETQDAG (type).dedges))
                      {
                        /* Remove edge from 'v' to 'vtd_tmp_var'. */
#ifndef NDEBUG
                        Edge *del =
                          pq_remove_elem (&
                                          (vtd_tmp_var->
                                           GETQDAG (type).dedge_pq),
vtd_tmp->pos);
                        assert (del == vtd_tmp);
                        assert (del->tail_var == vid);
                        assert (del->head_var == vtd_tmp_varid);
#else
                        pq_remove_elem (&
                                        (vtd_tmp_var->
                                         GETQDAG (type).dedge_pq),
                                        vtd_tmp->pos);
#endif
                        et_remove (&(v->GETQDAG (type).dedges),
                                   vtd_tmp_varid);
                        delete_edge (mm, vtd_tmp);
                        removed_edges++;

                        QDPLL_RESET_STACK (stack);
                        /* While-loop will break subsequently. */
                      }
                    else
                      {
                        /* Push and mark dependency pointers of 'tmp'. Must also 
                           handle existential class members. */
                        Edge *d;
                        unsigned int i, end = tmp->GETQDAG (type).dedges.size;
                        for (i = 0; i < end; i++)
                          for (d = tmp->GETQDAG (type).dedges.table[i]; d;
                               d = d->chain_next)
                            {
                              Var *dvar = VARID2VARPTR (vars, d->head_var);
                              assert (UF_IS_REP (dvar, 0, type));
                              assert (dvar != vtd_tmp_var);

                              /* Ignore marked variables and such that are larger than 'vtd_tmp_var'. */
                              if (dvar->GETQDAG (type).mark0
                                  || dvar->scope->nesting >=
                                  vtd_tmp_var_nesting)
                                continue;

                              dvar->GETQDAG (type).mark0 = 1;
                              QDPLL_PUSH_STACK (mm, marks, dvar);
                              QDPLL_PUSH_STACK (mm, stack, dvar);

                              /* Push dependencies of existential class members. */
                              if (QDPLL_SCOPE_EXISTS (dvar->scope)
                                  && !UF_IS_SINGLETON_SET (dvar, 0, type))
                                {
                                  VarID mid;
                                  Var *m;
                                  for (mid =
                                       dvar->GETQDAG (type).uf[0].
                                       members.list.first; mid;
                                       mid =
                                       m->GETQDAG (type).uf[0].members.
                                       link.next)
                                    {
                                      m = VARID2VARPTR (vars, mid);
                                      assert (!m->GETQDAG (type).mark0);
                                      assert (m->scope->nesting <
                                              vtd_tmp_var_nesting);
                                      m->GETQDAG (type).mark0 = 1;
                                      QDPLL_PUSH_STACK (mm, marks, m);
                                      QDPLL_PUSH_STACK (mm, stack, m);
                                    }
                                }
                            }
                      }
                  }
                /* Unmark variables, reset mark stack. */
                while (!QDPLL_EMPTY_STACK (marks))
                  {
                    Var *tmp = QDPLL_POP_STACK (marks);
                    assert (tmp->GETQDAG (type).mark0);
                    tmp->GETQDAG (type).mark0 = 0;
                  }
                assert (marks.top == marks.start);
                assert (stack.top == stack.start);
              }
        }
    }


  QDPLL_DELETE_STACK (mm, stack);
  QDPLL_DELETE_STACK (mm, marks);

#ifndef NDEBUG
#if QDAG_ASSERT_REMOVE_TRANSITIVITIES_VARS_UNMARKED
  /* Check that qdag-marks are all set to 0. */
  do
    {
      Var *p, *e;
      for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
        {
          assert (!p->GETQDAG (type).mark0);
          assert (!p->GETQDAG (type).mark1);
        }
    }
  while (0);
#endif
#endif

  return removed_edges;
}


static int
var_edges_subseteq (Var * v1, Var * v2)
{
  assert (v1->scope->type == v2->scope->type);
  assert (v1->scope->nesting == v2->scope->nesting);
  assert (QDPLL_SCOPE_EXISTS (v1->scope) || UF_IS_REP (v1, 0, type));
  assert (QDPLL_SCOPE_EXISTS (v2->scope) || UF_IS_REP (v2, 0, type));
  EdgeTable *t1, *t2;

  if (QDPLL_SCOPE_FORALL (v1->scope))
    {
      t1 = &(v1->GETQDAG (type).dedges);
      t2 = &(v2->GETQDAG (type).dedges);
    }
  else
    {
      assert (QDPLL_SCOPE_EXISTS (v1->scope));
      t1 = &(v1->GETQDAG (type).sedges);
      t2 = &(v2->GETQDAG (type).sedges);
    }

  if (t1->count > t2->count)
    return 0;

  int i, end = t1->size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = t1->table[i]; d; d = d->chain_next)
      {
        if (!et_lookup (t2, d->head_var))
          return 0;
      }

  return 1;
}


#ifndef NDEBUG
static void
assert_merged_univ_vars (Var * vars, Scope * s)
{
  assert (QDPLL_SCOPE_FORALL (s));
  Var *v1, *v2;
  VarID vid1, vid2;
  for (vid1 = s->GETPART (type).classes[0].first; vid1;
       vid1 = v1->GETQDAG (type).uf[0].class_link.next)
    {
      v1 = VARID2VARPTR (vars, vid1);
      for (vid2 = v1->GETQDAG (type).uf[0].class_link.next; vid2;
           vid2 = v2->GETQDAG (type).uf[0].class_link.next)
        {
          v2 = VARID2VARPTR (vars, vid2);
          assert (!var_edges_subseteq (v1, v2)
                  || !var_edges_subseteq (v2, v1));
        }
      if (!UF_IS_SINGLETON_SET (v1, 0, type))
        {
          Var *m;
          VarID mid;
          for (mid = v1->GETQDAG (type).uf[0].members.list.first; mid;
               mid = m->GETQDAG (type).uf[0].members.link.next)
            {
              m = VARID2VARPTR (vars, mid);
              assert (m->GETQDAG (type).dedges.count == 0);
            }
        }
    }
}


static void
assert_merged_exist_vars (Var * vars, Scope * s)
{
  assert (QDPLL_SCOPE_EXISTS (s));
  Var *v1, *v2;
  VarID vid1, vid2;
  for (vid1 = s->GETPART (type).classes[1].first; vid1;
       vid1 = v1->GETQDAG (type).uf[1].class_link.next)
    {
      v1 = VARID2VARPTR (vars, vid1);
      for (vid2 = v1->GETQDAG (type).uf[1].class_link.next; vid2;
           vid2 = v2->GETQDAG (type).uf[1].class_link.next)
        {
          v2 = VARID2VARPTR (vars, vid2);
          assert (!var_edges_subseteq (v1, v2)
                  || !var_edges_subseteq (v2, v1));
        }
      if (!UF_IS_SINGLETON_SET (v1, 1, type))
        {
          Var *m;
          VarID mid;
          for (mid = v1->GETQDAG (type).uf[1].members.list.first; mid;
               mid = m->GETQDAG (type).uf[1].members.link.next)
            {
              m = VARID2VARPTR (vars, mid);
            }
        }
    }
}

#endif

static void
cleanup_non_rep_sedges (QDPLLMemMan * mm, Var * vars, Var * v)
{
  assert (!UF_IS_REP (v, 1, type));
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  int i, end = v->GETQDAG (type).sedges.size;
  Edge *d, *n;
  for (i = 0; i < end; i++)
    {
      for (d = v->GETQDAG (type).sedges.table[i]; d; d = n)
        {
          n = d->chain_next;
          Var *h = VARID2VARPTR (vars, d->head_var);
          assert (VARID2VARPTR (vars, d->tail_var) == v);
          assert (QDPLL_SCOPE_EXISTS (h->scope));
          assert (UF_IS_REP (h, 1, type));
          assert (d->priority == v->scope->nesting);
#ifndef NDEBUG
          Edge *tmp = pq_remove_elem (&(h->GETQDAG (type).sedge_pq), d->pos);
          assert (tmp == d);
#else
          pq_remove_elem (&(h->GETQDAG (type).sedge_pq), d->pos);
#endif
          delete_edge (mm, d);
        }
      v->GETQDAG (type).sedges.table[i] = 0;
    }
  v->GETQDAG (type).sedges.count = 0;
}


static void
cleanup_non_rep_dedges (QDPLLMemMan * mm, Var * vars, Var * v)
{
  assert (!UF_IS_REP (v, 0, type));
  assert (QDPLL_SCOPE_FORALL (v->scope));
  int i, end = v->GETQDAG (type).dedges.size;
  Edge *d, *n;
  for (i = 0; i < end; i++)
    {
      for (d = v->GETQDAG (type).dedges.table[i]; d; d = n)
        {
          n = d->chain_next;
          Var *h = VARID2VARPTR (vars, d->head_var);
          assert (VARID2VARPTR (vars, d->tail_var) == v);
          assert (QDPLL_SCOPE_EXISTS (h->scope));
          assert (UF_IS_REP (h, 0, type));
          assert (d->priority == v->scope->nesting);
#ifndef NDEBUG
          Edge *tmp = pq_remove_elem (&(h->GETQDAG (type).dedge_pq), d->pos);
          assert (tmp == d);
#else
          pq_remove_elem (&(h->GETQDAG (type).dedge_pq), d->pos);
#endif
          delete_edge (mm, d);
        }
      v->GETQDAG (type).dedges.table[i] = 0;
    }

  v->GETQDAG (type).dedges.count = 0;
}


static void
merge_exist_scope_vars_by_sedges (QDPLLMemMan * mm, Var * vars, Scope * s,
                                  const QDPLLDepManType type)
{
  assert (QDPLL_SCOPE_EXISTS (s));
  Var *v1, *v2, *n1, *n2;
  VarID vid1, vidn1, vid2, vidn2;
  for (vid1 = s->GETPART (type).classes[1].first; vid1; vid1 = vidn1)
    {
      v1 = VARID2VARPTR (vars, vid1);
      assert (UF_IS_REP (v1, 1, type));
      vidn1 = v1->GETQDAG (type).uf[1].class_link.next;
      n1 = vidn1 ? VARID2VARPTR (vars, vidn1) : 0;
      for (vid2 = v1->GETQDAG (type).uf[1].class_link.next; vid2;
           vid2 = vidn2)
        {
          v2 = VARID2VARPTR (vars, vid2);
          assert (UF_IS_REP (v2, 1, type));
          vidn2 = v2->GETQDAG (type).uf[1].class_link.next;
          n2 = vidn2 ? VARID2VARPTR (vars, vidn2) : 0;
          if (var_edges_subseteq (v1, v2) && var_edges_subseteq (v2, v1))
            {
              if (v2 == n1)
                {
                  vidn1 = vidn2;
                  n1 = n2;
                }
              uf_unite (vars, v1, v2, 1, type);

              /* Cleanup s-edges of merged classes. */
              if (UF_IS_REP (v1, 1, type))
                {
                  cleanup_non_rep_sedges (mm, vars, v2);
                }
              else
                {
                  cleanup_non_rep_sedges (mm, vars, v1);
                  v1 = v2;
                }
            }
        }
    }

#ifndef NDEBUG
#if QDAG_ASSERT_MERGED_UNIV_VARS
  assert_merged_exist_vars (vars, s);
#endif
#endif
}


static void
merge_univ_scope_vars_by_dedges (QDPLLMemMan * mm, Var * vars, Scope * s,
                                 const QDPLLDepManType type)
{
  assert (QDPLL_SCOPE_FORALL (s));
  Var *v1, *v2, *n1, *n2;
  VarID vid1, vidn1, vid2, vidn2;
  for (vid1 = s->GETPART (type).classes[0].first; vid1; vid1 = vidn1)
    {
      v1 = VARID2VARPTR (vars, vid1);
      assert (UF_IS_REP (v1, 0, type));
      vidn1 = v1->GETQDAG (type).uf[0].class_link.next;
      n1 = vidn1 ? VARID2VARPTR (vars, vidn1) : 0;
      for (vid2 = v1->GETQDAG (type).uf[0].class_link.next; vid2;
           vid2 = vidn2)
        {
          v2 = VARID2VARPTR (vars, vid2);
          assert (UF_IS_REP (v2, 0, type));
          vidn2 = v2->GETQDAG (type).uf[0].class_link.next;
          n2 = vidn2 ? VARID2VARPTR (vars, vidn2) : 0;
          if (var_edges_subseteq (v1, v2) && var_edges_subseteq (v2, v1))
            {
              if (v2 == n1)
                {
                  vidn1 = vidn2;
                  n1 = n2;
                }
              uf_unite (vars, v1, v2, 0, type);

              if (UF_IS_REP (v1, 0, type))
                {
                  cleanup_non_rep_dedges (mm, vars, v2);
                }
              else
                {
                  cleanup_non_rep_dedges (mm, vars, v1);
                  v1 = v2;
                }
            }
        }
    }

#ifndef NDEBUG
#if QDAG_ASSERT_MERGED_UNIV_VARS
  assert_merged_univ_vars (vars, s);
#endif
#endif
}


/* This version is expected to avoid transitive edges by construction  
   yet this is not entirely possible (counterexample). */
static void
insert_existential_deps (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;

  Scope *s;
  for (s = dm->pcnf->scopes.last; s; s = s->link.prev)
    {
      if (QDPLL_SCOPE_EXISTS (s))
        {
          VarID vid;
          Var *v, *c, *insert;
          for (vid = s->GETPART (type).classes[0].first; vid;
               vid = v->GETQDAG (type).uf[0].class_link.next)
            {
              v = VARID2VARPTR (vars, vid);
              insert = v;
              VarID cid = v->id;
              /* Check 'v' and all c-forest ancestors 'c' of 'v'. */
              while (cid)
                {
                  c = VARID2VARPTR (vars, cid);

                  /* By moving the insert position, edges are 'chained' 
                     -> heuristically tries to avoid transitive edges. */
                  if (pq_count (&(c->GETQDAG (type).dedge_pq)) != 0)
                    insert = c;

                  /* Check all s-edges of current c-forest ancestor 'c'. */
                  Edge *s, **cur, **end;
                  end = c->GETQDAG (type).sedge_pq.elems_top;
                  cur = c->GETQDAG (type).sedge_pq.elems_start;
                  for (; cur < end; cur++)
                    {
                      s = *cur;
                      Var *s_tailvar = VARID2VARPTR (vars, s->tail_var);
                      /* NEW: s-edge partition -> will get d-edges from classes to classes. */
                      assert (QDPLL_SCOPE_EXISTS (s_tailvar->scope));
                      assert (UF_IS_REP (s_tailvar, 1, type));
                      Edge *d, **d_cur, **d_end;
                      d_end = insert->GETQDAG (type).dedge_pq.elems_top;
                      d_cur = insert->GETQDAG (type).dedge_pq.elems_start;
                      for (; d_cur < d_end; d_cur++)
                        {
                          d = *d_cur;
                          Var *d_tailvar = VARID2VARPTR (vars, d->tail_var);
                          /* Only representative of universal class has d-edges, but not members. */
                          assert (QDPLL_SCOPE_FORALL (d_tailvar->scope));
                          assert (UF_IS_REP (d_tailvar, 0, type));
                          /* Insert edge. */
                          if (!HAS_EDGE
                              (s_tailvar, d_tailvar->id,
                               GETQDAG (type).dedges))
                            {
                              Edge *edge;
                              edge = create_edge (mm);
                              edge->tail_var = s_tailvar->id;
                              edge->head_var = d_tailvar->id;
                              pq_insert (mm,
                                         &(d_tailvar->
                                           GETQDAG (type).dedge_pq), edge,
                                         s_tailvar->scope->nesting);
                              et_insert (mm,
                                         &(s_tailvar->GETQDAG (type).dedges),
                                         edge);
                              /* NEW: due to s-edge partition, must
                                 also set ptrs from s-edge class members
                                 to head var. This behaviour occurred
                                 automatically when we did not merge
                                 variables by s-edges. */
                              if (!UF_IS_SINGLETON_SET (s_tailvar, 1, type))
                                {
                                  VarID mid;
                                  Var *m;
                                  for (mid =
                                       s_tailvar->GETQDAG (type).
                                       uf[1].members.list.first; mid;
                                       mid =
                                       m->GETQDAG (type).uf[1].members.
                                       link.next)
                                    {
                                      m = VARID2VARPTR (vars, mid);
                                      assert (!HAS_EDGE
                                              (m, d_tailvar->id,
                                               GETQDAG (type).dedges));
                                      edge = create_edge (mm);
                                      edge->tail_var = mid;
                                      edge->head_var = d_tailvar->id;
                                      pq_insert (mm,
                                                 &(d_tailvar->
                                                   GETQDAG (type).dedge_pq),
                                                 edge, m->scope->nesting);
                                      et_insert (mm,
                                                 &(m->GETQDAG (type).dedges),
                                                 edge);
                                    }
                                }
                            }
                        }
                    }
                  cid = c->GETQDAG (type).cedges.cpar;
                }
            }
        }
    }

  remove_transitivities (dm);
}

/* --------------- START: QUANTIFIER DAG INITIALIZATION --------------- */

static void
extract_dependencies (QDPLLDepManQDAG * dm)
{
  const QDPLLDepManType type = dm->dmg.type;
  Constraint *c;
  for (c = dm->pcnf->clauses.first; c; c = c->link.next)
    {
      assert (!c->is_cube);
      assert (!c->learnt);
      extract_dependencies_from_lits (dm, c->lits, c->num_lits);
    }

#ifndef NDEBUG
#if QDAG_ASSERT_GRAPH_INTEGRITY
  assert_graph_integrity (dm);
#endif
#endif

  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      if (QDPLL_SCOPE_FORALL (s))
        merge_univ_scope_vars_by_dedges (mm, vars, s, type);
      else
        merge_exist_scope_vars_by_sedges (mm, vars, s, type);
    }

#ifndef NDEBUG
#if QDAG_ASSERT_GRAPH_INTEGRITY
  assert_graph_integrity (dm);
#endif
#endif

  insert_existential_deps (dm);

#ifndef NDEBUG
#if QDAG_ASSERT_GRAPH_INTEGRITY
  assert_graph_integrity (dm);
#endif
#if QDAG_ASSERT_XCHECK_DEPENDENCIES
  assert_xcheck_dependencies (dm);
#endif
#if QDAG_ASSERT_CHECK_DEPENDENCIES_BY_FUNCTIONS
  assert_check_dependencies_by_functions (dm);
#endif
#endif

}

/* --------------- END: QUANTIFIER DAG INITIALIZATION --------------- */


/* --------------- START: LINEAR GRAPH INITIALIZATION --------------- */

static void
linear_graph_merge_scope_classes (Var * vars, Scope * s, const int offset,
                                  const QDPLLDepManType type)
{
  /* Must handle disabled variables at top-level. */
  VarID first;
  if (!(first = s->GETPART (type).classes[offset].first))
    return;
  Var *rep = VARID2VARPTR (vars, first);
  assert (UF_IS_REP (rep, offset, type));
  assert (UF_IS_SINGLETON_SET (rep, offset, type));

  VarID class, next;
  for (class = rep->GETQDAG (type).uf[offset].class_link.next; class;
       class = next)
    {
      Var *cur = VARID2VARPTR (vars, class);
      next = cur->GETQDAG (type).uf[offset].class_link.next;
      assert (UF_IS_REP (rep, offset, type));
      assert (UF_IS_REP (cur, offset, type));
      assert (UF_IS_SINGLETON_SET (cur, offset, type));
      uf_unite (vars, rep, cur, offset, type);
      rep = uf_find (vars, rep, offset, type);
    }
  /* Must have one big class afterwards. */
  assert (UF_IS_REP (rep, offset, type));
  assert (s->GETPART (type).classes[offset].first);
  assert (s->GETPART (type).classes[offset].first ==
          s->GETPART (type).classes[offset].last);
}


/* Build a linear dependency explicitly. Do NOT take into account
   formula structure at all. This is done to get the same behaviour as
   on a linear prefix. */
static void
build_linear_dependency_graph (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;
  const QDPLLDepManType type = dm->dmg.type;

  /* First, merge all variables in a scope into one big equivalence
     class. For exists-scopes, this generates the forest classes and
     s-edge partition, and for univ-scopes the d-edge partition. */
  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      linear_graph_merge_scope_classes (vars, s, 0, type);
      if (QDPLL_SCOPE_EXISTS (s))
        linear_graph_merge_scope_classes (vars, s, 1, type);
    }

  /* Next, insert forest edges between existential scopes and s-edges
     from exist-vars to exist-classes. */
  Scope *prev;
  for (prev = dm->pcnf->scopes.last; prev; prev = prev->link.prev)
    if (QDPLL_SCOPE_EXISTS (prev) && prev->GETPART (type).classes[0].first)
      break;
  for (s = prev ? prev->link.prev : 0; s; s = s->link.prev)
    {
      /* Must handle disabled variables at top-level. */
      if (QDPLL_SCOPE_FORALL (s) || !s->GETPART (type).classes[0].first)
        continue;
      assert (QDPLL_SCOPE_EXISTS (prev));
      assert (QDPLL_SCOPE_EXISTS (s));
      assert (s->nesting < prev->nesting);
      /* Insert s-edges from variables to big class. */
      Var *target =
        VARID2VARPTR (vars, prev->GETPART (type).classes[0].first);
      assert (UF_IS_REP (target, 0, type));
      Var *class_rep;
      VarID class;
      for (class = s->GETPART (type).classes[1].first; class;
           class = class_rep->GETQDAG (type).uf[1].class_link.next)
        {
          class_rep = VARID2VARPTR (vars, class);
          assert (QDPLL_SCOPE_EXISTS (class_rep->scope));
          assert (UF_IS_REP (class_rep, 1, type));
          insert_edge (dm, class_rep, target);
        }
      /* Insert forest edge between big existential classes. */
      insert_c_edge (dm,
                     VARID2VARPTR (vars, s->GETPART (type).classes[0].first),
                     VARID2VARPTR (vars,
                                   prev->GETPART (type).classes[0].first),
                     type);
      prev = s;
    }

  /* At this point, forest edges and s-edges from vars to classes are
     inserted. Next insert d-edges between big classes. */
  for (prev = dm->pcnf->scopes.last; prev; prev = prev->link.prev)
    if (prev->GETPART (type).classes[0].first)
      break;
  for (s = prev ? prev->link.prev : 0; s; s = s->link.prev)
    {
      if (!s->GETPART (type).classes[0].first)
        continue;
      assert (s->nesting < prev->nesting);
      if (QDPLL_SCOPE_FORALL (s) && QDPLL_SCOPE_EXISTS (prev))
        {


          insert_edge_aux (dm->mm,
                           VARID2VARPTR (vars,
                                         s->GETPART (type).classes[0].first),
                           VARID2VARPTR (vars,
                                         prev->GETPART (type).
                                         classes[0].first));
        }
      if (QDPLL_SCOPE_EXISTS (s))
        prev = s;
    }

  /* Finally insert d-edges from existential to universal classes. */
  insert_existential_deps (dm);

#ifndef NDEBUG
#if QDAG_ASSERT_GRAPH_INTEGRITY
  assert_graph_integrity (dm);
#endif
#if QDAG_ASSERT_CHECK_DEPENDENCIES_BY_FUNCTIONS
  assert_check_dependencies_by_functions (dm);
#endif
#endif
}

/* --------------- END: LINEAR GRAPH INITIALIZATION --------------- */

static void
collect_deps_from_cnf_check_clause (QDPLLDepManQDAG * dm,
                                    VarPtrStack * deps,
                                    VarPtrStack * con,
                                    QDPLLQuantifierType var_type,
                                    unsigned int var_nesting, Constraint * c)
{
  assert (!c->is_cube);
  if (c->learnt)
    return;

  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  LitID *litp, *lite = c->lits + c->num_lits - 1;
  for (litp = c->lits; litp <= lite; litp++)
    {
      LitID lit = *litp;
      Var *d = LIT2VARPTR (vars, lit);
      assert (!(QDPLL_VAR_MARKED_PROPAGATED (d)
               && d->decision_level <= 0));
      if (QDPLL_VAR_MARKED_PROPAGATED (d)
          && d->decision_level <= 0)
        continue;

      Scope *d_scope = d->scope;

      /* We only consider larger variables. Note that for dependencies
         of kind E->A, we could also use existential variables from the
         same existential scope (as originally in Marko Samer's proof of
         D^{std}) but this gives more restrictive dependencies. */

      if (var_nesting < d_scope->nesting)
        {
          /* Assumes that clauses are universally reduced. */
          if (var_type != d_scope->type)
            {
              /* Collect and mark dependency. */
              if (!d->GETQDAG (type).mark0)
                {
                  d->GETQDAG (type).mark0 = 1;
                  QDPLL_PUSH_STACK (mm, *deps, d);
                }
            }
          if (QDPLL_SCOPE_EXISTS (d_scope))
            {
              /* Collect and mark connecting variable. */
              if (!d->GETQDAG (type).mark1)
                {
                  d->GETQDAG (type).mark1 = 1;
                  QDPLL_PUSH_STACK (mm, *con, d);
                }
            }
        }
    }
}


static void
collect_deps_from_cnf (QDPLLDepManQDAG * dm, VarPtrStack * deps, Var * v)
{
  QDPLLQuantifierType var_type = v->scope->type;
  unsigned int var_nesting = v->scope->nesting;
  QDPLLMemMan *mm = dm->mm;
  VarPtrStack con;
  QDPLL_INIT_STACK (con);

  Var *vars = dm->pcnf->vars;

  assert (!v->GETQDAG (type).mark0);    /* 'mark0' marks collected dependencies. */
  assert (!v->GETQDAG (type).mark1);    /* 'mark1' marks collected connections. */
  /* Mark as connecting variable. */
  v->GETQDAG (type).mark1 = 1;
  QDPLL_PUSH_STACK (mm, con, v);

  while (!QDPLL_EMPTY_STACK (con))
    {
      Var *t = QDPLL_POP_STACK (con);
      assert (!
              (QDPLL_VAR_MARKED_PROPAGATED (t)
               && t->decision_level <= 0));
      assert (t->GETQDAG (type).mark1);        /* Must be marked as collected. */
      assert (t == v || v->scope->nesting < t->scope->nesting);
      assert (t == v || t->scope->type == QDPLL_QTYPE_EXISTS);

      /* Check all clauses containing literals of 'v'. */
      BLitsOcc *bp, *be;
      for (bp = t->pos_occ_clauses.start, be = t->pos_occ_clauses.top;
           bp < be; bp++)
        collect_deps_from_cnf_check_clause (dm, deps, &(con), var_type,
                                            var_nesting,
                                            BLIT_STRIP_PTR (bp->constraint));
      for (bp = t->neg_occ_clauses.start, be = t->neg_occ_clauses.top;
           bp < be; bp++)
        collect_deps_from_cnf_check_clause (dm, deps, &(con), var_type,
                                            var_nesting,
                                            BLIT_STRIP_PTR (bp->constraint));
    }

  QDPLL_DELETE_STACK (mm, con);

  /* Reset marks for 'collected connection' to 0 in all variables
     (some overhead but more convenient than collecting marked
     variables). */
  Var *p, *e;
  for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
    p->GETQDAG (type).mark1 = 0;

  /* Marks for collected dependencies will be reset later after cross-checking. */
}


/* Collect dependencies of universal variable by collecting all c-forest successors. */
static void
collect_deps_from_graph_forall (QDPLLDepManQDAG * dm, VarPtrStack * deps,
                                Var * v)
{
  const QDPLLDepManType type = dm->dmg.type;
  assert (QDPLL_SCOPE_FORALL (v->scope));
  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  VarPtrStack forest_succ;
  QDPLL_INIT_STACK (forest_succ);

  /* Must work on representative of variable 'v' due to merging of 
     universal classes (only representatives have d-edges). 
     Note: we could save a lot of work when computing dependencies 
     only once for each universal class. */
  v = uf_find (dm->pcnf->vars, v, 0, type);
  assert (UF_IS_REP (v, 0, type));

  unsigned int i, end = v->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = v->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
      {
        Var *dvar = VARID2VARPTR (vars, d->head_var);
        assert (UF_IS_REP (dvar, 0, type));
        assert (VARID2VARPTR (vars, d->tail_var) == v);
        assert (v->scope->nesting < dvar->scope->nesting);
        assert (QDPLL_SCOPE_EXISTS (dvar->scope));
        QDPLL_PUSH_STACK (mm, forest_succ, dvar);
      }

  while (!QDPLL_EMPTY_STACK (forest_succ))
    {
      Var *succ = QDPLL_POP_STACK (forest_succ);
      assert (UF_IS_REP (succ, 0, type));
      assert (QDPLL_SCOPE_EXISTS (succ->scope));
      assert (v->scope->nesting < succ->scope->nesting);

      /* Actually, need not mark collected dependencies/connections because of 
         tree property. Setting mark for assertion checking only. */
      assert (!succ->GETQDAG (type).mark0);
      succ->GETQDAG (type).mark0 = 1;
      QDPLL_PUSH_STACK (mm, *deps, succ);

      /* Must also collect class members, if any. */
      if (!UF_IS_SINGLETON_SET (succ, 0, type))
        {
          VarID mid;
          Var *m;
          for (mid = succ->GETQDAG (type).uf[0].members.list.first; mid;
               mid = m->GETQDAG (type).uf[0].members.link.next)
            {
              m = VARID2VARPTR (vars, mid);
              assert (!UF_IS_REP (m, 0, type));
              assert (QDPLL_SCOPE_EXISTS (m->scope));
              assert (v->scope->nesting < m->scope->nesting);
              assert (!m->GETQDAG (type).mark0);
              m->GETQDAG (type).mark0 = 1;
              QDPLL_PUSH_STACK (mm, *deps, m);
            }
        }

      /* Push c-children on successor stack for further traversal. */
      VarID cid;
      Var *c;
      for (cid = succ->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
          c = VARID2VARPTR (vars, cid);
          assert (!c->GETQDAG (type).mark0);
          assert (!c->GETQDAG (type).mark1);
          QDPLL_PUSH_STACK (mm, forest_succ, c);
        }
    }

  QDPLL_DELETE_STACK (mm, forest_succ);
}


static void
collect_deps_from_graph_exists (QDPLLDepManQDAG * dm, VarPtrStack * deps,
                                Var * v)
{
  const QDPLLDepManType type = dm->dmg.type;
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  VarPtrStack forest_succ;
  QDPLL_INIT_STACK (forest_succ);

  Var *v_rep = uf_find (vars, v, 1, type);

  /* Push all s-edges. */
  unsigned int i, end = v_rep->GETQDAG (type).sedges.size;
  Edge *s;
  for (i = 0; i < end; i++)
    for (s = v_rep->GETQDAG (type).sedges.table[i]; s; s = s->chain_next)
      {
        Var *svar = VARID2VARPTR (vars, s->head_var);
        assert (VARID2VARPTR (vars, s->tail_var) == v_rep);
        assert (QDPLL_SCOPE_EXISTS (svar->scope));
        assert (UF_IS_REP (svar, 0, type));
        assert (v_rep->scope->nesting < svar->scope->nesting);
        QDPLL_PUSH_STACK (mm, forest_succ, svar);
      }

  while (!QDPLL_EMPTY_STACK (forest_succ))
    {
      Var *succ = QDPLL_POP_STACK (forest_succ);
      assert (UF_IS_REP (succ, 0, type));
      assert (QDPLL_SCOPE_EXISTS (succ->scope));
      assert (v->scope->nesting < succ->scope->nesting);

      /* Collect all universal variables which have d-edge to 'succ'. */
      Edge **p, **e;
      for (p = succ->GETQDAG (type).dedge_pq.elems_start,
           e = succ->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
        {
          Var *dvar = VARID2VARPTR (vars, (*p)->tail_var);
          assert (VARID2VARPTR (vars, (*p)->head_var) == succ);
          assert (v->scope->nesting < dvar->scope->nesting);
          assert (dvar->scope->nesting < succ->scope->nesting);
          assert (QDPLL_SCOPE_FORALL (dvar->scope));
          assert (UF_IS_REP (dvar, 0, type));

          if (!dvar->GETQDAG (type).mark0)
            {
              dvar->GETQDAG (type).mark0 = 1;
              QDPLL_PUSH_STACK (mm, *deps, dvar);

              if (!UF_IS_SINGLETON_SET (dvar, 0, type))
                {
                  VarID mid;
                  Var *m;
                  for (mid = dvar->GETQDAG (type).uf[0].members.list.first;
                       mid; mid = m->GETQDAG (type).uf[0].members.link.next)
                    {
                      m = VARID2VARPTR (vars, mid);
                      assert (!m->GETQDAG (type).mark0);
                      m->GETQDAG (type).mark0 = 1;
                      QDPLL_PUSH_STACK (mm, *deps, m);
                    }
                }
            }
        }

      /* Push c-children on successor stack for further traversal. */
      VarID cid;
      Var *c;
      for (cid = succ->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
          c = VARID2VARPTR (vars, cid);
          assert (!c->GETQDAG (type).mark0);
          assert (!c->GETQDAG (type).mark1);
          QDPLL_PUSH_STACK (mm, forest_succ, c);
        }
    }

  QDPLL_DELETE_STACK (mm, forest_succ);
}

static void
collect_deps_from_graph (QDPLLDepManQDAG * dm, VarPtrStack * deps, Var * v)
{
  if (QDPLL_SCOPE_FORALL (v->scope))
    collect_deps_from_graph_forall (dm, deps, v);
  else
    {
      assert (QDPLL_SCOPE_EXISTS (v->scope));
      collect_deps_from_graph_exists (dm, deps, v);
    }
}


static int
qsort_compare_deps_by_id (const void *dep1, const void *dep2)
{
  Var *v1 = *((Var **) dep1);
  Var *v2 = *((Var **) dep2);

  if (v1->id < v2->id)
    return -1;
  else if (v1->id > v2->id)
    return 1;
  else
    return 0;
}


static void
unmark_dependency_marks (VarPtrStack * deps)
{
  Var **p, **e;
  for (p = deps->start, e = deps->top; p < e; p++)
    {
      Var *v = *p;
      assert (v->GETQDAG (type).mark0);
      v->GETQDAG (type).mark0 = 0;
    }
}


/* Mark all universal variables (i.e. classes!) pointed to by d-edges
   from existential classes as depending. */
static void
mark_non_candidates_from_exists (QDPLLDepManQDAG * dm, Scope * s)
{
  Var *vars = dm->pcnf->vars;
  assert (QDPLL_SCOPE_EXISTS (s));

  VarID *p, *e;
  for (p = s->vars.start, e = s->vars.top; p < e; p++)
    {
      Var *v = VARID2VARPTR (vars, *p);
      unsigned int i, e = v->GETQDAG (type).dedges.size;
      Edge *d;
      for (i = 0; i < e; i++)
        for (d = v->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
          {
            Var *dvar = VARID2VARPTR (vars, d->head_var);
            assert (QDPLL_SCOPE_FORALL (dvar->scope));
            assert (UF_IS_REP (dvar, 0, type));
            assert (v->scope->nesting < dvar->scope->nesting);
            dvar->GETQDAG (type).mark0 = 1;
          }
    }
}


/* Mark all forest-successors (i.e. classes!) of universal variables as
   depending. Such variables can not be candidates since they depend
   on at least one universal variable. */
static void
mark_non_candidates_from_forall (QDPLLDepManQDAG * dm, Scope * s)
{
  Var *vars = dm->pcnf->vars;
  QDPLLMemMan *mm = dm->mm;
  VarPtrStack forest_succ;
  QDPLL_INIT_STACK (forest_succ);
  assert (QDPLL_SCOPE_FORALL (s));

  Var *v;
  VarID vid;
  for (vid = s->GETPART (type).classes[0].first; vid;
       vid = v->GETQDAG (type).uf[0].class_link.next)
    {
      v = VARID2VARPTR (vars, vid);
      assert (UF_IS_REP (v, 0, type));
      assert (QDPLL_SCOPE_FORALL (v->scope));

      /* Mark and push d-edges on traversal stack. */
      unsigned int i, end = v->GETQDAG (type).dedges.size;
      Edge *d;
      for (i = 0; i < end; i++)
        for (d = v->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
          {
            Var *dvar = VARID2VARPTR (vars, d->head_var);
            assert (QDPLL_SCOPE_EXISTS (dvar->scope));
            assert (UF_IS_REP (dvar, 0, type));
            assert (v->scope->nesting < dvar->scope->nesting);

            if (!dvar->GETQDAG (type).mark0)
              {
                dvar->GETQDAG (type).mark0 = 1;
                QDPLL_PUSH_STACK (mm, forest_succ, dvar);
              }
          }

      while (!QDPLL_EMPTY_STACK (forest_succ))
        {
          Var *succ = QDPLL_POP_STACK (forest_succ);
          assert (QDPLL_SCOPE_EXISTS (succ->scope));
          assert (v->scope->nesting < succ->scope->nesting);
          assert (UF_IS_REP (succ, 0, type));
          assert (succ->GETQDAG (type).mark0);

          /* Mark and push all c-children not yet marked. */
          Var *c;
          VarID cid;
          for (cid = succ->GETQDAG (type).cedges.cchilds.first; cid;
               cid = c->GETQDAG (type).cedges.csibs.next)
            {
              c = VARID2VARPTR (vars, cid);
              if (!c->GETQDAG (type).mark0)
                {
                  c->GETQDAG (type).mark0 = 1;
                  QDPLL_PUSH_STACK (mm, forest_succ, c);
                }
            }
        }
    }

  QDPLL_DELETE_STACK (mm, forest_succ);
}


/* Returns the number of variables not yet marked as propagated in the
   class of universal 'v', i.e. the number of active variables. */
static unsigned int
count_non_propagated_in_class (Var * vars, Var * v, const unsigned int offset)
{
  assert (offset <= 1);
  assert (offset != 0 || QDPLL_SCOPE_FORALL (v->scope));
  assert (offset != 1 || QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, offset, type));
  unsigned int result = 0;

  if (!QDPLL_VAR_MARKED_PROPAGATED (v))
    result++;
#if SKIP_DELAYED_NOTIF_ASSERT
  else if (!v->GETQDAG (type).mark_notified_inactive)
    result++;
#endif

  if (!UF_IS_SINGLETON_SET (v, offset, type))
    {
      Var *m;
      VarID mid;
      for (mid = v->GETQDAG (type).uf[offset].members.list.first; mid;
           mid = m->GETQDAG (type).uf[offset].members.link.next)
        {
          m = VARID2VARPTR (vars, mid);
          if (!QDPLL_VAR_MARKED_PROPAGATED (m))
            result++;
#if SKIP_DELAYED_NOTIF_ASSERT
          else if (!m->GETQDAG (type).mark_notified_inactive)
            result++;
#endif
        }
    }

  return result;
}


/* Returns the number of direct references from universal classes to
   existential 'v' which are not yet marked as candidate. */
static unsigned int
count_direct_non_candidate_refs_by_univ_class (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, 0, type));
  unsigned int result = 0;

  Edge **p, **e;
  for (p = v->GETQDAG (type).dedge_pq.elems_start,
       e = v->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
    {
      Edge *u = *p;
      Var *uvar = VARID2VARPTR (vars, u->tail_var);
      assert (QDPLL_SCOPE_FORALL (uvar->scope));
      assert (uvar->scope->nesting < v->scope->nesting);
      assert (UF_IS_REP (uvar, 0, type));
      /*'uvar' references 'v'. */
      if (!uvar->GETQDAG (type).mark_is_candidate)
        result++;
    }

  return result;
}


/* Returns the number of direct references from existential variables to
   universal 'v' which are not yet marked as propagated i.e. the number
   of active references. */
static unsigned int
count_direct_active_refs_by_exist_var (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_FORALL (v->scope));
  assert (UF_IS_REP (v, 0, type));
  unsigned int result = 0;

  Edge **p, **e;
  for (p = v->GETQDAG (type).dedge_pq.elems_start,
       e = v->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
    {
      Edge *u = *p;
      Var *uvar = VARID2VARPTR (vars, u->tail_var);
      assert (QDPLL_SCOPE_EXISTS (uvar->scope));
      assert (uvar->scope->nesting < v->scope->nesting);
#if 1
      if (!QDPLL_VAR_MARKED_PROPAGATED (uvar))
        result++;
#if SKIP_DELAYED_NOTIF_ASSERT
      else if (!uvar->GETQDAG (type).mark_notified_inactive)
        result++;
#endif
#endif
    }

  return result;
}


/* Returns the number of direct references by s-edges from existential
   variables to existential classes 'v' which are not yet marked as
   propagated i.e. the number of active references. */
static unsigned int
count_direct_active_refs_by_sedge (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, 0, type));
  unsigned int result = 0;

  Edge **p, **e;
  for (p = v->GETQDAG (type).sedge_pq.elems_start,
       e = v->GETQDAG (type).sedge_pq.elems_top; p < e; p++)
    {
      Edge *u = *p;
      Var *uvar = VARID2VARPTR (vars, u->tail_var);
      assert (QDPLL_SCOPE_EXISTS (uvar->scope));
      assert (UF_IS_REP (uvar, 1, type));
      assert (uvar->scope->nesting < v->scope->nesting);
      /* 'uvar' references 'v'. */
      if (count_non_propagated_in_class (vars, uvar, 1) != 0)
        result++;
    }

  return result;
}


/* Returns the number of direct references from universal classes to
   existential 'v' which are not yet marked as propagated i.e. the number
   of active references. */
static unsigned int
count_direct_active_refs_by_univ_class (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, 0, type));
  unsigned int result = 0;

  Edge **p, **e;
  for (p = v->GETQDAG (type).dedge_pq.elems_start,
       e = v->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
    {
      Edge *u = *p;
      Var *uvar = VARID2VARPTR (vars, u->tail_var);
      assert (QDPLL_SCOPE_FORALL (uvar->scope));
      assert (uvar->scope->nesting < v->scope->nesting);
      assert (UF_IS_REP (uvar, 0, type));
      /*'uvar' references 'v'. */
      if (count_non_propagated_in_class (vars, uvar, 0) != 0)
        result++;
    }

  return result;
}


static unsigned int
count_class_members (Var * vars, Var * v, const unsigned int offset)
{
  assert (offset <= 1);
  assert (offset != 0 || QDPLL_SCOPE_FORALL (v->scope));
  assert (offset != 1 || QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, offset, type));
  unsigned int result = 1;
  if (!UF_IS_SINGLETON_SET (v, offset, type))
    {
      Var *m;
      VarID mid;
      for (mid = v->GETQDAG (type).uf[offset].members.list.first; mid;
           mid = m->GETQDAG (type).uf[offset].members.link.next)
        {
          m = VARID2VARPTR (vars, mid);
          result++;
        }
    }
  return result;
}


/* Find all variables 'x' such that D^{-1}(x) is empty, that is,
   variables which do not depend on any other variable. */
static void
fill_candidates (QDPLLDepManQDAG * dm)
{
  assert (dm->state.init);
#if COMPUTE_STATS
  assert (dm->stats.num_cur_inactive == 0);
  assert (dm->stats.num_cur_active_cands == 0);
#endif
  Var *vars = dm->pcnf->vars;

#ifndef NDEBUG
#if QDAG_ASSERT_FILL_CANDIDATES_VARS
  do
    {
      Var *p, *e;
      for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
        {
          assert (!p->GETQDAG (type).mark_is_candidate);
          assert (!p->GETQDAG (type).mark_notified_inactive);
          assert (!p->GETQDAG (type).mark0);
          assert (!p->GETQDAG (type).mark1);
          assert (!QDPLL_VAR_MARKED_PROPAGATED (p));
        }
    }
  while (0);
#endif
#endif

  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      if (QDPLL_SCOPE_EXISTS (s))
        mark_non_candidates_from_exists (dm, s);
      else
        {
          assert (QDPLL_SCOPE_FORALL (s));
          mark_non_candidates_from_forall (dm, s);
        }
    }

  /* Traverse all classes of variables and collect unmarked variables
     as candidates. Unmark depending variables on-the-fly. */

  /* POSSIBLE OPTIMIZATION? suffices to mark class representatives as candidate? */

  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      unsigned int cnt_members;
      Var *v;
      VarID vid;
      for (vid = s->GETPART (type).classes[0].first; vid;
           vid = v->GETQDAG (type).uf[0].class_link.next)
        {
          cnt_members = 0;
          v = VARID2VARPTR (vars, vid);
          assert (UF_IS_REP (v, 0, type));

          /* Mark forest roots as as beginning of
             inactive-sedge-frontier. */
          if (QDPLL_SCOPE_EXISTS (s) && !v->GETQDAG (type).cedges.cpar)
            v->GETQDAG (type).cnt.exists.inactive_sedge_frontier = 1;

          if (!v->GETQDAG (type).mark0)
            {
              /* Link variable and all class members to candidate list. */
              assert (!v->GETQDAG (type).mark_is_candidate);
              v->GETQDAG (type).mark_is_candidate = 1;
              VAR_LINK (vars, dm->candidates, v, GETQDAG (type).cand_link);
              cnt_members++;
#if COMPUTE_STATS
              if (!v->GETQDAG (type).mark_notified_inactive)
                {
                  assert (dm->stats.num_cur_active_cands <
                          dm->pcnf->used_vars);
                  dm->stats.num_cur_active_cands++;
                }
#endif
              if (!UF_IS_SINGLETON_SET (v, 0, type))
                {
                  Var *m;
                  VarID mid;
                  for (mid = v->GETQDAG (type).uf[0].members.list.first; mid;
                       mid = m->GETQDAG (type).uf[0].members.link.next)
                    {
                      m = VARID2VARPTR (vars, mid);
                      assert (!m->GETQDAG (type).mark0);
                      assert (!m->GETQDAG (type).mark_is_candidate);
                      m->GETQDAG (type).mark_is_candidate = 1;
                      VAR_LINK (vars, dm->candidates, m,
                                GETQDAG (type).cand_link);
                      cnt_members++;
#if COMPUTE_STATS
                      if (!m->GETQDAG (type).mark_notified_inactive)
                        {
                          assert (dm->stats.num_cur_active_cands <
                                  dm->pcnf->used_vars);
                          dm->stats.num_cur_active_cands++;
                        }
#endif
                    }
                }
            }
          else                  /* Unmark variable (class members have never been marked). */
            v->GETQDAG (type).mark0 = 0;
          /* Set up counters for incremental candidate maintenance in variables. */
          if (QDPLL_SCOPE_FORALL (s))
            {
              if (!cnt_members)
                cnt_members = count_class_members (vars, v, 0);
              assert (cnt_members ==
                      count_non_propagated_in_class (vars, v, 0));
              v->GETQDAG (type).cnt.forall.non_propagated_in_class =
                cnt_members;
              assert (pq_count (&(v->GETQDAG (type).dedge_pq)) ==
                      count_direct_active_refs_by_exist_var (vars, v));
#ifndef NDEBUG
              v->GETQDAG (type).cnt.forall.active_direct_refs_by_exist_var =
                pq_count (&(v->GETQDAG (type).dedge_pq));
#endif
            }
          else
            {
              assert (QDPLL_SCOPE_EXISTS (s));
              assert (pq_count (&(v->GETQDAG (type).dedge_pq)) ==
                      count_direct_active_refs_by_univ_class (vars, v));
              v->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class =
                pq_count (&(v->GETQDAG (type).dedge_pq));
              assert (pq_count (&(v->GETQDAG (type).sedge_pq)) ==
                      count_direct_active_refs_by_sedge (vars, v));
              v->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge =
                pq_count (&(v->GETQDAG (type).sedge_pq));

            }
        }
    }

  /* Traverse s-edge partition in existential scopes to set up
     non-propagated counter. */
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      if (QDPLL_SCOPE_FORALL (s))
        continue;
      Var *v;
      VarID vid;
      for (vid = s->GETPART (type).classes[1].first; vid;
           vid = v->GETQDAG (type).uf[1].class_link.next)
        {
          v = VARID2VARPTR (vars, vid);
          assert (QDPLL_SCOPE_EXISTS (s));
          assert (UF_IS_REP (v, 1, type));
          unsigned int cnt_members = count_class_members (vars, v, 1);
          assert (cnt_members == count_non_propagated_in_class (vars, v, 1));
          v->GETQDAG (type).cnt.exists.non_propagated_in_class = cnt_members;
        }
    }

#ifndef NDEBUG
#if QDAG_ASSERT_FILL_CANDIDATES_VARS
  do
    {
      Var *p, *e;
      for (p = vars, e = vars + dm->pcnf->size_vars; p < e; p++)
        {
          assert (!p->GETQDAG (type).mark0);
          assert (!p->GETQDAG (type).mark1);
          assert (!QDPLL_VAR_MARKED_PROPAGATED (p));
          if (p->id && UF_IS_REP (p, 0, type))
            {
              if (QDPLL_SCOPE_EXISTS (p->scope))
                {
                  assert (p->GETQDAG (type).cnt.
                          exists.active_direct_refs_by_univ_class ==
                          count_direct_active_refs_by_univ_class (vars, p));
                  assert (p->GETQDAG (type).cnt.
                          exists.active_direct_refs_by_sedge ==
                          count_direct_active_refs_by_sedge (vars, p));
                }
              else
                {
                  assert (QDPLL_SCOPE_FORALL (p->scope));
                  assert (p->GETQDAG (type).cnt.forall.
                          active_direct_refs_by_exist_var ==
                          count_direct_active_refs_by_exist_var (vars, p));
                  assert (p->GETQDAG (type).cnt.
                          forall.non_propagated_in_class ==
                          count_non_propagated_in_class (vars, p, 0));
                }
            }
        }
    }
  while (0);
#endif
#if QDAG_ASSERT_CANDIDATE_LIST
  assert_candidate_list (dm);
#endif
#endif
}


static void
collect_class_as_candidate (QDPLLDepManQDAG * dm, Var * vars, Var * class)
{
  assert (UF_IS_REP (class, 0, type));
  assert (!class->GETQDAG (type).mark_is_candidate);
  class->GETQDAG (type).mark_is_candidate = 1;
  VAR_LINK (vars, dm->candidates, class, GETQDAG (type).cand_link);
#if COMPUTE_STATS
  dm->stats.num_total_notinact_costs++;
  if (!class->GETQDAG (type).mark_notified_inactive)
    {
      assert (dm->stats.num_cur_active_cands < dm->pcnf->used_vars);
      dm->stats.num_cur_active_cands++;
    }
#endif
  if (!UF_IS_SINGLETON_SET (class, 0, type))
    {
      VarID mid;
      Var *m;
      for (mid = class->GETQDAG (type).uf[0].members.list.first;
           mid; mid = m->GETQDAG (type).uf[0].members.link.next)
        {
          m = VARID2VARPTR (vars, mid);
          assert (!m->GETQDAG (type).mark_is_candidate);
          m->GETQDAG (type).mark_is_candidate = 1;
          VAR_LINK (vars, dm->candidates, m, GETQDAG (type).cand_link);
#if COMPUTE_STATS
          dm->stats.num_total_notinact_costs++;
          if (!m->GETQDAG (type).mark_notified_inactive)
            {
              assert (dm->stats.num_cur_active_cands < dm->pcnf->used_vars);
              dm->stats.num_cur_active_cands++;
            }
#endif
        }
    }
}


static void
undo_collect_class_as_candidate (QDPLLDepManQDAG * dm, Var * vars,
                                 Var * class)
{
  assert (UF_IS_REP (class, 0, type));
  assert (class->GETQDAG (type).mark_is_candidate);
  class->GETQDAG (type).mark_is_candidate = 0;

  if (class->GETQDAG (type).cand_link.prev
      || class->GETQDAG (type).cand_link.next
      || class->id == dm->candidates.first)
    VAR_UNLINK (vars, dm->candidates, class, GETQDAG (type).cand_link);

#if COMPUTE_STATS
  dm->stats.num_total_notact_costs++;
  if (!class->GETQDAG (type).mark_notified_inactive)
    {
      assert (dm->stats.num_cur_active_cands > 0);
      dm->stats.num_cur_active_cands--;
    }
#endif

  if (!UF_IS_SINGLETON_SET (class, 0, type))
    {
      VarID mid;
      Var *m;
      for (mid = class->GETQDAG (type).uf[0].members.list.first;
           mid; mid = m->GETQDAG (type).uf[0].members.link.next)
        {
          m = VARID2VARPTR (vars, mid);
          assert (m->GETQDAG (type).mark_is_candidate);
          m->GETQDAG (type).mark_is_candidate = 0;

          if (m->GETQDAG (type).cand_link.prev
              || m->GETQDAG (type).cand_link.next
              || mid == dm->candidates.first)
            VAR_UNLINK (vars, dm->candidates, m, GETQDAG (type).cand_link);

#if COMPUTE_STATS
          dm->stats.num_total_notact_costs++;
          if (!m->GETQDAG (type).mark_notified_inactive)
            {
              assert (dm->stats.num_cur_active_cands > 0);
              dm->stats.num_cur_active_cands--;
            }
#endif
        }
    }
}


/* NOTE: when calling this function, we typically already know that one
 'dvar' is part of frontier. */
static int
is_candidate_by_frontier (QDPLLDepManQDAG * dm, Var * vars, Var * u)
{
  assert (QDPLL_SCOPE_FORALL (u->scope));
  assert (UF_IS_REP (u, 0, type));
  unsigned int i, end = u->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = u->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notinact_costs++;
#endif
        Var *dvar = VARID2VARPTR (vars, d->head_var);
        assert (QDPLL_SCOPE_EXISTS (dvar->scope));
        assert (UF_IS_REP (dvar, 0, type));

        if (!dvar->GETQDAG (type).cnt.exists.inactive_sedge_frontier)
          {
            return 0;
          }
        else
          assert (dvar->GETQDAG (type).cnt.
                  exists.active_direct_refs_by_sedge == 0);
      }

  assert (!referenced_by_active_existential_var (vars, u));
  return 1;
}


static void
get_universal_candidates_top_down (QDPLLDepManQDAG * dm, Var * var)
{
  assert (QDPLL_SCOPE_EXISTS (var->scope));
  assert (UF_IS_REP (var, 0, type));
  Var *vars = dm->pcnf->vars;
  assert (var->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 0);
  assert (var->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
          count_direct_active_refs_by_sedge (vars, var));
#ifndef NDEBUG
#if QDAG_ASSERT_INACTIVE_SEDGE_FRONTIER
  if (var->GETQDAG (type).cedges.cpar)
    assert_inactive_sedge_frontier_by_ancestors (dm,
                                                 VARID2VARPTR (vars,
                                                               var->GETQDAG
                                                               (type).cedges.
                                                               cpar));
#endif
#endif
  QDPLLMemMan *mm = dm->mm;
  VarPtrStack succ;
  QDPLL_INIT_STACK (succ);

  QDPLL_PUSH_STACK (mm, succ, var);

  /* Propagate inactive s-edge frontier downwards. */
  while (!QDPLL_EMPTY_STACK (succ))
    {
#if COMPUTE_STATS
      dm->stats.num_total_notinact_costs++;
#endif
      Var *s = QDPLL_POP_STACK (succ);
      assert (QDPLL_SCOPE_EXISTS (s->scope));
      assert (UF_IS_REP (s, 0, type));
      assert (s->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 0);
      assert (s->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
              count_direct_active_refs_by_sedge (vars, s));

      assert (!s->GETQDAG (type).cnt.exists.inactive_sedge_frontier);
      s->GETQDAG (type).cnt.exists.inactive_sedge_frontier = 1;

      /* Collect all universal candidates. */
      Edge **p, **e;
      for (p = s->GETQDAG (type).dedge_pq.elems_start,
           e = s->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notinact_costs++;
#endif
          Var *d = VARID2VARPTR (vars, (*p)->tail_var);
          assert (QDPLL_SCOPE_FORALL (d->scope));
          assert (UF_IS_REP (d, 0, type));

          if (!d->GETQDAG (type).mark_is_candidate
              && is_candidate_by_frontier (dm, vars, d))
            collect_class_as_candidate (dm, vars, d);
#ifndef NDEBUG
          else
            {
              /* assert no member is candidate. */
            }
#endif
        }

      /* Push all c-children which are not referenced by active s-edge. */
      VarID cid;
      Var *c;
      for (cid = s->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notinact_costs++;
#endif
          c = VARID2VARPTR (vars, cid);
          if (c->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 0)
            QDPLL_PUSH_STACK (mm, succ, c);
#ifndef NDEBUG
          else
            {
              /* all d-edge-tail-vars of 'c' are actively referenced by exist. var. */
            }
#endif
        }
    }

  QDPLL_DELETE_STACK (mm, succ);
}


#ifndef NDEBUG
static void
update_active_refs_by_exist_var_count (QDPLLDepManQDAG * dm, Var * var,
                                       const int delta)
{
  assert (delta == -1 || delta == 1);
  assert (QDPLL_SCOPE_EXISTS (var->scope));
  assert (delta != -1 || QDPLL_VAR_MARKED_PROPAGATED (var));
  assert (delta != 1 || !QDPLL_VAR_MARKED_PROPAGATED (var));
  Var *vars = dm->pcnf->vars;
  unsigned int i, end;
  Edge *s;
  end = var->GETQDAG (type).dedges.size;
  for (i = 0; i < end; i++)
    for (s = var->GETQDAG (type).dedges.table[i]; s; s = s->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notinact_costs++;
#endif
        Var *svar = VARID2VARPTR (vars, s->head_var);
        assert (s->tail_var == var->id);
        assert (QDPLL_SCOPE_FORALL (svar->scope));
        assert (var->scope->nesting < svar->scope->nesting);
        assert (UF_IS_REP (svar, 0, type));
        assert (delta != -1
                || svar->GETQDAG (type).cnt.
                forall.active_direct_refs_by_exist_var > 0);
        svar->GETQDAG (type).cnt.forall.active_direct_refs_by_exist_var +=
          delta;
        assert (svar->GETQDAG (type).cnt.
                forall.active_direct_refs_by_exist_var ==
                count_direct_active_refs_by_exist_var (vars, svar));
      }

}
#endif


static void
notify_inactive_exists (QDPLLDepManQDAG * dm, Var * inactive_var,
                        Var * inactive_class)
{
#if COMPUTE_STATS
  dm->stats.num_total_notinact_exists_calls++;
#endif
  const QDPLLDepManType type = dm->dmg.type;
  Var *vars = dm->pcnf->vars;
  assert (QDPLL_SCOPE_EXISTS (inactive_var->scope));
  assert (QDPLL_VAR_MARKED_PROPAGATED (inactive_var));
  assert (QDPLL_SCOPE_EXISTS (inactive_class->scope));
  assert (UF_IS_REP (inactive_class, 1, type));
  assert (count_non_propagated_in_class (vars, inactive_class, 1) == 0);
  assert (inactive_class->GETQDAG (type).cnt.exists.non_propagated_in_class ==
          0);

  const int rep_is_inactive = uf_find (vars, inactive_var, 0,
                                       type)->GETQDAG (type).cnt.exists.
    inactive_sedge_frontier;
#ifndef NDEBUG
  Var *inactive_var_rep = uf_find (vars, inactive_var, 0, type);
#endif
  unsigned int i, end;
  Edge *s;

  /* Update s-edges counter and, if needed, update inactive s-edge
     frontier by traversal. */
  end = inactive_class->GETQDAG (type).sedges.size;
  for (i = 0; i < end; i++)
    for (s = inactive_class->GETQDAG (type).sedges.table[i]; s;
         s = s->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notinact_costs++;
#endif
        Var *svar = VARID2VARPTR (vars, s->head_var);
        assert (s->tail_var == inactive_class->id);
        assert (QDPLL_SCOPE_EXISTS (svar->scope));
        assert (inactive_class->scope->nesting < svar->scope->nesting);
        assert (UF_IS_REP (svar, 0, type));
        assert (svar->GETQDAG (type).cedges.cpar == inactive_var_rep->id);
        assert (svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge >
                0);
        svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge--;
        assert (svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
                count_direct_active_refs_by_sedge (vars, svar));

        if (rep_is_inactive &&
            svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 0)
          get_universal_candidates_top_down (dm, svar);
      }
}


static int
referenced_by_active_universal_class (Var * vars, Var * v)
{
  assert (QDPLL_SCOPE_EXISTS (v->scope));
  assert (UF_IS_REP (v, 0, type));
  assert (count_direct_active_refs_by_univ_class (vars, v) ==
          v->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class);
  return (v->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class != 0);
}


static void
get_candidate_and_successors (QDPLLDepManQDAG * dm, Var * dvar)
{
  assert (QDPLL_SCOPE_EXISTS (dvar->scope));
  assert (UF_IS_REP (dvar, 0, type));
  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  VarPtrStack succ;
  QDPLL_INIT_STACK (succ);

  assert (dvar->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class ==
          0);
  assert (!referenced_by_active_universal_class (vars, dvar));
  assert (!dvar->GETQDAG (type).mark_is_candidate);
  QDPLL_PUSH_STACK (mm, succ, dvar);

  while (!QDPLL_EMPTY_STACK (succ))
    {
#if COMPUTE_STATS
      dm->stats.num_total_notinact_costs++;
#endif
      Var *s = QDPLL_POP_STACK (succ);
      assert (QDPLL_SCOPE_EXISTS (s->scope));
      assert (UF_IS_REP (s, 0, type));
      assert (!referenced_by_active_universal_class (vars, s));
      assert (s->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class ==
              0);

      assert (!s->GETQDAG (type).mark_is_candidate);
      collect_class_as_candidate (dm, vars, s);

      /* Push c-children not referenced by an active universal class. */
      Var *c;
      VarID cid;
      for (cid = s->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notinact_costs++;
#endif
          c = VARID2VARPTR (vars, cid);
          if (c->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class ==
              0)
            QDPLL_PUSH_STACK (mm, succ, c);
          else
            {
              assert (!c->GETQDAG (type).mark_is_candidate);
              assert (referenced_by_active_universal_class (vars, c));
#ifndef NDEBUG
#if QDAG_ASSERT_GET_EXIST_CANDIDATES_MEMBERS
              if (!UF_IS_SINGLETON_SET (c, 0, type))
                {
                  Var *m;
                  VarID mid;
                  for (mid = c->GETQDAG (type).uf[0].members.list.first; mid;
                       mid = m->GETQDAG (type).uf[0].members.link.next)
                    {
                      m = VARID2VARPTR (vars, mid);
                      assert (!m->GETQDAG (type).mark_is_candidate);
                    }
                }
#endif
#endif
            }
          /* If 's' is referenced by active universal class, then 
             so are all c-successors. Must stop traversal at this point. */
        }
    }

  QDPLL_DELETE_STACK (mm, succ);
}


/* A universal class 'inactive_class' has become inactive. Check if
   there are variables (classes) 'y' in D^{*}(inactive_var) where 'y'
   does not depend on any other universal variable. This can be done
   by checking forest ancestors of d-edges of 'inactive_var'. Collect
   any candidates. */
static void
notify_inactive_forall (QDPLLDepManQDAG * dm, Var * inactive_class)
{
#if COMPUTE_STATS
  dm->stats.num_total_notinact_forall_calls++;
#endif
  Var *vars = dm->pcnf->vars;
  assert (QDPLL_SCOPE_FORALL (inactive_class->scope));
  assert (UF_IS_REP (inactive_class, 0, type));
  assert (count_non_propagated_in_class (vars, inactive_class, 0) == 0);
  assert (inactive_class->GETQDAG (type).cnt.forall.non_propagated_in_class ==
          0);

  /* All references from universal class 'inactive_class' are inactive
     now. Decrement counter in existential head-variables of references;
     if any counter goes down to zero, then this variable is not
     referenced actively any more. */
  unsigned int i, end = inactive_class->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = inactive_class->GETQDAG (type).dedges.table[i]; d;
         d = d->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notinact_costs++;
#endif
        Var *dvar = VARID2VARPTR (vars, d->head_var);
        assert (!dvar->GETQDAG (type).mark_is_candidate);
        assert (d->tail_var == inactive_class->id);
        assert (QDPLL_SCOPE_EXISTS (dvar->scope));
        assert (inactive_class->scope->nesting < dvar->scope->nesting);
        assert (UF_IS_REP (dvar, 0, type));

        assert (dvar->GETQDAG (type).cnt.
                exists.active_direct_refs_by_univ_class != 0);
        dvar->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class--;
        assert (dvar->GETQDAG (type).cnt.
                exists.active_direct_refs_by_univ_class ==
                count_direct_active_refs_by_univ_class (vars, dvar));

        if (dvar->GETQDAG (type).cnt.
            exists.active_direct_refs_by_univ_class == 0)
          {
            assert (!referenced_by_active_universal_class (vars, dvar));
            /* Here, 'dvar' is not referenced by an active universal
               variable. Must also check if parent is candidate
               already. If so, then can start traversal to collect new
               candidates. */
            VarID parid = dvar->GETQDAG (type).cedges.cpar;
            Var *par = parid ? VARID2VARPTR (vars, parid) : 0;
            if (!par || par->GETQDAG (type).mark_is_candidate)
              get_candidate_and_successors (dm, dvar);
          }
      }
}


static void
undo_get_universal_candidates_top_down (QDPLLDepManQDAG * dm, Var * var)
{
  assert (QDPLL_SCOPE_EXISTS (var->scope));
  assert (UF_IS_REP (var, 0, type));
  Var *vars = dm->pcnf->vars;
  assert (var->GETQDAG (type).cnt.exists.inactive_sedge_frontier);
  assert (var->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 1);
  assert (var->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
          count_direct_active_refs_by_sedge (vars, var));
#ifndef NDEBUG
#if QDAG_ASSERT_INACTIVE_SEDGE_FRONTIER
  if (var->GETQDAG (type).cedges.cpar)
    assert_inactive_sedge_frontier_by_ancestors (dm,
                                                 VARID2VARPTR (vars,
                                                               var->GETQDAG
                                                               (type).cedges.
                                                               cpar));
#endif
#endif
  QDPLLMemMan *mm = dm->mm;
  VarPtrStack succ;
  QDPLL_INIT_STACK (succ);

  QDPLL_PUSH_STACK (mm, succ, var);

  /* Propagate inactive s-edge frontier downwards. */
  while (!QDPLL_EMPTY_STACK (succ))
    {
#if COMPUTE_STATS
      dm->stats.num_total_notact_costs++;
#endif
      Var *s = QDPLL_POP_STACK (succ);
      assert (QDPLL_SCOPE_EXISTS (s->scope));
      assert (UF_IS_REP (s, 0, type));
      assert (s == var
              || s->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
              0);
      assert (s->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
              count_direct_active_refs_by_sedge (vars, s));

      assert (s->GETQDAG (type).cnt.exists.inactive_sedge_frontier);
      s->GETQDAG (type).cnt.exists.inactive_sedge_frontier = 0;

      /* "Reset" all universal candidates. */
      Edge **p, **e;
      for (p = s->GETQDAG (type).dedge_pq.elems_start,
           e = s->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notact_costs++;
#endif
          Var *d = VARID2VARPTR (vars, (*p)->tail_var);
          assert (QDPLL_SCOPE_FORALL (d->scope));
          assert (UF_IS_REP (d, 0, type));
          assert (referenced_by_active_existential_var (vars, d));

          if (d->GETQDAG (type).mark_is_candidate)
            {
              undo_collect_class_as_candidate (dm, vars, d);
            }
        }

      /* Push all c-children which are not directly referenced by
         active s-edge. Such ones are now indirectly referenced by active
         variable. */
      VarID cid;
      Var *c;
      for (cid = s->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notact_costs++;
#endif
          c = VARID2VARPTR (vars, cid);
          if (c->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge == 0)
            QDPLL_PUSH_STACK (mm, succ, c);
#ifndef NDEBUG
          else
            {
              /* all d-edge-tail-vars of 'c' are actively referenced by exist. var. */
              assert (!c->GETQDAG (type).cnt.exists.inactive_sedge_frontier);
            }
#endif
        }
    }

  QDPLL_DELETE_STACK (mm, succ);
}


/* This is very similar to 'notify-inactive-exists'. */
static void
notify_active_exists (QDPLLDepManQDAG * dm, Var * active_var,
                      Var * active_class)
{
#if COMPUTE_STATS
  dm->stats.num_total_notact_exists_calls++;
#endif
  const QDPLLDepManType type = dm->dmg.type;
  Var *vars = dm->pcnf->vars;
  assert (QDPLL_SCOPE_EXISTS (active_var->scope));
  assert (!QDPLL_VAR_MARKED_PROPAGATED (active_var));
  assert (UF_IS_REP (active_class, 1, type));
  assert (QDPLL_SCOPE_EXISTS (active_class->scope));
  assert (active_class->GETQDAG (type).cnt.exists.non_propagated_in_class ==
          1);
  assert (count_non_propagated_in_class (vars, active_class, 1) ==
          active_class->GETQDAG (type).cnt.exists.non_propagated_in_class);

  Var *active_var_rep = uf_find (vars, active_var, 0, type);
  unsigned int i, end;
  Edge *s;

  /* Update s-edges counter and, if needed, update inactive s-edge
     frontier by traversal. */
  end = active_class->GETQDAG (type).sedges.size;
  for (i = 0; i < end; i++)
    for (s = active_class->GETQDAG (type).sedges.table[i]; s;
         s = s->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notact_costs++;
#endif
        Var *svar = VARID2VARPTR (vars, s->head_var);
        assert (s->tail_var == active_class->id);
        assert (QDPLL_SCOPE_EXISTS (svar->scope));
        assert (active_class->scope->nesting < svar->scope->nesting);
        assert (UF_IS_REP (svar, 0, type));
        assert (svar->GETQDAG (type).cedges.cpar == active_var_rep->id);

        svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge++;
        assert (svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
                count_direct_active_refs_by_sedge (vars, svar));

        if (active_var_rep->GETQDAG (type).cnt.exists.inactive_sedge_frontier
            && svar->GETQDAG (type).cnt.exists.active_direct_refs_by_sedge ==
            1)
          undo_get_universal_candidates_top_down (dm, svar);
      }
}


static void
undo_get_candidate_and_successors (QDPLLDepManQDAG * dm, Var * dvar)
{
  assert (QDPLL_SCOPE_EXISTS (dvar->scope));
  assert (UF_IS_REP (dvar, 0, type));
  QDPLLMemMan *mm = dm->mm;
  Var *vars = dm->pcnf->vars;
  VarPtrStack succ;
  QDPLL_INIT_STACK (succ);

  assert (dvar->GETQDAG (type).mark_is_candidate);
  QDPLL_PUSH_STACK (mm, succ, dvar);

  while (!QDPLL_EMPTY_STACK (succ))
    {
#if COMPUTE_STATS
      dm->stats.num_total_notact_costs++;
#endif
      Var *s = QDPLL_POP_STACK (succ);
      assert (QDPLL_SCOPE_EXISTS (s->scope));
      assert (UF_IS_REP (s, 0, type));
      assert (s->GETQDAG (type).mark_is_candidate);

      undo_collect_class_as_candidate (dm, vars, s);

      Var *c;
      VarID cid;
      for (cid = s->GETQDAG (type).cedges.cchilds.first; cid;
           cid = c->GETQDAG (type).cedges.csibs.next)
        {
#if COMPUTE_STATS
          dm->stats.num_total_notact_costs++;
#endif
          c = VARID2VARPTR (vars, cid);
          if (c->GETQDAG (type).mark_is_candidate)
            QDPLL_PUSH_STACK (mm, succ, c);
        }
    }

  QDPLL_DELETE_STACK (mm, succ);
}


static void
notify_active_forall (QDPLLDepManQDAG * dm, Var * active_class)
{
#if COMPUTE_STATS
  dm->stats.num_total_notact_forall_calls++;
#endif
  Var *vars = dm->pcnf->vars;
  assert (UF_IS_REP (active_class, 0, type));
  assert (QDPLL_SCOPE_FORALL (active_class->scope));
  assert (active_class->GETQDAG (type).cnt.forall.non_propagated_in_class ==
          1);
  assert (count_non_propagated_in_class (vars, active_class, 0) ==
          active_class->GETQDAG (type).cnt.forall.non_propagated_in_class);

  unsigned int i, end = active_class->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = active_class->GETQDAG (type).dedges.table[i]; d;
         d = d->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_notact_costs++;
#endif
        Var *dvar = VARID2VARPTR (vars, d->head_var);
        assert (d->tail_var == active_class->id);
        assert (QDPLL_SCOPE_EXISTS (dvar->scope));
        assert (active_class->scope->nesting < dvar->scope->nesting);
        assert (UF_IS_REP (dvar, 0, type));

        dvar->GETQDAG (type).cnt.exists.active_direct_refs_by_univ_class++;
        assert (dvar->GETQDAG (type).cnt.
                exists.active_direct_refs_by_univ_class ==
                count_direct_active_refs_by_univ_class (vars, dvar));

        if (dvar->GETQDAG (type).mark_is_candidate)
          {
            /* Unmark 'dvar' and all of its c-successors. */
            undo_get_candidate_and_successors (dm, dvar);
          }
      }
}


static void
print_candidate_list (QDPLLDepManQDAG * dm)
{
  Var *vars = dm->pcnf->vars;
  Var *c;
  VarID cid;
  for (cid = dm->candidates.first; cid;
       cid = c->GETQDAG (type).cand_link.next)
    {
      c = VARID2VARPTR (vars, cid);
      fprintf (stderr, "%d ", c->id);
    }
  fprintf (stderr, "\n");
}


static void
print_marked_candidates (QDPLLDepManQDAG * dm)
{
  Var *p, *e;
  for (p = dm->pcnf->vars, e = p + dm->pcnf->size_vars; p < e; p++)
    {
      if (p->id && p->GETQDAG (type).mark_is_candidate)
        {
          fprintf (stderr, "%d ", p->id);
        }
    }
  fprintf (stderr, "\n");
}


static Var *
depends_get_ancestor (QDPLLDepManQDAG * dm, Var * start,
                      unsigned int stop_nesting)
{
  Var *vars = dm->pcnf->vars;
  assert (QDPLL_SCOPE_EXISTS (start->scope));
  assert (UF_IS_REP (start, 0, type));
  assert (stop_nesting <= start->scope->nesting);

  Var *pvar, *prev;
  VarID pid;

  prev = pvar = start;

  while (stop_nesting < pvar->scope->nesting)
    {
#if COMPUTE_STATS
      dm->stats.num_total_depends_costs++;
#endif
      assert (QDPLL_SCOPE_EXISTS (pvar->scope));
      assert (UF_IS_REP (pvar, 0, type));
      prev = pvar;
      pid = pvar->GETQDAG (type).cedges.cpar;
      /* Abort if has no ancestor. */
      if (pid == 0)
        break;
      pvar = VARID2VARPTR (vars, pid);
    }
  assert (stop_nesting < prev->scope->nesting);
  return prev;
}


/* Check if 'y' is reachable from root classes of 'x'. This can be
   done by bottom-up travering y's forest ancestors as far as possible 
   and then checking x's root class set. */
static int
depends_forall_exists (QDPLLDepManQDAG * dm, Var * x, Var * y)
{
  const QDPLLDepManType type = dm->dmg.type;
  assert (QDPLL_SCOPE_FORALL (x->scope));
  assert (QDPLL_SCOPE_EXISTS (y->scope));
  assert (x->scope->nesting < y->scope->nesting);
  Var *vars = dm->pcnf->vars;

  Var *rep_x = uf_find (vars, x, 0, type);
  Var *rep_y = uf_find (vars, y, 0, type);

  Var *ancestor = depends_get_ancestor (dm, rep_y, x->scope->nesting);

  /* Check if (representative of) 'x' has d-edge to 'pvar', which is
     ancestor of 'y'. if so, then 'x' is connected to 'y' and there is
     dependency. */
  if (HAS_EDGE (rep_x, ancestor->id, GETQDAG (type).dedges))
    return 1;
  else
    return 0;
}


/* Similar to above function for the other case, but must now do
   upward traversal for each root class of universal variable. */
static int
depends_exists_forall (QDPLLDepManQDAG * dm, Var * x, Var * y)
{
  const QDPLLDepManType type = dm->dmg.type;
  assert (QDPLL_SCOPE_EXISTS (x->scope));
  assert (QDPLL_SCOPE_FORALL (y->scope));
  assert (x->scope->nesting < y->scope->nesting);
  Var *vars = dm->pcnf->vars;
  unsigned int stop_nesting = x->scope->nesting;
  Var *rep_x = uf_find (vars, x, 1, type);
  Var *rep_y = uf_find (vars, y, 0, type);
  unsigned int i, end = rep_y->GETQDAG (type).dedges.size;
  Edge *d;
  for (i = 0; i < end; i++)
    for (d = rep_y->GETQDAG (type).dedges.table[i]; d; d = d->chain_next)
      {
#if COMPUTE_STATS
        dm->stats.num_total_depends_costs++;
#endif
        assert (d->tail_var == rep_y->id);
        VarID head_varid = d->head_var;
        Var *head_var = VARID2VARPTR (vars, head_varid);
        assert (QDPLL_SCOPE_EXISTS (head_var->scope));
        assert (UF_IS_REP (head_var, 0, type));
        Var *ancestor = depends_get_ancestor (dm, head_var, stop_nesting);
        if (HAS_EDGE (rep_x, ancestor->id, GETQDAG (type).sedges))
          return 1;
      }
  return 0;
}


/* Given a stack of universal variables/classes, mark all those
   collected existential variables/classes where one of the universals
   depends on. */
static unsigned int
mark_inverse_depending_exists_forall (QDPLLDepManQDAG * dm, Var * vars,
                                      VarPtrStack * var_stack)
{
  QDPLLMemMan *mm = dm->mm;
  QDPLL *qdpll = dm->dmg.qdpll;
  VarPtrStack marks;
  QDPLL_INIT_STACK (marks);

  unsigned int unmarked = 0;

  Var **stack_p, **stack_e;
  for (stack_p = var_stack->start, stack_e = var_stack->top;
       stack_p < stack_e; stack_p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      Var *stack_var = *stack_p;
      assert (QDPLL_SCOPE_FORALL (stack_var->scope));
      assert (UF_IS_REP (stack_var, 0, type));

      unsigned int i, end = stack_var->GETQDAG (type).dedges.size;
      Edge *d;
      for (i = 0; i < end; i++)
        for (d = stack_var->GETQDAG (type).dedges.table[i]; d;
             d = d->chain_next)
          {
#if COMPUTE_STATS
            qdpll->stats.total_type_reduce_costs++;
#endif
            assert (d->tail_var == stack_var->id);
            VarID cur_id = d->head_var;
            assert (cur_id);
            while (cur_id)
              {
#if COMPUTE_STATS
                qdpll->stats.total_type_reduce_costs++;
#endif
                Var *cur_var = VARID2VARPTR (vars, cur_id);
                if (QDPLL_VAR_NEG_MARKED (cur_var))
                  break;
                QDPLL_VAR_NEG_MARK (cur_var);
                QDPLL_PUSH_STACK (mm, marks, cur_var);
                assert (QDPLL_SCOPE_EXISTS (cur_var->scope));
                assert (UF_IS_REP (cur_var, 0, type));
                Edge **p, **e;
                for (p = cur_var->GETQDAG (type).sedge_pq.elems_start,
                     e = cur_var->GETQDAG (type).sedge_pq.elems_top; p < e;
                     p++)
                  {
#if COMPUTE_STATS
                    qdpll->stats.total_type_reduce_costs++;
#endif
                    Edge *s = *p;
                    VarID owner_id = s->tail_var;
                    assert (owner_id);
                    Var *owner = VARID2VARPTR (vars, owner_id);
                    assert (QDPLL_SCOPE_EXISTS (owner->scope));
                    assert (UF_IS_REP (owner, 1, type));
                    /* Check if 'owner' occurs on stack then unmark -> will be skipped then. */
                    if (QDPLL_VAR_POS_MARKED (owner))
                      {
                        unmarked++;
                        QDPLL_VAR_POS_UNMARK (owner);
                      }
                  }
                cur_id = cur_var->GETQDAG (type).cedges.cpar;
              }
          }
    }

  for (stack_p = marks.start, stack_e = marks.top;
       stack_p < stack_e; stack_p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      assert (QDPLL_VAR_NEG_MARKED (*stack_p));
      QDPLL_VAR_NEG_UNMARK (*stack_p);
    }
  QDPLL_DELETE_STACK (mm, marks);
  return unmarked;
}


/* Given a stack of existential variables/classes, mark all those
   collected universal variables/classes where one of the existentials
   depends on. */
static unsigned int
mark_inverse_depending_forall_exists (QDPLLDepManQDAG * dm, Var * vars,
                                      VarPtrStack * var_stack)
{
  QDPLLMemMan *mm = dm->mm;
  QDPLL *qdpll = dm->dmg.qdpll;
  VarPtrStack marks;
  QDPLL_INIT_STACK (marks);

  unsigned int unmarked = 0;

  Var **stack_p, **stack_e;
  for (stack_p = var_stack->start, stack_e = var_stack->top;
       stack_p < stack_e; stack_p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      Var *stack_var = *stack_p;
      VarID cur_id = stack_var->id;
      assert (cur_id);
      while (cur_id)
        {
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          Var *cur_var = VARID2VARPTR (vars, cur_id);
          assert (QDPLL_SCOPE_EXISTS (cur_var->scope));
          assert (UF_IS_REP (cur_var, 0, type));
          if (QDPLL_VAR_NEG_MARKED (cur_var))
            break;
          QDPLL_VAR_NEG_MARK (cur_var);
          QDPLL_PUSH_STACK (mm, marks, cur_var);
          Edge **p, **e;
          for (p = cur_var->GETQDAG (type).dedge_pq.elems_start,
               e = cur_var->GETQDAG (type).dedge_pq.elems_top; p < e; p++)
            {
#if COMPUTE_STATS
              qdpll->stats.total_type_reduce_costs++;
#endif
              Edge *s = *p;
              VarID owner_id = s->tail_var;
              assert (owner_id);
              Var *owner = VARID2VARPTR (vars, owner_id);
              assert (QDPLL_SCOPE_FORALL (owner->scope));
              assert (UF_IS_REP (owner, 0, type));
              /* Check if 'owner_rep' occurs on stack then unmark -> will be skipped then. */
              if (QDPLL_VAR_POS_MARKED (owner))
                {
                  unmarked++;
                  QDPLL_VAR_POS_UNMARK (owner);
                }
            }
          cur_id = cur_var->GETQDAG (type).cedges.cpar;
        }
    }

  for (stack_p = marks.start, stack_e = marks.top;
       stack_p < stack_e; stack_p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      assert (QDPLL_VAR_NEG_MARKED (*stack_p));
      QDPLL_VAR_NEG_UNMARK (*stack_p);
    }
  QDPLL_DELETE_STACK (mm, marks);
  return unmarked;
}


static unsigned int
mark_inverse_depending (QDPLLDepManGeneric * dmg, VarPtrStack * var_stack,
                        const QDPLLQuantifierType type)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;
  if (type == QDPLL_QTYPE_EXISTS)
    return mark_inverse_depending_exists_forall (dm, vars, var_stack);
  else
    return mark_inverse_depending_forall_exists (dm, vars, var_stack);
}


static void
type_reduce_unmark_members (QDPLL * qdpll, Var * check_var)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = check_var->type_red_member_lits.start,
       e = check_var->type_red_member_lits.top; p < e; p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      Var *var = LIT2VARPTR (vars, *p);
      LEARN_VAR_UNMARK (var);
    }
}


static void
type_reduce_push_members (QDPLL * qdpll, Var * check_var, LitIDStack * other)
{
  QDPLLMemMan *mm = qdpll->mm;
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
  for (p = check_var->type_red_member_lits.start,
       e = check_var->type_red_member_lits.top; p < e; p++)
    {
#if COMPUTE_STATS
      qdpll->stats.total_type_reduce_costs++;
#endif
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      assert (LEARN_VAR_MARKED (var));
      QDPLL_PUSH_STACK (mm, *other, lit);
    }
}


static unsigned int
type_reduce_unmark_by_graph (QDPLL * qdpll, VarPtrStack * other_lits,
                             const QDPLLQuantifierType type)
{
  return mark_inverse_depending (qdpll->dm, other_lits, type);
}


/* Advanced version of type-reduce-by-standard-deps. */
static void
type_reduce_by_std_deps_adv (QDPLL * qdpll, LitIDStack ** lit_stack,
                             LitIDStack ** lit_stack_tmp,
                             const QDPLLQuantifierType type)
{
  Var *vars = qdpll->pcnf.vars;
  LitID *p, *e;
#ifndef NDEBUG
  assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_lits_no_holes ((*lit_stack)->start, (*lit_stack)->top);
  /* Lits must be non-empty and reduced. */
  assert (QDPLL_COUNT_STACK (**lit_stack) != 0);
#endif
  assert (type == QDPLL_QTYPE_FORALL || type == QDPLL_QTYPE_EXISTS);
  assert (!QDPLL_EMPTY_STACK (qdpll->wreason_a) || !QDPLL_EMPTY_STACK (qdpll->wreason_e));

#ifndef NDEBUG
  /* Assert that data for type-reduce was collected properly. */
  for (p = (*lit_stack)->start, e = (*lit_stack)->top; p < e; p++)
    {
      LitID lit = *p;
      assert (lit);
      Var *var = LIT2VARPTR (vars, lit);
      assert (LEARN_VAR_MARKED (var));
      assert (QDPLL_LIT_POS (lit) || LEARN_VAR_NEG_MARKED (var));
      assert (QDPLL_LIT_NEG (lit) || LEARN_VAR_POS_MARKED (var));
      if (QDPLL_SCOPE_FORALL (var->scope))
        {
          Var *rep = VARID2VARPTR (vars,
                                   qdpll->dm->get_class_rep (qdpll->dm,
                                                             var->id, 0));
          assert (QDPLL_VAR_POS_MARKED (rep));
          assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) != 0);
	  /* With long distance resolution, may have complementary literals on stack. */
          assert (is_lit_on_lit_stack (&(rep->type_red_member_lits), lit) || 
		  is_lit_on_lit_stack (&(rep->type_red_member_lits), -lit));
        }
      else
        {
          Var *rep = type == QDPLL_QTYPE_EXISTS ? VARID2VARPTR (vars,
                                                                qdpll->dm->
                                                                get_class_rep
                                                                (qdpll->dm,
                                                                 var->id,
                                                                 1)) :
            VARID2VARPTR (vars,
                          qdpll->dm->get_class_rep (qdpll->dm,
                                                    var->id, 0));
          assert (QDPLL_VAR_POS_MARKED (rep));
          assert (QDPLL_COUNT_STACK (rep->type_red_member_lits) != 0);
          assert (is_lit_on_lit_stack (&(rep->type_red_member_lits), lit));
        }
    }
#endif

#if COMPUTE_STATS
  qdpll->stats.total_type_reduce_effort +=
    (QDPLL_COUNT_STACK (qdpll->wreason_e) *
     QDPLL_COUNT_STACK (qdpll->wreason_a));
#endif

  VarPtrStack *check_lits, *other_lits;
  if (type == QDPLL_QTYPE_EXISTS)
    {
      check_lits = &(qdpll->wreason_e);
      other_lits = &(qdpll->wreason_a);
    }
  else
    {
      check_lits = &(qdpll->wreason_a);
      other_lits = &(qdpll->wreason_e);
    }

  /* Simply check literal class sets. */
  unsigned int unmarked =
    type_reduce_unmark_by_graph (qdpll, other_lits, type);

#ifndef NDEBUG
  do
    {
      /* POS-marks must still be set for all other-lits. */
      Var **p, **e;
      for (p = other_lits->start, e = other_lits->top; p < e; p++)
        assert (QDPLL_VAR_POS_MARKED (*p));
      unsigned int check_unmarked = 0;
      for (p = check_lits->start, e = check_lits->top; p < e; p++)
        {
          if (!QDPLL_VAR_POS_MARKED (*p))
            check_unmarked++;
        }
      assert (unmarked == check_unmarked);
    }
  while (0);
#endif

  Var **cp = check_lits->start, **ce = check_lits->top;
  Var **op = other_lits->start, **oe = other_lits->top;

  /* Check if literals have been reduced by checking how many classes
     were unmarked. If all are unmarked, then no reduction was
     performed. */
  if (unmarked != QDPLL_COUNT_STACK (*check_lits))
    {
      /* Traverse collected classes and immediately add irreducible
         literals to tmp-stack, unmark reducible literals. Finally swap
         stacks. Note that adding literals can be done in order as classes
         are also collected in order. */

      Var *cvar, *ovar;
      LitIDStack *other = *lit_stack_tmp;
      assert (QDPLL_EMPTY_STACK (*other));

      /* Traverse collected classes like merge-sort to add literals in
         scope order. */
      while (cp < ce && op < oe)
        {
          cvar = *cp;
          ovar = *op;
          if (cvar->scope->nesting <= ovar->scope->nesting)
            {
              if (QDPLL_VAR_POS_MARKED (cvar))
                type_reduce_unmark_members (qdpll, cvar);
              else
                type_reduce_push_members (qdpll, cvar, other);
#if COMPUTE_STATS
              qdpll->stats.total_type_reduce_costs++;
#endif
              QDPLL_VAR_UNMARK (cvar);
              QDPLL_RESET_STACK (cvar->type_red_member_lits);
              cp++;
            }
          else
            {
              /* other-lits are never reduced, e.g. exist-vars never
                 removed from clauses. */
              assert (QDPLL_VAR_POS_MARKED (ovar));
              type_reduce_push_members (qdpll, ovar, other);
#if COMPUTE_STATS
              qdpll->stats.total_type_reduce_costs++;
#endif
              QDPLL_VAR_UNMARK (ovar);
              QDPLL_RESET_STACK (ovar->type_red_member_lits);
              op++;
            }
        }
      assert (cp >= ce || op >= oe);

      while (cp < ce)
        {
          cvar = *cp;
          if (QDPLL_VAR_POS_MARKED (cvar))
            type_reduce_unmark_members (qdpll, cvar);
          else
            type_reduce_push_members (qdpll, cvar, other);
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          QDPLL_VAR_UNMARK (cvar);
          QDPLL_RESET_STACK (cvar->type_red_member_lits);
          cp++;
        }

      while (op < oe)
        {
          /* other-lits are never reduced, e.g. exist-vars never
             removed from clauses. */
          ovar = *op;
          assert (QDPLL_VAR_POS_MARKED (ovar));
          type_reduce_push_members (qdpll, ovar, other);
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          QDPLL_VAR_UNMARK (ovar);
          QDPLL_RESET_STACK (ovar->type_red_member_lits);
          op++;
        }
      /* End: adding literals in order. */

      /* Swap stacks. */
      LitIDStack *swap_tmp = *lit_stack;
      *lit_stack = *lit_stack_tmp;
      *lit_stack_tmp = swap_tmp;
      QDPLL_RESET_STACK (**lit_stack_tmp);
    }
  else
    {
      /* Reset class representatives. In the other case this is done incrementally. */
      for (cp = check_lits->start; cp < ce; cp++)
        {
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          QDPLL_VAR_UNMARK (*cp);
          QDPLL_RESET_STACK ((*cp)->type_red_member_lits);
        }
      for (cp = other_lits->start; cp < oe; cp++)
        {
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          QDPLL_VAR_UNMARK (*cp);
          QDPLL_RESET_STACK ((*cp)->type_red_member_lits);
        }
    }

  QDPLL_RESET_STACK (qdpll->wreason_a);
  QDPLL_RESET_STACK (qdpll->wreason_e);

#ifndef NDEBUG
  assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_lits_no_holes ((*lit_stack)->start, (*lit_stack)->top);
#endif
}


static void
type_reduce (QDPLLDepManGeneric * dmg,
             LitIDStack ** lit_stack, LitIDStack ** lit_stack_tmp,
             const QDPLLQuantifierType other_type, const int lits_sorted)
{
  QDPLL *qdpll = dmg->qdpll;
  assert (*lit_stack != *lit_stack_tmp);
  assert (*lit_stack != &(qdpll->add_stack)
          || *lit_stack_tmp == &(qdpll->add_stack_tmp));
  assert (*lit_stack_tmp != &(qdpll->add_stack)
          || *lit_stack == &(qdpll->add_stack_tmp));
#if COMPUTE_STATS
  qdpll->stats.total_type_reduce_calls++;
#endif
#ifndef NDEBUG
  if (lits_sorted)
    assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_lits_no_holes ((*lit_stack)->start, (*lit_stack)->top);
#endif
  assert (other_type == QDPLL_QTYPE_FORALL
          || other_type == QDPLL_QTYPE_EXISTS);

  /* Skip empty constraint. */
  if (QDPLL_COUNT_STACK (**lit_stack) == 0)
    return;

#if COMPUTE_STATS
  unsigned int num_lits_before_reduction = QDPLL_COUNT_STACK(**lit_stack);
#endif

  if (qdpll->options.depman_simple)
    {
      if (!lits_sorted)
        {
          /* We should never call this function if the literal set is not
             sorted since sorting is too costly. */
          QDPLL_ABORT_DEPMAN (1, "reached expected dead code!");
          unsigned int cnt = QDPLL_COUNT_STACK (**lit_stack);
          QDPLL_SORT (qdpll, int, compare_lits_by_variable_nesting,
                      (*lit_stack)->start, cnt);
        }

      /* Reduce literals by scope order. */
      Var *lit_var, *vars = qdpll->pcnf.vars;
      LitID lit, *elemp, *start = (*lit_stack)->start;
      while (start <= (elemp = (*lit_stack)->top - 1))
        {
#if COMPUTE_STATS
          qdpll->stats.total_type_reduce_costs++;
#endif
          lit = *elemp;
          lit_var = LIT2VARPTR (vars, lit);
          if (!lit_var->is_internal && other_type != lit_var->scope->type)
            {
              LEARN_VAR_UNMARK (lit_var);
              QDPLL_POP_STACK (**lit_stack);
              if (qdpll->options.verbosity > 1)
                {
                  if (other_type == QDPLL_QTYPE_EXISTS)
                    fprintf (stderr,
                             "CDCL: type-reducing lit %d by ordering\n", lit);
                  else
                    fprintf (stderr,
                             "SDCL: type-reducing lit %d by ordering\n", lit);
                }
            }
          else
            break;
        }
    }
  else
    {
      /* Must not use dependency scheme other than trivial one (i.e. linear
         ordering) when using incremental mode. */
      assert (!qdpll->options.incremental_use);
      type_reduce_by_std_deps_adv (qdpll, lit_stack, lit_stack_tmp,
                                   other_type ==
                                   QDPLL_QTYPE_EXISTS ? QDPLL_QTYPE_FORALL
                                   : QDPLL_QTYPE_EXISTS);
      if (!lits_sorted)
        {
          /* We should never call this function if the literal set is not
             sorted since sorting is too costly. */
          QDPLL_ABORT_DEPMAN (1, "reached expected dead code!");
          unsigned int cnt = QDPLL_COUNT_STACK (**lit_stack);
          QDPLL_SORT (qdpll, int, compare_lits_by_variable_nesting,
                      (*lit_stack)->start, cnt);
        }
    }

#if COMPUTE_STATS
  qdpll->stats.total_type_reduce_lits += 
    (num_lits_before_reduction - QDPLL_COUNT_STACK(**lit_stack));
#endif

#ifndef NDEBUG
  assert_lits_sorted (qdpll, (*lit_stack)->start, (*lit_stack)->top);
  assert_lits_no_holes ((*lit_stack)->start, (*lit_stack)->top);
#endif
}


/* -------------------- END: INTERNAL FUNCTIONS -------------------- */


/* -------------------- START: CORE FUNCTIONS -------------------- */
static void
qdpll_dep_man_init (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  const QDPLLDepManType type = dmg->type;
  const double init_start_time = time_stamp ();
  const char *type_string =
    (dm->dmg.type == QDPLL_DEPMAN_TYPE_SIMPLE) ? "simple" : "qdag";

  assert (!dm->state.init);
  QDPLL_ABORT_DEPMAN (dm->state.init,
                      "dependency manager already initialized.");
  dm->state.init = 1;

  /* Traverse all scopes, make-set on all variables, link singleton
     classes to scope's list of equivalence classes.  
     NOTE: This could also be done right after variables have been added to 
     scope by user. */
  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      VarID *p, *e;
      Var *vars = dm->pcnf->vars;
      for (p = s->vars.start, e = s->vars.top; p < e; p++)
        {
          Var *var = VARID2VARPTR (vars, *p);
          assert (!QDPLL_VAR_MARKED_PROPAGATED (var));
          assert (!var->GETQDAG (type).uf[0].par);
          assert (!var->GETQDAG (type).uf[1].par);
          uf_make_set (var, 0);
          VAR_LINK (vars, s->GETPART (type).classes[0], var,
                    GETQDAG (type).uf[0].class_link);
          if (QDPLL_SCOPE_EXISTS (s))
            {
              uf_make_set (var, 1);
              VAR_LINK (vars, s->GETPART (type).classes[1], var,
                        GETQDAG (type).uf[1].class_link);
            }
        }
    }

  if (dm->dmg.type == QDPLL_DEPMAN_TYPE_QDAG)
    extract_dependencies (dm);
  else if (dm->dmg.type == QDPLL_DEPMAN_TYPE_SIMPLE)
    build_linear_dependency_graph (dm);
  else
    {
      QDPLL_ABORT_DEPMAN (1, "invalid dependency manager!");
    }

  fill_candidates (dm);

#ifndef NDEBUG
#if QDAG_ASSERT_CANDIDATE_MARKS_BY_REMARKING
  assert_candidate_marks_by_remarking (dm);
#endif
#endif
  if (dmg->qdpll->options.verbosity > 0)
    {
      fprintf (stderr, "DM %s: init-time: %f\n", type_string,
               time_stamp () - init_start_time);
    }
}


/* Allocate memory for edge tables and priority queues. This can be redundant 
   for some variables, especially from innermost scope. */
static void
qdpll_dep_man_notify_init_variable (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (id > 0 && id < dm->pcnf->size_vars);
  QDPLLMemMan *mm = dm->mm;
  Var *v = VARID2VARPTR (dm->pcnf->vars, id);
  assert (!v->GETQDAG (type).dedges.table);
  et_init (mm, &(v->GETQDAG (type).dedges), DEFAULT_EDGE_TABLE_SIZE);
  assert (!v->GETQDAG (type).sedges.table);
  et_init (mm, &(v->GETQDAG (type).sedges), DEFAULT_EDGE_TABLE_SIZE);
  assert (!v->GETQDAG (type).dedge_pq.elems_start);
  pq_init (mm, &(v->GETQDAG (type).dedge_pq), DEFAULT_EDGE_PQUEUE_SIZE);
  assert (!v->GETQDAG (type).sedge_pq.elems_start);
  pq_init (mm, &(v->GETQDAG (type).sedge_pq), DEFAULT_EDGE_PQUEUE_SIZE);
}


/* De-allocate memory for edge tables and priority queues for given variable. */
static void
qdpll_dep_man_notify_reset_variable (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (id > 0 && id < dm->pcnf->size_vars);
  QDPLLMemMan *mm = dm->mm;
  Var *v = VARID2VARPTR (dm->pcnf->vars, id);
  unsigned int i, end;
  Edge *d, *n;

  if (v->GETQDAG (type).dedges.table)
    {
      assert (v->GETQDAG (type).dedges.size > 0);
      /* Delete edges in table. */
      end = v->GETQDAG (type).dedges.size;
      for (i = 0; i < end; i++)
        for (d = v->GETQDAG (type).dedges.table[i]; d; d = n)
          {
            n = d->chain_next;
            delete_edge (mm, d);
          }
      et_delete (mm, &(v->GETQDAG (type).dedges));
    }

  if (v->GETQDAG (type).sedges.table)
    {
      assert (v->GETQDAG (type).dedges.size > 0);
      /* Delete edges in table. */
      end = v->GETQDAG (type).sedges.size;
      for (i = 0; i < end; i++)
        for (d = v->GETQDAG (type).sedges.table[i]; d; d = n)
          {
            n = d->chain_next;
            delete_edge (mm, d);
          }
      et_delete (mm, &(v->GETQDAG (type).sedges));
    }

  /* Edges already deleted, can free pqueues immediately. */
  if (v->GETQDAG (type).dedge_pq.elems_start)
    pq_delete (mm, &(v->GETQDAG (type).dedge_pq));
  if (v->GETQDAG (type).sedge_pq.elems_start)
    pq_delete (mm, &(v->GETQDAG (type).sedge_pq));
}


static void
qdpll_dep_man_reset (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;

  Var *p, *e;
  for (p = dm->pcnf->vars, e = p + dm->pcnf->size_vars; p < e; p++)
    {
      if (p->id)
        {
          /* NOTE: here we also release memory held by QDAG. This is
             actually not needed and can be optimized. */
          qdpll_dep_man_notify_reset_variable (dmg, p->id);
          memset (&(p->GETQDAG (type)), 0, sizeof (QDAG));
          qdpll_dep_man_notify_init_variable (dmg, p->id);
          assert (!p->GETQDAG (type).mark_is_candidate);
          assert (!p->GETQDAG (type).mark_is_candidate_debug);
          assert (!p->GETQDAG (type).mark_notified_inactive);
        }
    }

  /* Reset data in dep-man. */
  dm->state.init = 0;
  dm->candidates.first = dm->candidates.last = 0;
#if COMPUTE_STATS
  dm->stats.num_cur_inactive = 0;
  dm->stats.num_cur_active_cands = 0;
#endif

  /* Reset class links in scopes. */
  Scope *s;
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      s->GETPART (type).classes[0].first = s->GETPART (type).classes[0].last =
        0;
      s->GETPART (type).classes[1].first = s->GETPART (type).classes[1].last =
        0;
    }
}


static VarID
qdpll_dep_man_get_candidate (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (dm->state.init);

#if COMPUTE_STATS
  dm->stats.num_total_get_cand_costs++;
#endif

  VarID result;
  if ((result = dm->candidates.first))
    {
      Var *vars = dm->pcnf->vars;
      Var *r = VARID2VARPTR (vars, result);
      VAR_UNLINK (vars, dm->candidates, r, GETQDAG (type).cand_link);
    }

  /* ---------------------------------------- */
#if COMPUTE_STATS
  /* Assumption: solver calls 'get-candidate' only at decision
     points. If all candidates have been exported then collect
     statistics. */
  if (!result)
    {
      /* All candidates exported. */
      unsigned long long int cur = dm->stats.num_total_get_cand_costs -
        dm->stats.num_total_get_cand_costs_at_last_dp;
      assert (cur <= dm->stats.num_total_get_cand_costs);
      if (cur > dm->stats.num_max_get_cand_costs)
        dm->stats.num_max_get_cand_costs = cur;
      dm->stats.num_total_get_cand_costs_at_last_dp =
        dm->stats.num_total_get_cand_costs;

      assert (dm->dmg.qdpll->assigned_vars_top == dm->dmg.qdpll->bcp_ptr);
#ifndef NDEBUG
      /* Check collected statistics at decision points */
      unsigned long long int check_active_cands = 0,
        check_inactive = 0, check_active = 0;
      Var *p, *e;
      for (p = dm->pcnf->vars, e = p + dm->pcnf->size_vars; p < e; p++)
        {
          if (p->id)
            {
              if (QDPLL_VAR_MARKED_PROPAGATED (p))
                check_inactive++;
              else
                check_active++;
              if (!QDPLL_VAR_MARKED_PROPAGATED (p)
                  && p->GETQDAG (type).mark_is_candidate)
                check_active_cands++;
            }
        }
      assert (check_active_cands == dm->stats.num_cur_active_cands);
      assert (check_inactive == dm->stats.num_cur_inactive);
      assert (check_active ==
              dm->pcnf->used_vars - dm->stats.num_cur_inactive);
#endif

      /* Cumulative statistics. */
      dm->stats.num_decision_points++;
      dm->stats.num_total_active_cands_at_dp +=
        dm->stats.num_cur_active_cands;
      dm->stats.num_total_active_vars_at_dp +=
        (dm->pcnf->used_vars - dm->stats.num_cur_inactive);
      dm->stats.num_total_ratio_active_cands_per_active_vars +=
        ((long double) dm->stats.num_cur_active_cands) /
        (dm->pcnf->used_vars - dm->stats.num_cur_inactive);
    }
#endif
  /* ---------------------------------------- */

  return result;
}

static void
qdpll_dep_man_notify_inactive (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  const QDPLLDepManType type = dmg->type;
  assert (id > 0 && id < dm->pcnf->size_vars);
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;
  Var *inactive_var = VARID2VARPTR (vars, id);
  assert (QDPLL_VAR_MARKED_PROPAGATED (inactive_var));
#if (COMPUTE_STATS || !defined(NDEBUG))
  assert (!inactive_var->GETQDAG (type).mark_notified_inactive);
  inactive_var->GETQDAG (type).mark_notified_inactive = 1;
#endif
#if COMPUTE_STATS
  unsigned long long int old_total_costs = dm->stats.num_total_notinact_costs;
  dm->stats.num_total_notinact_costs++;
  dm->stats.num_total_notinact_calls++;
  dm->stats.num_cur_inactive++;
  if (inactive_var->GETQDAG (type).mark_is_candidate)
    {
      assert (dm->stats.num_cur_active_cands > 0);
      dm->stats.num_cur_active_cands--;
    }
#endif

  Var *rep;
  if (QDPLL_SCOPE_EXISTS (inactive_var->scope))
    {
#ifndef NDEBUG
      /* Decrement active reference counter in universal classes. */
      /* NOTE: for testing only, we can do without this counter. */
      update_active_refs_by_exist_var_count (dm, inactive_var, -1);
#endif
      rep = uf_find (vars, inactive_var, 1, type);
      assert (rep->GETQDAG (type).cnt.exists.non_propagated_in_class);
      rep->GETQDAG (type).cnt.exists.non_propagated_in_class--;
      assert (rep->GETQDAG (type).cnt.exists.non_propagated_in_class ==
              count_non_propagated_in_class (vars, rep, 1));
      /* Need only notify if non-propagated-count goes from 1 to 0. */
      if (rep->GETQDAG (type).cnt.exists.non_propagated_in_class == 0)
        notify_inactive_exists (dm, inactive_var, rep);
    }
  else
    {
      assert (QDPLL_SCOPE_FORALL (inactive_var->scope));
      rep = uf_find (vars, inactive_var, 0, type);
      assert (rep->GETQDAG (type).cnt.forall.non_propagated_in_class);
      rep->GETQDAG (type).cnt.forall.non_propagated_in_class--;
      assert (rep->GETQDAG (type).cnt.forall.non_propagated_in_class ==
              count_non_propagated_in_class (vars, rep, 0));
      /* Need only notify if non-propagated-count goes from 1 to 0. */
      if (rep->GETQDAG (type).cnt.forall.non_propagated_in_class == 0)
        notify_inactive_forall (dm, rep);
    }

#if COMPUTE_STATS
  unsigned long long int cur =
    dm->stats.num_total_notinact_costs - old_total_costs;
  assert (cur <= dm->stats.num_total_notinact_costs);
  if (cur > dm->stats.num_max_notinact_costs)
    dm->stats.num_max_notinact_costs = cur;
#endif
#ifndef NDEBUG
#if QDAG_ASSERT_CANDIDATE_LIST
  assert_candidate_list (dm);
#endif
#if QDAG_ASSERT_CANDIDATE_MARKS_BY_REMARKING
  assert_candidate_marks_by_remarking (dm);
#endif
#endif
}


static void
qdpll_dep_man_notify_active (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  const QDPLLDepManType type = dmg->type;
  assert (id > 0 && id < dm->pcnf->size_vars);
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;
  Var *active_var = VARID2VARPTR (vars, id);
  assert (!QDPLL_VAR_MARKED_PROPAGATED (active_var));
#if (COMPUTE_STATS || !defined(NDEBUG))
  assert (active_var->GETQDAG (type).mark_notified_inactive);
  active_var->GETQDAG (type).mark_notified_inactive = 0;
#endif
#if COMPUTE_STATS
  unsigned long long int old_total_costs = dm->stats.num_total_notact_costs;
  dm->stats.num_total_notact_calls++;
  dm->stats.num_total_notact_costs++;
  assert (dm->stats.num_cur_inactive > 0);
  dm->stats.num_cur_inactive--;
  if (active_var->GETQDAG (type).mark_is_candidate)
    {
      assert (dm->stats.num_cur_active_cands < dm->pcnf->used_vars);
      dm->stats.num_cur_active_cands++;
    }
#endif

  Var *rep;
  if (QDPLL_SCOPE_EXISTS (active_var->scope))
    {
#ifndef NDEBUG
      /* Increment active reference counter in universal classes. */
      /* NOTE: for testing only, we can do without this counter. */
      update_active_refs_by_exist_var_count (dm, active_var, 1);
#endif
      rep = uf_find (vars, active_var, 1, type);
      rep->GETQDAG (type).cnt.exists.non_propagated_in_class++;
      assert (count_non_propagated_in_class (vars,
                                             rep, 1) ==
              rep->GETQDAG (type).cnt.exists.non_propagated_in_class);
      /* NOTE: need only notify if non-propagated-count goes from 0 to 1. */
      if (rep->GETQDAG (type).cnt.exists.non_propagated_in_class == 1)
        notify_active_exists (dm, active_var, rep);
    }
  else
    {
      assert (QDPLL_SCOPE_FORALL (active_var->scope));
      Var *rep = uf_find (vars, active_var, 0, type);
      rep->GETQDAG (type).cnt.forall.non_propagated_in_class++;
      assert (count_non_propagated_in_class (vars,
                                             rep, 0) ==
              rep->GETQDAG (type).cnt.forall.non_propagated_in_class);
      /* NOTE: need only notify if non-propagated-count goes from 0 to 1. */
      if (rep->GETQDAG (type).cnt.forall.non_propagated_in_class == 1)
        notify_active_forall (dm, rep);
    }

  /* Link active-var to candidates again, if is candidate. Check, if not already in list. */
  if (active_var->GETQDAG (type).mark_is_candidate)
    {
      if (!active_var->GETQDAG (type).cand_link.prev
          && !active_var->GETQDAG (type).cand_link.next
          && id != dm->candidates.first)
        VAR_LINK (vars, dm->candidates, active_var, GETQDAG (type).cand_link);
    }

#if COMPUTE_STATS
  unsigned long long int cur =
    dm->stats.num_total_notact_costs - old_total_costs;
  assert (cur <= dm->stats.num_total_notact_costs);
  if (cur > dm->stats.num_max_notact_costs)
    dm->stats.num_max_notact_costs = cur;
#endif
#ifndef NDEBUG
#if QDAG_ASSERT_CANDIDATE_LIST
  assert_candidate_list (dm);
#endif
#if QDAG_ASSERT_CANDIDATE_MARKS_BY_REMARKING
  assert_candidate_marks_by_remarking (dm);
#endif
#endif
}


static int
qdpll_dep_man_is_candidate (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (id > 0 && id < dm->pcnf->size_vars);
  assert (dm->state.init);
  Var *v = VARID2VARPTR (dm->pcnf->vars, id);
  return v->GETQDAG (type).mark_is_candidate;
}


static int
qdpll_dep_man_is_init (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  return dm->state.init;
}


/* 'print_deps' function. */
static void
qdpll_dep_man_print_deps_by_graph (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (id > 0 && id < dm->pcnf->size_vars);
  assert (dm->state.init);
  Var *v = VARID2VARPTR (dm->pcnf->vars, id);

  /* Handle uninitialized variables. */
  if (!v->id)
    {
      fprintf (stdout, "unused");
      return;
    }

  /* Handle top-level vars. */
  if (QDPLL_VAR_MARKED_PROPAGATED (v)
          && v->decision_level <= 0)
    {
      fprintf (stdout, "disabled");
      return;
    }

  QDPLLMemMan *mm = dm->mm;
  VarPtrStack deps;
  QDPLL_INIT_STACK (deps);

  collect_deps_from_graph (dm, &deps, v);
  unmark_dependency_marks (&deps);
  qsort (deps.start, QDPLL_COUNT_STACK (deps),
         sizeof (*deps.start), qsort_compare_deps_by_id);

  Var **p, **e;
  for (p = deps.start, e = deps.top; p < e; p++)
    {
      Var *d = *p;
      fprintf (stdout, "%u ", d->id);
    }
  fprintf (stdout, "0");
  QDPLL_DELETE_STACK (mm, deps);
}

/* 'print_deps' function. */
static void
qdpll_dep_man_print_deps_by_search (QDPLLDepManGeneric * dmg, VarID id)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (id > 0 && id < dm->pcnf->size_vars);
  assert (dm->state.init);
  Var *v = VARID2VARPTR (dm->pcnf->vars, id);

  /* Handle uninitialized variables. */
  if (!v->id)
    {
      fprintf (stdout, "unused");
      return;
    }

  /* Handle top-level vars. */
  if (QDPLL_VAR_MARKED_PROPAGATED (v)
          && v->decision_level <= 0)
    {
      fprintf (stdout, "disabled");
      return;
    }

  QDPLLMemMan *mm = dm->mm;
  VarPtrStack deps;
  QDPLL_INIT_STACK (deps);

  collect_deps_from_cnf (dm, &deps, v);
  unmark_dependency_marks (&deps);
  qsort (deps.start, QDPLL_COUNT_STACK (deps),
         sizeof (*deps.start), qsort_compare_deps_by_id);

  Var **p, **e;
  for (p = deps.start, e = deps.top; p < e; p++)
    {
      Var *d = *p;
      fprintf (stdout, "%u ", d->id);
    }
  fprintf (stdout, "0");
  QDPLL_DELETE_STACK (mm, deps);
}


#define PRINT_EDGES(v, edges, style, tag, htag)				\
  do {									\
    end = v->GETQDAG(type).edges.size;					\
    for (i = 0; i < end; i++)						\
      for (d = v->GETQDAG(type).edges.table[i]; d; d = d->chain_next)	\
        {                                                                \
          fprintf (stdout, "  %c%d -> %c%d[style=%s];\n", tag, v->id,	\
                   htag, VARID2VARPTR(vars, d->head_var)->id, style);	\
        }                                                                \
  } while(0)


static void
qdpll_dep_man_dump_dep_graph (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;

  fprintf (stdout, "digraph qdag {\n");

  Scope *s;
  VarID vid, mid, nid;
  Var *v, *m, *n;
  char tag;
  char *shape;
  const char *dedge_style = "solid";
  const char *cedge_style = "dotted";
  const char *cedge_member_style = "solid";
  const char *cedge_member_color = "blue";
  const char *rep_peripheries = "2";

  /* First, declare variables. */
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      fprintf (stdout, "  { rank=same;\n");
      tag = QDPLL_SCOPE_EXISTS (s) ? 'e' : 'a';
      shape = QDPLL_SCOPE_EXISTS (s) ? "diamond" : "box";
      VarID *p, *e;
      for (p = s->vars.start, e = s->vars.top; p < e; p++)
        {
          v = VARID2VARPTR (vars, *p);
          if (UF_IS_REP (v, 0, type))
            fprintf (stdout, "    %c%d[shape=%s, peripheries=%s];\n", tag,
                     v->id, shape, rep_peripheries);
          else
            fprintf (stdout, "    %c%d[shape=%s];\n", tag, v->id, shape);
        }
      fprintf (stdout, "  }\n");
    }

  Edge *d;
  unsigned int htag, i, end;

  /* next, traverse vars and insert edges */
  for (s = dm->pcnf->scopes.first; s; s = s->link.next)
    {
      tag = QDPLL_SCOPE_EXISTS (s) ? 'e' : 'a';
      htag = tag == 'e' ? 'a' : 'e';

#if 1
      /* dummy edge between first classes of scopes */
      if (s->GETPART (type).classes[0].first && s->link.next
          && s->link.next->GETPART (type).classes[0].first)
        fprintf (stdout, "%c%d -> %c%d[style=invisible, arrowhead=none]\n",
                 tag, VARID2VARPTR (vars,
                                    s->GETPART (type).classes[0].first)->id,
                 htag, VARID2VARPTR (vars,
                                     s->link.next->GETPART (type).
                                     classes[0].first)->id);
#endif

      for (vid = s->GETPART (type).classes[0].first; vid;
           vid = v->GETQDAG (type).uf[0].class_link.next)
        {
          v = VARID2VARPTR (vars, vid);

          /* dummy-edge between classes of scope */
          if (v->GETQDAG (type).uf[0].class_link.next)
            fprintf (stdout,
                     "%c%d -> %c%d[style=invisible, arrowhead=none]\n", tag,
                     v->id, tag, VARID2VARPTR (vars,
                                               v->GETQDAG (type).
                                               uf[0].class_link.next)->id);
#if 1
          PRINT_EDGES (v, dedges, dedge_style, tag, htag);
          if (QDPLL_SCOPE_EXISTS (v->scope))
            PRINT_EDGES (v, sedges, cedge_style, tag, tag);
#endif

          /* print c-edges of rep. */
          if (QDPLL_SCOPE_EXISTS (v->scope))
            for (mid = v->GETQDAG (type).cedges.cchilds.first; mid;
                 mid = m->GETQDAG (type).cedges.csibs.next)
              {
                m = VARID2VARPTR (vars, mid);
                fprintf (stdout, "  %c%d -> %c%d[style=%s];\n", tag, v->id,
                         tag, m->id, cedge_style);
              }

          assert (UF_IS_REP (v, 0, type));
          if (!UF_IS_SINGLETON_SET (v, 0, type))
            {
              fprintf (stdout,
                       "  %c%d -> %c%d[style=%s, color=%s, arrowhead=none];\n",
                       tag, v->id, tag, VARID2VARPTR (vars,
                                                      v->GETQDAG (type).
                                                      uf[0].members.list.
                                                      first)->id,
                       cedge_member_style, cedge_member_color);
              for (mid = v->GETQDAG (type).uf[0].members.list.first; mid;
                   mid = nid)
                {
                  m = VARID2VARPTR (vars, mid);
                  nid = m->GETQDAG (type).uf[0].members.link.next;
                  if (nid)
                    {
                      n = VARID2VARPTR (vars, nid);
                      fprintf (stdout,
                               "  %c%d -> %c%d[style=%s, color=%s, arrowhead=none];\n",
                               tag, m->id, tag, n->id, cedge_member_style,
                               cedge_member_color);
                    }
#if 1
                  PRINT_EDGES (m, dedges, dedge_style, tag, htag);
                  if (QDPLL_SCOPE_EXISTS (m->scope))
                    PRINT_EDGES (m, sedges, cedge_style, tag, tag);
#endif
                }
            }
        }
    }

  fprintf (stdout, "}\n");
}


/* Checks if 'y' depends on 'x', i.e. whether it is the case that 
   'y \in D^{std}(x)'. 
   Note that this is a constant-time check for the simple dependency
   manager.
*/
static int
qdpll_dep_man_depends (QDPLLDepManGeneric * dmg, VarID x, VarID y)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;
#if COMPUTE_STATS
  unsigned long long int old_total_costs = dm->stats.num_total_depends_costs;
  dm->stats.num_total_depends_calls++;
  /* Count first deref. */
  dm->stats.num_total_depends_costs++;
#endif
  Var *var_x = VARID2VARPTR (vars, x);
  Var *var_y = VARID2VARPTR (vars, y);
  Scope *scope_x = var_x->scope;
  Scope *scope_y = var_y->scope;

  int result;
  /* Do early check. */
  if (scope_x->nesting >= scope_y->nesting || scope_x->type == scope_y->type)
    result = 0;
  else if (dmg->type == QDPLL_DEPMAN_TYPE_SIMPLE)
    {
      assert (scope_x->nesting < scope_y->nesting
              && scope_x->type != scope_y->type);
      result = 1;
    }
  else if (QDPLL_SCOPE_FORALL (scope_x))
    {
      assert (QDPLL_SCOPE_EXISTS (scope_y));
      result = depends_forall_exists (dm, var_x, var_y);
    }
  else
    {
      assert (QDPLL_SCOPE_EXISTS (scope_x));
      assert (QDPLL_SCOPE_FORALL (scope_y));
      result = depends_exists_forall (dm, var_x, var_y);
    }
#if COMPUTE_STATS
  unsigned long long int cur =
    dm->stats.num_total_depends_costs - old_total_costs;
  assert (cur <= dm->stats.num_total_depends_costs);
  if (cur > dm->stats.num_max_depends_costs)
    dm->stats.num_max_depends_costs = cur;
#endif
  return result;
}


/* Returns x's class representative wrt. d-edges. */
static VarID
qdpll_dep_man_get_class_rep (QDPLLDepManGeneric * dmg, VarID x,
                             const unsigned int ufoffset)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  const QDPLLDepManType type = dmg->type;
  assert (dm->state.init);
  Var *vars = dm->pcnf->vars;
  Var *var_x = VARID2VARPTR (vars, x);
  assert (ufoffset <= 1);
  assert (QDPLL_SCOPE_EXISTS (var_x->scope) || ufoffset == 0);
  return uf_find (vars, var_x, ufoffset, type)->id;
}


static void
qdpll_dep_man_reduce_lits (QDPLLDepManGeneric * dmg, LitIDStack ** lit_stack,
                           LitIDStack ** lit_stack_tmp,
                           const QDPLLQuantifierType other_type,
                           const int lits_sorted)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
#if COMPUTE_TIMES
  const double start = time_stamp ();
#endif
  assert (dm->state.init);
  assert (lits_sorted);
  type_reduce (dmg, lit_stack, lit_stack_tmp, other_type, lits_sorted);
#if COMPUTE_TIMES
  dm->dmg.qdpll->time_stats.total_reduce_time += (time_stamp () - start);
#endif
}


static LitID *
qdpll_dep_man_get_candidates (QDPLLDepManGeneric * dmg)
{
  QDPLLDepManQDAG *dm = (QDPLLDepManQDAG *) dmg;
  const QDPLLDepManType type = dmg->type;
  QDPLL_ABORT_DEPMAN (!(dm->state.init),
		      "dependency manager not initialized.");

  /* Count candidates. */
  unsigned int cnt = 0;
  Var *vars = dm->pcnf->vars;
  Var *c;
  VarID cid, cidn;
  for (cid = dm->candidates.first; cid; cid = c->qdag.cand_link.next)
    {
      c = VARID2VARPTR (vars, cid);
      assert (c->GETQDAG (type).mark_is_candidate);
      cnt++;
    }

  /* Allocate zero-terminated array of candidates. Caller is
     responsible for releasing that memory. We do not use memory
     manager here because caller might not have access to it to call
     'free' afterwards. */
  LitID *result = malloc ((cnt + 1) * sizeof (LitID));
  memset (result, 0, (cnt + 1) * sizeof (LitID));
  LitID *rp = result;

  for (cid = dm->candidates.first; cid; cid = c->qdag.cand_link.next)
    {
      c = VARID2VARPTR (vars, cid);
      assert (c->GETQDAG (type).mark_is_candidate);
      assert (c->id > 0);
      assert (c->scope->type == QDPLL_QTYPE_EXISTS || 
              c->scope->type == QDPLL_QTYPE_FORALL);
      /* Existential (universal) variables are exported as positive
         (negative) ID. */
      *rp++ = c->scope->type == QDPLL_QTYPE_EXISTS ? c->id : -c->id;
      assert (rp < (result + cnt + 1));
    }
  assert (rp == result + cnt);
  assert (!(*rp));

  return result;
}

/* -------------------- END: CORE FUNCTIONS -------------------- */



/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

QDPLLDepManQDAG *
qdpll_qdag_dep_man_create (QDPLLMemMan * mm, QDPLLPCNF * pcnf,
                           QDPLLDepManType type, int print_deps_by_search,
                           QDPLL * qdpll)
{
  QDPLLDepManQDAG *dm =
    (QDPLLDepManQDAG *) qdpll_malloc (mm, sizeof (QDPLLDepManQDAG));
  dm->mm = mm;
  dm->pcnf = pcnf;

  dm->dmg.qdpll = qdpll;
  dm->dmg.type = type;

  /* Set fptrs */
  dm->dmg.init = qdpll_dep_man_init;
  dm->dmg.reset = qdpll_dep_man_reset;
  dm->dmg.get_candidate = qdpll_dep_man_get_candidate;
  dm->dmg.notify_inactive = qdpll_dep_man_notify_inactive;
  dm->dmg.notify_active = qdpll_dep_man_notify_active;
  dm->dmg.is_candidate = qdpll_dep_man_is_candidate;
  dm->dmg.notify_init_variable = qdpll_dep_man_notify_init_variable;
  dm->dmg.notify_reset_variable = qdpll_dep_man_notify_reset_variable;
  dm->dmg.is_init = qdpll_dep_man_is_init;

  if (print_deps_by_search)
    dm->dmg.print_deps = qdpll_dep_man_print_deps_by_search;
  else
    dm->dmg.print_deps = qdpll_dep_man_print_deps_by_graph;

  dm->dmg.dump_dep_graph = qdpll_dep_man_dump_dep_graph;
  dm->dmg.depends = qdpll_dep_man_depends;
  dm->dmg.get_class_rep = qdpll_dep_man_get_class_rep;
  dm->dmg.reduce_lits = qdpll_dep_man_reduce_lits;
  dm->dmg.get_candidates = qdpll_dep_man_get_candidates;

  return dm;
}


void
qdpll_qdag_dep_man_delete (QDPLLDepManQDAG * dm)
{
  qdpll_free (dm->mm, dm, sizeof (QDPLLDepManQDAG));
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
