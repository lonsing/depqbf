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
#include "qdpll_mem.h"
#include "qdpll_exit.h"
#include "qdpll_pqueue.h"

#define PQ_ASSERT_HEAP_CONDITION_INSERT 1
#define PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN 1
#define PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM 1

static unsigned int
pqueue_get_left_child_pos (unsigned int cur_pos)
{
  assert (cur_pos != PQUEUE_INVALID_POS);
  return 2 * cur_pos + 1;
}


static unsigned int
pqueue_get_right_child_pos (unsigned int cur_pos)
{
  assert (cur_pos != PQUEUE_INVALID_POS);
  return 2 * (cur_pos + 1);
}


static unsigned int
pqueue_get_parent_pos (unsigned int cur_pos)
{
  assert (cur_pos != PQUEUE_INVALID_POS);
  unsigned int result;
  result = (cur_pos - 1) / 2;
  assert (cur_pos == pqueue_get_right_child_pos (result) ||
          cur_pos == pqueue_get_left_child_pos (result));
  return result;
}


static int
pqueue_compare (PriorityQueue * pqueue, unsigned int pos_a,
                unsigned int pos_b)
{
  assert (pos_a != PQUEUE_INVALID_POS);
  assert (pos_b != PQUEUE_INVALID_POS);
  assert (pos_a < pqueue->cnt);
  assert (pos_b < pqueue->cnt);

  PriorityQueueElem elem_a = pqueue->queue[pos_a];
  PriorityQueueElem elem_b = pqueue->queue[pos_b];

  double a_priority = pqueue->queue[pos_a].priority;
  double b_priority = pqueue->queue[pos_b].priority;

  if (a_priority < b_priority)
    return -1;
  else if (a_priority == b_priority)
    {
      if (elem_a.data < elem_b.data)
        return -1;
      else
        return 1;
    }
  else
    return 1;
}


static void
pqueue_swap (PriorityQueue * pqueue, unsigned int pos_a, unsigned int pos_b)
{
  assert (pos_a != pos_b);
  assert (pos_a != PQUEUE_INVALID_POS);
  assert (pos_b != PQUEUE_INVALID_POS);
  assert (pos_a < pqueue->cnt);
  assert (pos_b < pqueue->cnt);

  PriorityQueueElem tmp, *ptr_a, *ptr_b;

  ptr_a = pqueue->queue + pos_a;
  tmp = *ptr_a;
  ptr_b = pqueue->queue + pos_b;

  assert (ptr_a->pos == pos_a);
  assert (ptr_b->pos == pos_b);

  *ptr_a = *ptr_b;
  ptr_a->pos = pos_a;

  *ptr_b = tmp;
  ptr_b->pos = pos_b;
}


static void
pqueue_up_heap (PriorityQueue * pqueue, unsigned int cur_pos)
{
  assert (cur_pos != PQUEUE_INVALID_POS);
  assert (cur_pos < pqueue->cnt);

  while (cur_pos > 0)
    {
      unsigned int parent_pos = pqueue_get_parent_pos (cur_pos);

      if (pqueue_compare (pqueue, cur_pos, parent_pos) <= 0)
        break;

      pqueue_swap (pqueue, cur_pos, parent_pos);
      cur_pos = parent_pos;
    }
}


static void
pqueue_down_heap (PriorityQueue * pqueue, unsigned int cur_pos)
{
  assert (cur_pos != PQUEUE_INVALID_POS);
  assert (cur_pos < pqueue->cnt);

  unsigned int child_pos, left_child_pos, right_child_pos;
  unsigned int count = pqueue->cnt;

  for (;;)
    {
      left_child_pos = pqueue_get_left_child_pos (cur_pos);

      if (left_child_pos >= count)
        break;

      right_child_pos = pqueue_get_right_child_pos (cur_pos);

      if (right_child_pos < count &&
          pqueue_compare (pqueue, left_child_pos, right_child_pos) < 0)
        child_pos = right_child_pos;
      else
        child_pos = left_child_pos;

      if (pqueue_compare (pqueue, cur_pos, child_pos) < 0)
        {
          pqueue_swap (pqueue, cur_pos, child_pos);
          cur_pos = child_pos;
        }
      else
        break;
    }
}


static void
assert_pqueue_condition (PriorityQueue * pqueue)
{
  unsigned int pos, no_children = pqueue->cnt / 2,
    left_child_pos, right_child_pos;

  for (pos = 0; pos < pqueue->cnt; pos++)
    {
      PriorityQueueElem *cur, *left, *right;

      cur = pqueue->queue + pos;
      assert (cur->pos == pos);

      left_child_pos = pqueue_get_left_child_pos (pos);
      right_child_pos = pqueue_get_right_child_pos (pos);

      if (pos < no_children)
        {
          assert (left_child_pos < pqueue->cnt);

          left = pqueue->queue + left_child_pos;
          assert (left->pos == left_child_pos);

          if (right_child_pos < pqueue->cnt)
            {
              right = pqueue->queue + right_child_pos;
              assert (right->pos == right_child_pos);
            }

          assert (cur->priority >= left->priority);
          assert (right_child_pos >= pqueue->cnt ||
                  cur->priority >= right->priority);
        }
      else
        {
          /* has no children */
          assert (right_child_pos >= pqueue->cnt);
          assert (left_child_pos >= pqueue->cnt);
        }
    }
}


static void
print_pqueue (PriorityQueue * pqueue)
{
  fprintf (stderr, "pqueue:");
  PriorityQueueElem *p, *e;
  for (p = pqueue->queue, e = p + pqueue->cnt; p < e; p++)
    fprintf (stderr, " %p", p->data);
  fprintf (stderr, "\n");
}


/* ----------------- START: PUBLIC FUNCTIONS ----------------- */


PriorityQueue *
pqueue_create (QDPLLMemMan * mm, unsigned int init_size)
{
  PriorityQueue *pq = qdpll_malloc (mm, sizeof (PriorityQueue));
  if (init_size == 0)
    init_size = 1;
  PriorityQueueElem *queue =
    qdpll_malloc (mm, sizeof (PriorityQueueElem) * init_size);
  pq->queue = queue;
  pq->size = init_size;
  assert (pq->cnt == 0);
  PriorityQueueElem *p, *e;
  for (p = pq->queue, e = p + pq->size; p < e; p++)
    p->pos = PQUEUE_INVALID_POS;
  return pq;
}


void
pqueue_delete (QDPLLMemMan * mm, PriorityQueue * pqueue)
{
  qdpll_free (mm, pqueue->queue, sizeof (PriorityQueueElem) * pqueue->size);
  qdpll_free (mm, pqueue, sizeof (PriorityQueue));
}


void
pqueue_adjust (QDPLLMemMan * mm, PriorityQueue * pqueue, unsigned int size)
{
  unsigned int old_size;

  if ((old_size = pqueue->size) < size)
    {
      pqueue->queue = qdpll_realloc (mm, pqueue->queue,
                                     old_size * sizeof (PriorityQueueElem),
                                     size * sizeof (PriorityQueueElem));
      pqueue->size = size;
      PriorityQueueElem *p, *e;
      for (p = pqueue->queue + old_size, e = pqueue->queue + pqueue->size;
           p < e; p++)
        p->pos = PQUEUE_INVALID_POS;
    }
}


void
pqueue_insert (QDPLLMemMan * mm, PriorityQueue * pqueue, void *data,
               double priority)
{
  assert (data);
  unsigned int pos, cnt = pqueue->cnt, size = pqueue->size;

  pos = cnt;

  if (cnt == size)
    pqueue_adjust (mm, pqueue,
                   size ? (size + (size / 2) + 1) : 1);

  assert (pqueue->cnt == cnt);
  assert (pqueue->cnt < pqueue->size);

  pqueue->queue[pos].data = data;
  pqueue->queue[pos].priority = priority;
  assert (pqueue->queue[pos].pos == PQUEUE_INVALID_POS);
  pqueue->queue[pos].pos = pos;

  pqueue->cnt++;
  pqueue_up_heap (pqueue, pos);

#ifndef NDEBUG
#if PQ_ASSERT_HEAP_CONDITION_INSERT
  assert_pqueue_condition (pqueue);
#endif
#endif
}


/* Remove first element in constant time, e.g. for clearing queue.
   NOTE: destroys heap condition! 
*/
void *
pqueue_remove_first (PriorityQueue * pqueue)
{
  PriorityQueueElem result;
  unsigned int cnt = pqueue->cnt;

  if (cnt == 0)
    return 0;

  result = pqueue->queue[0];
  assert (result.pos == 0);

  cnt--;
  pqueue->queue[0] = pqueue->queue[cnt];
  assert (pqueue->queue[0].pos == cnt);
  pqueue->queue[0].pos = 0;

  pqueue->queue[cnt].pos = PQUEUE_INVALID_POS;
  pqueue->queue[cnt].data = 0;
  pqueue->queue[cnt].priority = 0;

  pqueue->cnt = cnt;

  return result.data;
}


void *
pqueue_remove_min (PriorityQueue * pqueue)
{
  void *result_data = 0;

  if (pqueue->cnt == 0)
    return result_data;

  result_data = pqueue_remove_first (pqueue);

  if (pqueue->cnt > 0)
    pqueue_down_heap (pqueue, 0);

#ifndef NDEBUG
#if PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN
  assert_pqueue_condition (pqueue);
#endif
#endif

  return result_data;
}


void *
pqueue_access_min (PriorityQueue * pqueue)
{
  if (pqueue->cnt == 0)
    return 0;
  else
    {
      assert (pqueue->queue[0].data);
      return pqueue->queue[0].data;
    }
}

/* ----------------- END: PUBLIC FUNCTIONS ----------------- */
