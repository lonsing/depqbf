/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        

 Copyright 2010, 2011, 2012, 2013, 2014, 2015, 2016 
 Florian Lonsing, Johannes Kepler University, Linz, Austria and 
 Vienna University of Technology, Vienna, Austria.

 Copyright 2012 Aina Niemetz, Johannes Kepler University, Linz, Austria.

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

#ifndef QDPLL_DEPMAN_QDAG_TYPES_H_INCLUDED
#define QDPLL_DEPMAN_QDAG_TYPES_H_INCLUDED

#include "qdpll.h"
#include "qdpll_config.h"

typedef struct QDAG QDAG;
typedef struct QDAGVarList QDAGVarList;
typedef struct QDAGVarLink QDAGVarLink;
typedef struct Edge Edge;
typedef struct EdgeTable EdgeTable;
typedef struct EdgePriorityQueue EdgePriorityQueue;
typedef struct UFObj UFObj;

struct QDAGVarList
{
  VarID first;
  VarID last;
};

struct QDAGVarLink
{
  VarID next;
  VarID prev;
};

struct EdgeTable
{
  Edge **table;
  unsigned int size;
  unsigned int count;
};

struct Edge
{
  VarID tail_var;
  VarID head_var;
  Edge *chain_next;
  unsigned int pos;
  unsigned int priority;
};

struct EdgePriorityQueue
{
  Edge **elems_start;
  Edge **elems_end;
  Edge **elems_top;
};

struct UFObj
{
  VarID par;
  unsigned int rank;
  QDAGVarLink class_link;       /* NOTE: for representatives only !!! */
  union
  {
    struct
    {
      VarID first;
      VarID last;
    } list;
    struct
    {
      VarID prev;
      VarID next;
    } link;
  } members;
};

struct QDAG
{
  QDAGVarLink cand_link;        /* candidate variables are kept in list. */
  EdgeTable dedges;
  EdgePriorityQueue dedge_pq;

  EdgeTable sedges;             /* NOTE: for exist. vars only */
  EdgePriorityQueue sedge_pq;   /* NOTE: for representatives only */

  VarID dupid;

  struct
  {                             /* NOTE: for representatives only !!! */
    VarID cpar;                 /* exactly one 'c-parent' per var */
    QDAGVarList cchilds;        /* list of vars connected by c-edge: 'c-children' */
    QDAGVarLink csibs;          /* ptrs to next/prev 'c-siebling' in list of 'c-children' */
  } cedges;                     /* c-edges */

  UFObj uf[2];

  /* NOTE: for representatives only !!! */
  union
  {
    struct
    {                           /* For existential variables only. */
      unsigned int non_propagated_in_class;
      unsigned int active_direct_refs_by_univ_class;
      unsigned int active_direct_refs_by_sedge:(sizeof (unsigned int) * 8 -
                                                1);
      unsigned int inactive_sedge_frontier:1;
    } exists;
    struct
    {                           /* For universal variables only. */
#ifndef NDEBUG
      unsigned int active_direct_refs_by_exist_var;
#endif
      unsigned int non_propagated_in_class;
    } forall;
  } cnt;

  unsigned int mark0:1;
  unsigned int mark1:1;

  unsigned int mark_is_candidate:1;
#if (COMPUTE_STATS || !defined(NDEBUG))
  unsigned int mark_is_candidate_debug:1;
  unsigned int mark_notified_inactive:1;
#endif
};

#endif
