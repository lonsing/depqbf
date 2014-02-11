/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        

 Copyright 2010, 2011, 2012, 2013, 2014 Florian Lonsing, 
 Johannes Kepler University, Linz, Austria and 
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

#ifndef QDPLL_PCNF_H_INCLUDED
#define QDPLL_PCNF_H_INCLUDED

#include <limits.h>
#include <stdint.h>
#include "qdpll.h"
#include "qdpll_stack.h"
#include "qdpll_dep_man_qdag_types.h"
#include "qdpll_config.h"

typedef struct QDPLLPCNF QDPLLPCNF;
typedef struct Scope Scope;
typedef struct Var Var;
typedef struct Constraint Constraint;

#define QDPLL_DECLARE_DLIST(name, type)					\
  struct name ## List {type * first; type * last; unsigned int cnt;};	\
  typedef struct name ## List name ## List				\

#define QDPLL_DECLARE_DLINK(name, type)			  \
  struct name ## Link {type * prev; type * next;};        \
  typedef struct name ## Link name ## Link                \

QDPLL_DECLARE_DLINK (Scope, Scope);
QDPLL_DECLARE_DLIST (Scope, Scope);
QDPLL_DECLARE_DLINK (Constraint, Constraint);
QDPLL_DECLARE_DLIST (Constraint, Constraint);

/* Wrapper for constraint occurrences: blocking literal and pointer to actual
   constraint. Used during literal-watcher updates: before pointer is deref'd,
   we check if the blocking literal 'blit' already satisfies/falsifies the
   clause/cube. We use bit-stuffing to store a flag whether 'constr' points to
   a clause or cube. */
struct BLitsOcc
{
  LitID blit;
  Constraint *constraint;
};

typedef struct BLitsOcc BLitsOcc;

#define BLIT_MARKED_PTR(ptr) (((uintptr_t)(ptr)) & ((uintptr_t)1))
#define BLIT_STRIP_PTR(ptr) ((Constraint *)(((uintptr_t)(ptr)) & (~((uintptr_t)(1)))))
#define BLIT_MARK_PTR(ptr) ((Constraint *)(((uintptr_t)(ptr)) | (((uintptr_t)(1)))))

QDPLL_DECLARE_STACK (ConstraintPtr, Constraint *);
QDPLL_DECLARE_STACK (VarPtr, Var *);
QDPLL_DECLARE_STACK (VarID, VarID);
QDPLL_DECLARE_STACK (LitID, LitID);
QDPLL_DECLARE_STACK (QDPLLQuantifierType, QDPLLQuantifierType);
QDPLL_DECLARE_STACK (LitIDPtr, LitID *);
QDPLL_DECLARE_STACK (BLitsOcc, BLitsOcc);
QDPLL_DECLARE_STACK (ScopePtr, Scope *);

typedef unsigned int QDPLLVarMode;
#define QDPLL_VARMODE_UNDEF 0
#define QDPLL_VARMODE_UNIT 1
#define QDPLL_VARMODE_PURE 2
#define QDPLL_VARMODE_LBRANCH 3
#define QDPLL_VARMODE_RBRANCH 4
#define QDPLL_VARMODE_ASSUMED 5

struct QDPLLPCNF
{
  /* Linked list of scopes internal to the solver. This list is obtained by
     cleaning up the user-given scopes stored in the list 'user_scopes' by
     removing variables without occurrences, removing empty scopes and merging
     adjacent scopes of the same type. However, the list of user-given scopes
     does not change. */
  ScopeList scopes;
  /* Linked list of user-given scopes, maintained through the API functions. */
  ScopeList user_scopes;
  /* Stack of pointers to scopes in linked list 'user_scopes'. This is an auxiliary
     data structure to be used in incremental solving when the scope list
     modified by API functions. This stack is redundant but it allows
     maintenance of scope list to be performed in constant time. */
  ScopePtrStack user_scope_ptrs;
  VarID max_declared_user_var_id;
  /* Total size of var-table. */
  VarID size_vars;
  /* Size of that part of var-table which is reserved for user-given vars. */
  VarID size_user_vars;
  VarID used_vars;
  Var *vars;
  ConstraintList clauses;
  ConstraintList learnt_clauses;
  ConstraintList learnt_cubes;
};

struct QDAGPartition
{
  QDAGVarList classes[2];
};

typedef struct QDAGPartition QDAGPartition;

struct Scope
{
  QDPLLQuantifierType type;
  unsigned int nesting;
  /* Flag to distinguish user-given scopes from internal scopes. */
  unsigned int is_internal:1;
  VarIDStack vars;
  ScopeLink link;

  /* Stack holding cover-literals. */
  LitIDStack cover_lits;

  QDAGPartition partition;
};

struct Var
{
  VarID id;
  unsigned int decision_level;
  unsigned int trail_pos;
  QDPLLAssignment assignment:2;
  QDPLLVarMode mode:3;
  /* Two multi-purpose marks. */
  unsigned int mark0:1;
  unsigned int mark1:1;
  /* Mark to indicate if variable is internal, i.e. used as selector
     variable. */
  unsigned int is_internal:1;
  unsigned int mark_propagated:1;
  unsigned int mark_is_neg_watching_cube:1;
  unsigned int mark_is_pos_watching_cube:1;
#if COMPUTE_STATS
  unsigned int mark_stats_type_reduce_lits:1;
#endif

  /* If variable is internal: the ID of the active (i.e. not popped off) frame
     where that variable is used as selector variable. If a frame is popped
     off then this value has no meaning. Otherwise, the value indicates the
     position of the variable on the stack 'cur_used_internal_vars'. */
  unsigned int frame_index;

  /* Marks used in learning. */
  unsigned int mark_learn0:1;
  unsigned int mark_learn1:1;

  /* Marks used for QPUP. TODO: could re-use other marks already present. */
  unsigned int qpup_mark_pos:1;
  unsigned int qpup_mark_neg:1;
  unsigned int qpup_res_mark_pos:1;
  unsigned int qpup_res_mark_neg:1;
  unsigned int qpup_predict_mark:1;
  Constraint *qpup_constraint;

  /* Mark used for qrp extraction. */
  unsigned int mark_qrp:1;

  LitIDStack type_red_member_lits;

  /* Antecedent of implied assignments. */
  Constraint *antecedent;

  /* The first clause on each occurrence stack 
     is watched for pure literal detection. Using blocking literals as well. */
  BLitsOccStack neg_occ_clauses;
  BLitsOccStack pos_occ_clauses;

  BLitsOccStack neg_occ_cubes;
  BLitsOccStack pos_occ_cubes;

  /* Clause watching for pure literal detection.
     The watcher (if any) is always the first clause on occurrence stack.
     Signed IDs of variables which must find new pos./neg. watcher after assignment. 
     Entries must be deleted if a variable has found a new watched clause.
   */
  LitIDStack pos_notify_clause_watchers;
  LitIDStack neg_notify_clause_watchers;

  /* For each literal 'l' in a clause watched by e.g. 'x', the
     position of x's entry in l's notify-list is maintained. Two lists
     of positions are needed, since there are two watched clauses: one
     positive and one negative. */
  VarIDStack pos_offset_in_notify_list;
  VarIDStack neg_offset_in_notify_list;

  /* For each entry 'l' in a notify-list of e.g. 'x', the position of
     'x' in the clause (containing both x and l) watched by 'l' is
     maintained. */
  VarIDStack pos_offset_in_watched_clause;
  VarIDStack neg_offset_in_watched_clause;

  /* Literal watching for unit literal detection.
     Two literals watched in each clause: EE or AE.
     Notification lists contain pointers to clauses where one of the two watchers 
     needs update after assignment of variable.
   */
  BLitsOccStack pos_notify_lit_watchers;
  BLitsOccStack neg_notify_lit_watchers;

  /* Pointer to internal scope of variable: will be set when importing
     a variable from its user-scope. */
  Scope *scope;
  /* Pointer to user scope: will be set when the user adds the
     variable to its scope through the API. 
     NOTE: this pointer is necessary because we must universal-reduce
     clauses based on the user-prefix at the time when they are
     added. Hence we must use the nesting levels of the user scopes to sort
     literals in added clauses. */
  Scope *user_scope;
  /* Position of this variable's ID on the stack of variables of its user-scope. */
  unsigned int offset_in_user_scope_vars;
  unsigned int priority_pos;
  double priority;

  QDPLLAssignment cached_assignment:2;
  QDAG qdag;
};


/* A constraint type that subsumes Clause and Cube. */
struct Constraint
{
  ConstraintID id;
  unsigned int size_lits;
  unsigned int num_lits:(sizeof (unsigned int) * 8 - 4);
  unsigned int is_cube:1;
  unsigned int learnt:1;
  unsigned int is_reason:1;
  /* Counting the number of times a constraint is watched by a
     variable. */
  unsigned int is_watched:(sizeof (unsigned int) * 8 - 2);
  unsigned int is_taut:1;

  unsigned int dep_init_level:(sizeof (unsigned int) * 8 - 1);
  /* NOTE: only for '--no-spure-literals'; marks constraints to be cleaned up. */
  unsigned int deleted:1;

  /* All original clauses are kept in linked list, also learnt clauses
     separately and learnt cubes. */
  ConstraintLink link;

  /* For O(1)-notify list maintenance during literal watcher update,
     we store the position of a constraint in the notify lists of the watched
     literals. This is different from SAT, where only one watcher has to
     be update each time and clauses can be easily dropped from the
     notify-list of the propagated literal. But in QBF we sometimes have
     to update both watchers, which amounts to deleting the clause from
     the non-propagated literal. Searching could be too costly
     then. Since a clause has two watchers, it occurs in two
     notify-lists. In the array, pos_in_notify_list[0] and [1] are the
     positions for the left and right watcher, respectively. */
  unsigned int offset_in_notify_list[2];
  unsigned int rwatcher_pos;    /* Position of right watched literal. */
  unsigned int lwatcher_pos;    /* Position of left watched literal. */
  LitID lits[];                 /* Flexible lit-array. */
};


#define QDPLL_LIT_NEG(lit) ((lit) < 0)
#define QDPLL_LIT_POS(lit) (!QDPLL_LIT_NEG((lit)))

#define LIT2VARID(lit) ((lit) < 0 ? -(lit) : (lit))
#define LIT2VARPTR(vars, lit) ((vars) + LIT2VARID(lit))
#define LIT2VAR(vars, lit) ((vars)[LIT2VARID(lit)])

#define VARID2VARPTR(vars, id) ((vars) + (id))
#define VARID2VAR(vars, lit) ((vars)[(id)])

#define QDPLL_DEFAULT_SCOPE_NESTING 0
#define QDPLL_SCOPE_EXISTS(s) ((s)->type == QDPLL_QTYPE_EXISTS)
#define QDPLL_SCOPE_FORALL(s) ((s)->type == QDPLL_QTYPE_FORALL)
#define QDPLL_VAR_EXISTS(v) (QDPLL_SCOPE_EXISTS((v)->scope))
#define QDPLL_VAR_FORALL(v) (QDPLL_SCOPE_FORALL((v)->scope))

#define QDPLL_VAR_POS_MARK(v) ((v)->mark0 = 1)
#define QDPLL_VAR_NEG_MARK(v) ((v)->mark1 = 1)
#define QDPLL_VAR_UNMARK(v) ((v)->mark0 = (v)->mark1 = 0)
#define QDPLL_VAR_POS_UNMARK(v) ((v)->mark0 = 0)
#define QDPLL_VAR_NEG_UNMARK(v) ((v)->mark1 = 0)
#define QDPLL_VAR_POS_MARKED(v) ((v)->mark0)
#define QDPLL_VAR_NEG_MARKED(v) ((v)->mark1)
#define QDPLL_VAR_MARKED(v) ((v)->mark0 || (v)->mark1)

#define QDPLL_VAR_ASSIGNED(v) ((v)->assignment)
#define QDPLL_VAR_ASSIGNED_TRUE(v) ((v)->assignment == QDPLL_ASSIGNMENT_TRUE)
#define QDPLL_VAR_ASSIGNED_FALSE(v) ((v)->assignment == QDPLL_ASSIGNMENT_FALSE)
#define QDPLL_VAR_ASSIGN_TRUE(v) ((v)->assignment = QDPLL_ASSIGNMENT_TRUE)
#define QDPLL_VAR_ASSIGN_FALSE(v) ((v)->assignment = QDPLL_ASSIGNMENT_FALSE)

#define QDPLL_INVALID_TRAIL_POS UINT_MAX
#define QDPLL_INVALID_PQUEUE_POS UINT_MAX
#define QDPLL_INVALID_WATCHER_POS UINT_MAX
#define QDPLL_WATCHER_SAT (UINT_MAX - 1)

#define QDPLL_VAR_HAS_NEG_OCC_CLAUSES(v) (!QDPLL_EMPTY_STACK((v)->neg_occ_clauses))
#define QDPLL_VAR_HAS_POS_OCC_CLAUSES(v) (!QDPLL_EMPTY_STACK((v)->pos_occ_clauses))
#define QDPLL_VAR_HAS_OCC_CLAUSES(v) (QDPLL_VAR_HAS_NEG_OCC_CLAUSES(v) || \
				      QDPLL_VAR_HAS_POS_OCC_CLAUSES(v))
#define QDPLL_VAR_HAS_NEG_OCC_CUBES(v) (!QDPLL_EMPTY_STACK((v)->neg_occ_cubes))
#define QDPLL_VAR_HAS_POS_OCC_CUBES(v) (!QDPLL_EMPTY_STACK((v)->pos_occ_cubes))
#define QDPLL_VAR_HAS_OCC_CUBES(v) (QDPLL_VAR_HAS_NEG_OCC_CUBES(v) ||	\
				    QDPLL_VAR_HAS_POS_OCC_CUBES(v))
#define QDPLL_VAR_HAS_NEG_OCCS(v) (QDPLL_VAR_HAS_NEG_OCC_CLAUSES(v) ||	\
				   QDPLL_VAR_HAS_NEG_OCC_CUBES(v))
#define QDPLL_VAR_HAS_POS_OCCS(v) (QDPLL_VAR_HAS_POS_OCC_CLAUSES(v) ||	\
				   QDPLL_VAR_HAS_POS_OCC_CUBES(v))
#define QDPLL_VAR_HAS_OCCS(v) (QDPLL_VAR_HAS_OCC_CLAUSES(v) ||	\
                               QDPLL_VAR_HAS_OCC_CUBES(v))
#define QDPLL_VAR_MARK_EXPORTED(v) ((v)->mark_exported = 1)
#define QDPLL_VAR_UNMARK_EXPORTED(v) ((v)->mark_exported = 0)
#define QDPLL_VAR_MARKED_EXPORTED(v) ((v)->mark_exported)
#define QDPLL_VAR_MARK_PROPAGATED(v) ((v)->mark_propagated = 1)
#define QDPLL_VAR_UNMARK_PROPAGATED(v) ((v)->mark_propagated = 0)
#define QDPLL_VAR_MARKED_PROPAGATED(v) ((v)->mark_propagated)


#define LEARN_VAR_NEG_MARK(v) ((v)->mark_learn0 = 1)
#define LEARN_VAR_NEG_UNMARK(v) ((v)->mark_learn0 = 0)
#define LEARN_VAR_NEG_MARKED(v) ((v)->mark_learn0)
#define LEARN_VAR_POS_MARK(v) ((v)->mark_learn1 = 1)
#define LEARN_VAR_POS_UNMARK(v) ((v)->mark_learn1 = 0)
#define LEARN_VAR_POS_MARKED(v) ((v)->mark_learn1)
#define LEARN_VAR_MARKED(v) ((v)->mark_learn0 || (v)->mark_learn1)
#define LEARN_VAR_UNMARK(v) ((v)->mark_learn0 = (v)->mark_learn1 = 0)


/* Sorting Macros. */
/* Sorting: taken from Picosat. */
#define INTERNAL_SORTING_SWAP(T,p,q)		      \
  do {                                                \
    T tmp = *(q);				      \
    *(q) = *(p);				       \
    *(p) = tmp;                                        \
  } while (0)

#define INTERNAL_SORTING_CMPSWAP(Q, T,cmp,p,q)                \
  do {                                                        \
    if ((cmp) (Q, *(p), *(q)) > 0)                            \
      INTERNAL_SORTING_SWAP (T, p, q);                        \
  } while(0)

#define INTERNAL_INSERTION_SORT(Q,T,cmp,a,n)                            \
  do {									\
    T pivot;								\
    int l = 0, r = (n) - 1, i, j;					\
    for (i = r; i > l; i--)						\
      INTERNAL_SORTING_CMPSWAP (Q, T, cmp, (a) + i - 1, (a) + i);       \
    for (i = l + 2; i <= r; i++)                                        \
      {									\
        j = i;								\
        pivot = (a)[i];							\
        while ((cmp) (Q, pivot, (a)[j - 1]) < 0)                        \
          {								\
	    (a)[j] = (a)[j - 1];					\
	    j--;							\
          }								\
        (a)[j] = pivot;							\
      }									\
  } while (0)

#ifdef NDEBUG
#define CHECK_SORTED(Q,cmp,a,n) do { } while(0)
#else
#define CHECK_SORTED(Q,cmp,a,n)                                 \
  do {								\
    int i;							\
    for (i = 0; i < (n) - 1; i++)				\
      assert ((cmp) (Q, (a)[i], (a)[i + 1]) <= 0);              \
  } while(0)
#endif

#define QDPLL_SORT(Q,T,cmp,a,n)                                 \
  do {								\
    T * aa = (a);						\
    int nn = (n);						\
    INTERNAL_INSERTION_SORT (Q, T, cmp, aa, nn);                \
    CHECK_SORTED (Q, cmp, aa, nn);                              \
  } while (0)

#endif
