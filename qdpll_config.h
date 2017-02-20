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

#ifndef QDPLL_CONFIG_H_INCLUDED
#define QDPLL_CONFIG_H_INCLUDED

#include <limits.h>

/* This switch enables all expensive assertions (anyway overridden by
 'NDEBUG'). */
#define FULL_ASSERT 0

/* ---------------------------------------*/
/* ---------- START: 'qdpll.c' ---------- */

/* Start: assertion switches: */

#if FULL_ASSERT

#define QDPLL_PQ_ASSERT_HEAP_CONDITION_INSERT 1
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN 1
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM 1
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_INCREASE_KEY 1
#define QDPLL_ASSERT_CANDIDATES_ON_PQUEUE 1
#define QDPLL_ASSERT_BCP_WATCHERS_INTEGRITY 1
#define QDPLL_ASSERT_FULL_FORMULA_INTEGRITY 1
#define QDPLL_ASSERT_SOLVE_STATE 1
#define QDPLL_ASSERT_FORMULA_NOT_TRUE_AFTER_SAT_WATCHER_CHECK 1
#define QDPLL_ASSERT_FIND_IN_ASSIGNED_VARS 1
#define QDPLL_ASSERT_LEARN_VARS_UNMARKED 1
#define QDPLL_ASSERT_CDCL_FORCED_ANTECEDENT 1
#define QDPLL_ASSERT_PUSHED_PURE_LITS 1

#else

#define QDPLL_PQ_ASSERT_HEAP_CONDITION_INSERT 0
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN 0
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM 0
#define QDPLL_PQ_ASSERT_HEAP_CONDITION_INCREASE_KEY 0
#define QDPLL_ASSERT_CANDIDATES_ON_PQUEUE 0
#define QDPLL_ASSERT_BCP_WATCHERS_INTEGRITY 0
#define QDPLL_ASSERT_FULL_FORMULA_INTEGRITY 0
#define QDPLL_ASSERT_SOLVE_STATE 0
#define QDPLL_ASSERT_FORMULA_NOT_TRUE_AFTER_SAT_WATCHER_CHECK 0
#define QDPLL_ASSERT_FIND_IN_ASSIGNED_VARS 0
#define QDPLL_ASSERT_LEARN_VARS_UNMARKED 0
#define QDPLL_ASSERT_CDCL_FORCED_ANTECEDENT 0
#define QDPLL_ASSERT_PUSHED_PURE_LITS 0

#endif
/* End: assertion switches. */

#define DEFAULT_VARS_SIZE (1 << 0)
#define DEFAULT_USER_VARS_SIZE (1 << 0)
#define DEFAULT_INTERNAL_VARS_INCREASE (100)
#define QDPLL_INVALID_DECISION_LEVEL UINT_MAX

#define COMPUTE_STATS 0
#define COMPUTE_TIMES 0

/* Try to eliminate universal variables from initial cubes while
   preserving effects of QBCE. */
#define QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS 1

/* Allow to learn 'elim_univ_dynamic_switch_delay' initial cubes before
   checking whether to turn of elimination of universals from initial
   cubes. */
#define ELIM_UNIV_DYNAMIC_SWITCH_DELAY_INIT_VAL 1000

/* Allow to collect as many cover sets as 'COLLECT_FULL_COVER_SETS_MULT_LIMIT'
   times the current maximal number of learned cubes. */
#define COLLECT_FULL_COVER_SETS_MULT_LIMIT (1)

/* Type of default dependency manager. 'QDPLL_DEPMAN_TYPE_SIMPLE' is the
   original quantifier prefix and 'QDPLL_DEPMAN_TYPE_QDAG' causes the solver to
   use the standard dependency scheme. */
#define DEFAULT_DEPMANTYPE QDPLL_DEPMAN_TYPE_QDAG

#define IRESTART_DIST_INIT_VAL 100
#define IRESTART_DIST_INC_INIT_VAL 10
#define ORESTART_DIST_INIT_VAL 10
#define ORESTART_DIST_INC_INIT_VAL 5

#define LCLAUSES_INIT_VAL (0)
#define LCUBES_INIT_VAL (0)
#define LCLAUSES_RESIZE_VAL (500)
#define LCUBES_RESIZE_VAL (500)

#define LCLAUSES_MIN_INIT_VAL 2500
#define LCLAUSES_MAX_INIT_VAL 10000
#define LCUBES_MIN_INIT_VAL 2500
#define LCUBES_MAX_INIT_VAL 10000

/* ---------- END: 'qdpll.c' ---------- */
/* ------------------------------------ */




/* --------------------------------------------------- */
/* ---------- START: 'qdpll_dep_man_qdag.c' ---------- */

/* Start: assertion switches. */

#if FULL_ASSERT

#define QDAG_PQ_ASSERT_HEAP_CONDITION_INSERT 1
#define QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN 1
#define QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM 1
#define QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_BEFORE 1
#define QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_AFTER 1
#define QDAG_ASSERT_INSERT_C_EDGE_CCHILDS 1
#define QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_BEFORE 1
#define QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_AFTER 1
#define QDAG_ASSERT_MERGED_UNIV_VARS 1
#define QDAG_ASSERT_REMOVE_TRANSITIVITIES_VARS_UNMARKED 1
#define QDAG_ASSERT_GRAPH_INTEGRITY 1
#define QDAG_ASSERT_XCHECK_DEPENDENCIES 1
#define QDAG_ASSERT_CANDIDATE_LIST 1
#define QDAG_ASSERT_INACTIVE_SEDGE_FRONTIER 1
#define QDAG_ASSERT_CANDIDATE_MARKS_BY_REMARKING 1
#define QDAG_ASSERT_FILL_CANDIDATES_VARS 1
#define QDAG_ASSERT_GET_EXIST_CANDIDATES_MEMBERS 1
#define QDAG_ASSERT_CHECK_DEPENDENCIES_BY_FUNCTIONS 1

#else

#define QDAG_PQ_ASSERT_HEAP_CONDITION_INSERT 0
#define QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_MIN 0
#define QDAG_PQ_ASSERT_HEAP_CONDITION_REMOVE_ELEM 0
#define QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_BEFORE 0
#define QDAG_ASSERT_INSERT_C_EDGE_INTEGRITY_AFTER 0
#define QDAG_ASSERT_INSERT_C_EDGE_CCHILDS 0
#define QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_BEFORE 0
#define QDAG_ASSERT_EXTRACT_DEPS_INSERT_C_EDGE_AFTER 0
#define QDAG_ASSERT_MERGED_UNIV_VARS 0
#define QDAG_ASSERT_REMOVE_TRANSITIVITIES_VARS_UNMARKED 0
#define QDAG_ASSERT_GRAPH_INTEGRITY 0
#define QDAG_ASSERT_XCHECK_DEPENDENCIES 0
#define QDAG_ASSERT_CANDIDATE_LIST 0
#define QDAG_ASSERT_INACTIVE_SEDGE_FRONTIER 0
#define QDAG_ASSERT_CANDIDATE_MARKS_BY_REMARKING 0
#define QDAG_ASSERT_FILL_CANDIDATES_VARS 0
#define QDAG_ASSERT_GET_EXIST_CANDIDATES_MEMBERS 0
#define QDAG_ASSERT_CHECK_DEPENDENCIES_BY_FUNCTIONS 0

#endif
/* End: assertion switches. */

#define DEFAULT_EDGE_TABLE_SIZE 1
#define DEFAULT_EDGE_PQUEUE_SIZE 1

/* Skip certain assertions, which is is needed during delayed
   notification of (in)active variables. In this case, counter values
   might be updated late. */
#ifdef NDEBUG
#define SKIP_DELAYED_NOTIF_ASSERT 0
#else
#define SKIP_DELAYED_NOTIF_ASSERT 1
#endif

/* ---------- END: 'qdpll_dep_man_qdag.c' ---------- */
/* ------------------------------------------------- */

#endif
