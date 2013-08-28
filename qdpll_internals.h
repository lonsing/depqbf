/*
 This file is part of DepQBF.

 DepQBF, a solver for quantified boolean formulae (QBF).        
 Copyright 2010, 2011, 2012, 2013 Florian Lonsing and Aina Niemetz, Johannes Kepler
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


#ifndef QDPLL_INTERNALS_H_INCLUDED
#define QDPLL_INTERNALS_H_INCLUDED

#include "qdpll_dep_man_generic.h"
#include "qdpll_pcnf.h"
#include "qdpll_config.h"
#include "qdpll.h"

/* Support both ascii QRP and binary QRP format when tracing. */
#define TRACE_QRP 1
#define TRACE_BQRP 2

enum QDPLLSolverState
{
  QDPLL_SOLVER_STATE_UNDEF = 0,
  QDPLL_SOLVER_STATE_SAT = 10,
  QDPLL_SOLVER_STATE_UNSAT = 20
};

typedef enum QDPLLSolverState QDPLLSolverState;


enum QDPLLDecisionHeuristic
{
  QDPLL_DH_SDCL = 0,
  QDPLL_DH_SIMPLE = 1,
  QDPLL_DH_QTYPE = 2,
  QDPLL_DH_RANDOM = 3
};

typedef enum QDPLLDecisionHeuristic QDPLLDecisionHeuristic;

struct QDPLL
{
  QDPLLMemMan *mm;              /* Memory manager. */
  QDPLLDepManGeneric *dm;       /* Dependency manager. */
  LitIDStack add_stack;
  LitIDStack add_stack_tmp;
  QDPLLPCNF pcnf;
  unsigned int cur_constraint_id;
  unsigned int num_deps_init;

  /* Stacks used for traversing implication graph in QPUP. */
  VarPtrStack qpup_nodes;
  VarPtrStack qpup_vars;
  VarPtrStack qpup_units;
  LitIDStack qpup_kept_lits;
  LitIDStack qpup_weak_predict_lits;
  Var *qpup_uip;

  QDPLLResult result;

  /* Tracing, support both ascii and binary QRP format. */
  void (*trace_scope) (Scope *);
  void (*trace_constraint) (ConstraintID, LitID *, unsigned int,
                            ConstraintID, ConstraintID);
  void (*trace_full_cover_set) (QDPLL *, ConstraintID, LitID *, unsigned int,
                                LitID *, unsigned int);


  /* Priority queue holding variable IDs for decision making. */
  unsigned int size_var_pqueue;
  unsigned int cnt_var_pqueue;
  VarID *var_pqueue;

  double var_act_decay;

  /* Stacks storing exist./univ. lits of working reason for faster
     type-reduce. */
  VarPtrStack wreason_a;
  VarPtrStack wreason_e;

  VarID *assigned_vars;
  VarID *assigned_vars_top;
  VarID *assigned_vars_end;
  VarID *bcp_ptr;
  VarID *old_bcp_ptr;

  /* Stack holding all assigned decision variables. */
  VarIDStack dec_vars;

  /* Data for fast check of stop-resolution. */
  unsigned int cnt_hi_dl_type_lits;
  Var *hi_dl_type_var;
  unsigned int hi_type_dl;
  LitIDStack smaller_type_lits;

  /* Pointer to satisfied cube or empty clause. */
  Constraint *result_constraint;

  /* For tracing only: ID of empty clause/cube or of new initial cube. */
  ConstraintID res_cons_id;

  struct
  {
    unsigned int scope_opened:1;
    unsigned int decision_level;
    unsigned int num_decisions;
    unsigned int num_backtracks;
    unsigned int pending_inits:1;
    unsigned int top_level_re_init_dist;
    unsigned int deps_init_trail_disabled;
    unsigned int lclauses_size;
    unsigned int lcubes_size;
    unsigned int clause_resizes;
    unsigned int cube_resizes;

    unsigned int restarting:1;
    unsigned int num_restarts;
    unsigned int num_inner_restarts;
    unsigned int last_backtracks;
    unsigned int num_restart_resets;
    unsigned int irestart_dist;
    unsigned int orestart_dist;
    /* Representation of forced assignment for backtracking. */
    struct
    {
      Var *var;
      QDPLLAssignment assignment;
      QDPLLVarMode mode;
      Constraint *antecedent;
    } forced_assignment;
    int exceeded_soft_max_space;
    unsigned int disabled_clauses;
  } state;

  struct
  {
    unsigned int no_pure_literals:1;
    unsigned int no_spure_literals:1;
    unsigned int no_cdcl:1;
    unsigned int no_sdcl:1;
    unsigned int no_univ_cache:1;
    unsigned int no_exists_cache:1;
    unsigned int var_act_bias;
    unsigned int no_unit_mtf:1;
    unsigned int no_res_mtf:1;
    unsigned int no_cover_by_trail:1;
    QDPLLDecisionHeuristic dh;
    unsigned int verbosity;
    unsigned int depman_simple:1;
    unsigned int depman_qdag:1;
    unsigned int depman_qdag_print_deps_by_search:1;
    unsigned int max_dec;
    unsigned int max_space;
    int seed;
    unsigned int soft_max_space;
    double lclauses_resize_value;
    double lcubes_resize_value;
    double lclauses_init_size;
    double lcubes_init_size;
    double lclauses_delfactor;
    double lcubes_delfactor;
    double var_act_inc;
    double var_act_decay_ifactor;
    unsigned int irestart_dist_init;
    unsigned int irestart_dist_inc;
    unsigned int orestart_dist_init;
    unsigned int orestart_dist_inc;
    unsigned int no_lin_irestart_inc:1;
    unsigned int no_lin_orestart_inc:1;
    unsigned int no_lin_lcubes_inc:1;
    unsigned int no_lin_lclauses_inc:1;
    unsigned int lclauses_min_init_size;
    unsigned int lclauses_max_init_size;
    unsigned int lcubes_min_init_size;
    unsigned int lcubes_max_init_size;
    unsigned int trace;
    unsigned int traditional_qcdcl:1;
    unsigned int no_qpup_cdcl:1;
    unsigned int no_qpup_sdcl:1;
    unsigned int no_lazy_qpup:1;
    unsigned int bump_vars_once:1;
  } options;

#if COMPUTE_STATS
  struct
  {
    unsigned long long int pushed_assignments;
    unsigned long long int assignment_flips;
    unsigned long long int decisions;
    unsigned long long int propagations;
    unsigned long long int total_prop_dlevels;
    unsigned long long int sat_results;
    unsigned long long int total_sat_results_dlevels;
    unsigned long long int total_sat_results_btlevels;
    unsigned long long int total_sat_results_btdist;
    unsigned long long int unsat_results;
    unsigned long long int total_unsat_results_dlevels;
    unsigned long long int total_unsat_results_btlevels;
    unsigned long long int total_unsat_results_btdist;
    unsigned long long int pushed_unit_literals;
    unsigned long long int pushed_univ_unit_literals;
    unsigned long long int pushed_top_unit_literals;
    unsigned long long int pushed_pure_literals;
    unsigned long long int pushed_top_pure_literals;
    unsigned long long int total_lit_watcher_update_calls;
    unsigned long long int total_lit_watcher_update_sat_by_lw;
    unsigned long long int total_lit_watcher_update_sat_by_rw;
    unsigned long long int total_lit_watcher_find_calls;
    unsigned long long int total_lit_watcher_find_lit_visits;
    unsigned long long int total_clause_watcher_find_calls;
    unsigned long long int total_clause_watcher_find_clause_visits;
    unsigned long long int total_clause_watcher_find_learnt_clause_visits;
    unsigned long long int total_is_clause_sat_calls;
    unsigned long long int total_is_clause_sat_by_lw;
    unsigned long long int total_is_clause_sat_by_rw;
    unsigned long long int total_is_clause_sat_lit_visits;
    double avg_sat_res_assigned_vars;
    double avg_sat_res_propped_vars;
    double avg_sat_res_propped_vars_per_assigned;
    unsigned long long int total_notify_litw_list_adds;
    unsigned long long int total_notify_litw_list_size;
    unsigned long long int total_notify_litw_list_cnt;
    unsigned long long int total_notify_clausew_list_adds;
    unsigned long long int total_notify_clausew_list_size;
    unsigned long long int total_notify_clausew_list_cnt;
    unsigned long long int total_occ_list_adds;
    unsigned long long int total_occ_list_cnt;
    unsigned long long int total_dep_man_init_calls;
#if COMPUTE_STATS_BTLEVELS_SIZE
    /* How often do we jump to level 'i' or less, regardless of result-type. */
    unsigned long long int btlevels[COMPUTE_STATS_BTLEVELS_SIZE];
    unsigned long long int btlevels_lin[COMPUTE_STATS_BTLEVELS_SIZE];
#endif
    unsigned long long int total_sdcl_covers;
    unsigned long long int total_learnt_cubes_mtfs;
    unsigned long long int total_learnt_clauses_mtfs;
    unsigned long long int total_learnt_clauses;
    unsigned long long int total_learnt_clauses_size;
    unsigned long long int total_learnt_cubes;
    unsigned long long int total_learnt_cubes_size;
    unsigned long long int total_unit_lcubes;
    unsigned long long int total_sat_lcubes;
    unsigned long long int total_unit_lclauses;
    unsigned long long int total_empty_lclauses;
    unsigned long long int total_constraint_dels;
    unsigned long long int total_clause_dels;
    unsigned long long int total_cube_dels;
    unsigned long long int total_type_reduce_lits;
    unsigned long long int total_sat_cubes;
    unsigned long long int total_mtf_dirty_deps_constraints;
    unsigned long long int total_type_reduce_effort;
    unsigned long long int total_type_reduce_calls;
    unsigned long long int total_type_reduce_costs;
    unsigned long long int total_learnt_mtf_calls;
    unsigned long long int total_splits_ignored_unit_clauses;
    unsigned long long int total_splits_ignored_unit_cubes;
    unsigned long long int total_splits_ignored_empty_clauses;
    unsigned long long int total_splits_ignored_satisfied_cubes;
    unsigned long long int total_var_act_rescales;

    unsigned long long int total_del_unit_cube_cnt;
    unsigned long long int total_del_unit_clause_cnt;
    unsigned long long int total_del_res_cube_cnt;
    unsigned long long int total_del_res_clause_cnt;
    unsigned long long int num_sat_res_steps;
    unsigned long long int num_unsat_res_steps;

    unsigned long long int num_learn_choose_vars;
    unsigned long long int num_learn_trail_pivot;
    unsigned long long int total_lwatched;
    unsigned long long int non_dep_lwatched_skipped;
    unsigned long long int total_lwatched_tested;

    unsigned long long int total_restart_dlevels;
    unsigned long long int total_restart_at_dlevels;
    unsigned long long int total_restart_at_dist;

    unsigned long long int blits_tested;
    unsigned long long int blits_disabling;
    unsigned long long int blits_update_calls;
    unsigned long long int blits_update_done;
    unsigned long long int blits_update_visits;

    unsigned long long int blits_pure_tested;
    unsigned long long int blits_pure_disabling;

    unsigned long long int constr_min_lits_reducible;
    unsigned long long int constr_min_lits_seen;
  } stats;
#endif

#if COMPUTE_TIMES
  struct
  {
    double total_sat_time;
    double sat_time_start;
    double total_bcp_time;
    double total_sol_learn_time;
    double total_conf_learn_time;
    double total_learn_time;
    double total_reduce_time;
    double total_ireason_time;
    double total_greason_time;
  } time_stats;
#endif
};

#endif
