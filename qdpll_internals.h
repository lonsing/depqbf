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

#ifndef QDPLL_INTERNALS_H_INCLUDED
#define QDPLL_INTERNALS_H_INCLUDED

#include "qdpll_dep_man_generic.h"
#include "qdpll_pqueue.h"
#include "qdpll_pcnf.h"
#include "qdpll_config.h"
#include "qdpll.h"
#include "./picosat/picosat.h"
#include "./nenofex/nenofex.h"

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
  QDPLL_DH_RANDOM = 3,
  QDPLL_DH_FALSIFY = 4,
  QDPLL_DH_SATISFY = 5
};

typedef enum QDPLLDecisionHeuristic QDPLLDecisionHeuristic;

struct QDPLL
{
  QDPLLMemMan *mm;              /* Memory manager. */
  QDPLLDepManGeneric *dm;       /* Dependency manager. */
  LitIDStack add_stack;
  /* For parsing only: maximal variable ID on stack 'add_stack'. */
  VarID max_var_id_on_add_stack;
  LitIDStack add_stack_tmp;
  QDPLLPCNF pcnf;
  unsigned int cur_constraint_id;

  /* Stack to collect IDs of variables from outermost quantifier block which
     were assigned during QDIMACS output reconstruction. These variables were
     previously unassigned but were then assigned for QBCE assignment
     reconstruction. */
  VarIDStack qdo_dummy_assigned_vars;

  /* Pointer to Nenofex solver used as QBF oracle. 
     NOTE: we used Bloqqer before, but this imposes limitations on
     using more than one instance of DepQBF, as Bloqqer is not
     reentrant. */
  Nenofex *nenofex_oracle;
  /* Options (strings) to configure Nenofex. These options must be set again
     after Nenofex object has been destroyed. We need to pass options to Nenofex
     to allow for bounded solving. */
  CharPtrStack nenofex_option_strings;

  PicoSAT *trivial_falsity_solver;
  PicoSAT *trivial_truth_solver;

  ConstraintList cover_sets;

  /* Data structures for empty formula watching. */
  /* Pointer to an unsatisfied, non-blocked clause which is a witness the
     formula is not empty. */
  BLitsOcc *empty_formula_watcher;
  /* Stack of pointers o empty formula watchers per each decision level. This
     allows to continue the search for an empty formula watcher where we stopped
     earlier after backtracking. */
  BLitsOccPtrStack empty_formula_watchers_per_dec_level;
  /* For better cache performance: stack of BLitsOccs to check if a clause is
     satisfied by a cached literal, to avoid fetching the clause from memory. */
  BLitsOccStack empty_formula_watching_blit_occs;

  QBCENonBlockedWitnessStack qbcp_qbce_maybe_blocked_clauses;
  /* Stack of clauses identified as being blocked. This is necessary to
     reconstruct a cover set of the CNF for initial cube learning. There is
     one stack of blocked clauses per decision level which is cleared during
     backtracking. */
  ConstraintPtrStackStack qbcp_qbce_blocked_clauses;
  /* Stack of clauses which have been marked at each decision level by setting
     'clause->qbcp_qbce_mark'. */
  ConstraintPtrStackStack qbcp_qbce_marked_clauses;

  /* For incremental solving under assumptions with QBCE: stack stores
     clauses which have been marked to be rescheduled for QBCE in next
     solver run. */
  ConstraintPtrStack reschedule_qbce_marked_clauses;

  /* Variables which appear in newly added input clauses AND which have
     occurrences that are used as QBCE witnesses. This information is needed
     for incremental QBCE to reschedule currently blocked clauses for QBCE
     checking based on newly added clauses. */
  VarIDStack qbcp_qbce_relevant_vars_in_new_input_clauses;

  LitIDStack internal_cover_lits;

  /* Assumptions given by the user through 'qdpll_assume' are collected on a
     stack and assigned before the actual solving starts. */
  LitIDStack user_given_assumptions;

  /* Stacks used for traversing implication graph in QPUP. */
  PriorityQueue *qpup_nodes;
  VarPtrStack qpup_vars;
  VarPtrStack qpup_units;
  LitIDStack qpup_kept_lits;
  LitIDStack qpup_weak_predict_lits;
  Var *qpup_uip;

  Var * qpup_var_at_max_dec_level;
  unsigned int qpup_cnt_at_max_dec_level;
  unsigned int qpup_recompute_var_at_max_dec_level:1;



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

  /* For solving under assumptions: if the formula is e.g. unsatisfiable under
     the given assumptions, then in the end the solver might produce a clause
     containing only literals of variables assigned as assumptions. This case is
     a generalization of solving without assumptions where in the end we derive
     the empty clause. The final clause containing only assumption literals
     represents the subset of the given assumptions which were in fact used to
     show unsatisfiability. The user can access that clause through the interface
     to retrieve the set of relevant assumption. */
  Constraint *assumption_lits_constraint;

  /* Data to fix QDIMACS output: some of the variables might be unassigned. */
  char *qdo_assignment_table;
  unsigned int qdo_table_bytes;

  struct
  {
    unsigned int scope_opened:1;
    unsigned int push_pop_api_called:1;
    unsigned int clause_group_api_called:1;
    Scope *scope_opened_ptr;
    unsigned int decision_level;
    /* The counter 'cnt_active_clause_groups' replaces the previous
       'cur_frame_index' to generalize the push/pop API to clause groups. For
       the use of the push/pop API, 'cnt_active_clause_groups' is in fact the
       current frame index: i.e. the number of times function 'qdpll_push' was
       called without a corresponding 'qdpll_pop'. The frame index is zero
       initially, it increases by one if push is called and decreases by one
       if pop is called. Each frame index has a single internal variable
       associated to. This variable "selects" the clauses attached to the
       frame. Selector variables are always assigned. */
    unsigned int cnt_created_clause_groups;
    /* For incremental solving with clause groups: ID of currently open clause
       group. This is relevant to add selector literals to clauses added by the
       user. */
    unsigned int cur_open_group_id;
    /* ID of a fresh internal variable to be associated to a frame. */
    unsigned int next_free_internal_var_id;
    /* Stack of internal variable IDs which were associated to a frame before
       but that frame was popped off by 'qdpll_pop'. If necessary, then these
       variables can be recycled. These variables must be set to */
    VarIDStack popped_off_internal_vars;
    /* Stack of internal variable IDs which are currently associated to a
       frame. Note: there is no relation between the current frame index and the
       internal variable associated to that frame. */
    VarIDStack cur_used_internal_vars;

    unsigned int num_decisions;
    unsigned int num_backtracks;
    unsigned int lclauses_size;
    unsigned int lcubes_size;
    unsigned int clause_resizes;
    unsigned int cube_resizes;

    /* For incremental solving: must check learned cubes only if clauses have
       been added after a 'push'. */
    unsigned int pending_cubes_check:1;
    unsigned int clauses_added_since_cube_check;
    /* For incremental solving: store full cover sets only if NO VARIANT
       (i.e. fully dynamic, pre-, or inprocessing) of dynamic QBCE is used.
       Purpose of flag: when generating initial cubes, make sure that first we
       collect an assignment which satisfies all the clauses WITHOUT reducing
       innermost existential literals on the fly. In incremental solving, this
       is needed to check if collected cover sets are propositional models of
       the CNF that may have been updated by the user. */
    unsigned int collect_full_cover_sets:1;
    unsigned int num_sat_calls;

    double var_act_inc;

    unsigned int assumptions_given:1;
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
    double solving_start_time;
    unsigned int popped_off_orig_clause_cnt;
    /* Flag to toggle import of user given prefix. */
    unsigned int no_scheduled_import_user_scopes:1;
    /* Flag to indicate necessary update of clause watched for empty formula
       detection. */
    unsigned int empty_formula_watcher_scheduled_update:1; 
#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
    unsigned int elim_univ_dynamic_disabled;
    unsigned int elim_univ_tried;
    unsigned int elim_univ_eliminated;
    unsigned int univ_vars_cur_collected;
#endif

    /* Flag indicates whether we are currently preprocessing by QBCE,
       i.e. 'find-blocked-clauses' is called at decision level 0 but WITHOUT
       having assigned any variables before. */
    unsigned int qbcp_qbce_currently_preprocessing:1;
    /* For QDIMACS partial output: schedule model reconstruction. */
    unsigned int qdo_no_schedule_model_reconstruction:1;
    /* Flag to indicate positive trivial truth test or that Nenofex
       returned SAT: the current branch in the search tree is
       satisfiable -> learn the current QBF solver assignment as a
       cube (or use that cube as starting point of a cube derivation). */
    unsigned int sat_branch_detected:1;
    /* Flag to skip trivial truth test based on failed assumptions of most
       recent negative trivial truth test. */
    unsigned int no_scheduled_trivial_truth:1;

    /* If the current assignment corresponds to an unsatisfiable
       branch in the search tree: Clause obtained by collecting
       negated failed assumption literals from the SAT solver (if
       trivial falsity is used) or by collecting negation of all
       literals currently assigned (if nenofex is used). */
    Constraint *unsat_branch_clause;

    /* Number of times the state of the formula after QBCP is undetermined. */
    unsigned int cnt_state_undetermined_after_qbcp;

    /* Disable calls of Nenofex if average calling time exceeds certain
       value. Using time is nondeterministic but there is currently no other,
       clean way to get information about how expensive a call of Nenofex
       was. Alternatively, we could collect statistics but this requires to let
       Nenofex print statistics to a log file which we then must parse again. */
    unsigned int dyn_nenofex_disabled:1;
    double dyn_nenofex_time;
    unsigned int dyn_nenofex_calls;

    /* Flag to dynamically disable calls of trivial falsity. */
    unsigned int trivial_falsity_disabled:1;
    /* Number of calls of trivial falsity. */
    unsigned int trivial_falsity_tried;

    /* Time spent in trivial falsity tests. */
    double trivial_falsity_time;
    /* Flag to dynamically disable calls of trivial truth. */
    unsigned int trivial_truth_disabled:1;
    /* Special case to handle QDIMACS output (values of outer existentials) if
       formula is solved by a trivial truth call but no variables are assigned
       in the QBF solver. If flag is true, then we can extract values of outer
       existentials from SAT solver. */
    unsigned int qdo_trivial_truth_success:1;
    /* Number of calls of trivial truth. */
    unsigned int trivial_truth_tried;
    /* Time spent in trivial truth tests. */
    double trivial_truth_time;
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
    /* Limits to be set by API function 'qdpll_setlimit'. */
    unsigned int limit_set:1;
    /* Max. decisions. */
    unsigned int max_dec;
    /* Max. seconds wallclock time. */
    unsigned int max_secs;
    /* Max. backtracks. */
    unsigned int max_btracks;
    /* Max. space (soft limit). */
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
    unsigned int long_dist_res:1;
    unsigned int incremental_use:1;
    unsigned int qbcp_qbce_watcher_list_mtf:1;
    /* For QBCE: do not check if literal 'l' is a blocking literal in
       clause, if '\neg l' has more than
       'qdpll->options.qbcp_qbce_find_witness_max_occs'
       occurrences. The value has to be non-zero to have any
       effect. */ 
    unsigned int qbcp_qbce_find_witness_max_occs;
    /* For QBCE: do not check clauses longer than limit whether they
       are blocked. Further, do not check literals 'l' whether they are
       blocking if '\neg l' has an occurrence which is longer than the
       limit. */
    unsigned int qbcp_qbce_max_clause_size;
#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
    /* Indicate whether to turn off elimination of universals from initial
       cubes dynamically. Default value 0. */
    unsigned int elim_univ_dynamic_switch:1;
    /* Allow to learn 'elim_univ_dynamic_switch_delay' initial cubes before
       checking whether to turn of elimination of universals from initial
       cubes. See also 'qdpll_config.h' for its initial value.*/
    unsigned int elim_univ_dynamic_switch_delay;
    /* Turn off elimination of universals from initial cubes if the success
       rate is less than or equal to 'elim_univ_dynamic_success_threshold'
       percent.  Default value 0. */
    unsigned int elim_univ_dynamic_success_threshold;
#endif
    /* Apply QBCE as preprocessing, i.e. do not take into account the
       top-level assignment. */
    unsigned int qbce_preprocessing:1;
    /* Apply QBCE as inprocessing. Take into account top-level assignment to
       simplify the formula. Inprocessing also allows for the usual way to
       construct learned cubes by collecting one satisfying literal from each
       original non-blocked clause. We may ignore blocked clauses in cube
       generation because they are blocked on the top-level. */
    unsigned int qbce_inprocessing:1;
    /* Apply QBCE for deduction. This generalizes inprocessing in that QBCE is
       applied at every decision level after QBCP (and may trigger additional
       rounds of QBCP). The usual cube learning cannot be applied because
       clauses may be blocked at arbitrary decision levels and we might not
       find a satisfying literal for a blocked clause (solution reconstruction
       does not work either). Hence we stop assigning variables as soon as the
       formula is true under the current assignment and under QBCE, and
       collect the current assignment as learned cube. Universals may be
       removed provided that QBCE can be "replayed", i.e. must keep universal
       is it was responsible for a clause becoming blocked. */
    unsigned int no_qbce_dynamic:1;
    /* Empty formula watching watches an unsatisfied and non-blocked clause as
       a witness that the CNF is not empty. If no such clause can be watched
       then the CNF is empty and the current assignment can be learned as an
       initial cube. We made mixed experiences with this option. When using
       dynamic QBCE then empty formula watching seems to improve the
       performance in contrast to plain QCDCL solving. Without empty formula
       watching the solver keeps assigning variables until all are assigned
       and no conflict was found, which shows the the CNF is currently true. */
    unsigned int no_empty_formula_watching:1;
    /* Flag to enable trivial falsity. */
    unsigned int no_trivial_falsity:1;
    /* Try to remove innermost existential by PicoSAT calls, and
       innermost universals by forall reductions. Abort if an existential
       cannot be removed. */
    unsigned int trivial_falsity_partial_mus_assumptions:1;
    /* Test trivial falsity dynamically every
       '2^{trivial_falsity_pow2_call_interval}' times the formula state under
       the current assignment after QBCP is undetermined. */
    unsigned int trivial_falsity_pow2_call_interval;
    /* Limit on number of decisions per SAT solver call in trivial falsity. */
    unsigned int trivial_falsity_decision_limit;
    /* Disable trivial falsity calls if average calling time exceeds
       'trivial_falsity_disable_time_threshold'. */
    float trivial_falsity_disable_time_threshold;
    /* Disable trivial falsity calls if number of calls is equal to or greater than
       'trivial_falsity_disable_calls_threshold' AND the average calling time
       exceeds 'trivial_falsity_disable_time_threshold'. */
    unsigned int trivial_falsity_disable_calls_threshold;

    /* Do not call trivial falsity test at all (i.e. disable it permanently)
       if the number of clauses in the CNF is equal to or greater than
       'trivial_falsity_disable_cnf_threshold'. */
    unsigned int trivial_falsity_disable_cnf_threshold;

    /* Flag to enable trivial truth. */
    unsigned int no_trivial_truth:1;
    /* Test trivial truth dynamically every
       '2^{trivial_truth_pow2_call_interval}' times the formula state under
       the current assignment after QBCP is undetermined. */
    unsigned int trivial_truth_pow2_call_interval;
    /* Disable trivial truth calls if average calling time exceeds
       'trivial_truth_disable_time_threshold'. */
    float trivial_truth_disable_time_threshold;
    /* Disable trivial truth calls if number of calls is equal to or greater than
       'trivial_truth_disable_calls_threshold' AND the average calling time
       exceeds 'trivial_truth_disable_time_threshold'. */
    unsigned int trivial_truth_disable_calls_threshold;

    /* Limit on number of decisions per SAT solver call in trivial
       truth. */
    unsigned int trivial_truth_decision_limit;
    /* Do not call trivial truth test at all (i.e. disable it permanently)
       if the number of clauses in the CNF is equal to or greater than
       'trivial_truth_disable_cnf_threshold'. */
    unsigned int trivial_truth_disable_cnf_threshold;

    /* Flag to enable dynamic Nenofex tests to check if current branch in
       search tree is (un)satisfiable. */
    unsigned int no_dynamic_nenofex:1;
    /* Ignore if Nenofex finds out that current branch is
       satisfiable. */
    unsigned int dyn_nenofex_ignore_sat:1;
    /* Ignore if Nenofex finds out that current branch is
       unsatisfiable. */
    unsigned int dyn_nenofex_ignore_unsat:1;
    /* Disable Nenofex calls if average calling time exceeds
       'dyn_nenofex_disable_time_threshold'. */
    float dyn_nenofex_disable_time_threshold;
    /* Disable Nenofex calls if number of calls is equal to or greater than
       'dyn_nenofex_disable_calls_threshold' AND the average calling time
       exceeds 'dyn_nenofex_disable_time_threshold'. */
    unsigned int dyn_nenofex_disable_calls_threshold;
    /* Call Nenofex dynamically every '2^{dyn_nenofex_call_interval}' times the
       formula state under the current assignment after QBCP is undetermined. */
    unsigned int dyn_nenofex_pow2_call_interval;
    /* Do not call Nenofex at all (i.e. disable it permanently) if the
       number of clauses in the CNF is equal to or greater than
       'dyn_nenofex_disable_cnf_threshold'. */
    unsigned int dyn_nenofex_disable_cnf_threshold;
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
    unsigned long long int total_learnt_cubes_mtfs;
    unsigned long long int total_learnt_clauses_mtfs;
    unsigned long long int total_learnt_clauses;
    unsigned long long int total_learnt_taut_clauses;
    unsigned long long int total_learnt_clauses_size;
    unsigned long long int total_learnt_cubes;
    unsigned long long int total_learnt_taut_cubes;
    unsigned long long int total_learnt_cubes_size;
    unsigned long long int total_unit_lcubes;
    unsigned long long int total_unit_taut_lcubes;
    unsigned long long int total_sat_lcubes;
    unsigned long long int total_sat_taut_lcubes;
    unsigned long long int total_unit_lclauses;
    unsigned long long int total_unit_taut_lclauses;
    unsigned long long int total_empty_lclauses;
    unsigned long long int total_empty_taut_lclauses;
    unsigned long long int total_constraint_dels;
    unsigned long long int total_clause_dels;
    unsigned long long int total_cube_dels;
    unsigned long long int total_type_reduce_lits;
    unsigned long long int total_sat_cubes;
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

    unsigned long long int qbcp_qbce_rounds;
    unsigned long long int qbcp_qbce_clauses_blocked;
    unsigned long long int qbcp_qbce_clauses_seen;
    unsigned long long int qbcp_qbce_literals_seen;
    unsigned long long int qbcp_qbce_find_entry_calls;
    unsigned long long int qbcp_qbce_find_entries_seen;

    unsigned long long int qbcp_qbce_watched_occ_find_entry_calls;
    unsigned long long int qbcp_qbce_watched_occ_find_entries_seen;
    unsigned long long int qbcp_qbce_watched_occ_add_or_remove_calls;
    unsigned long long int qbcp_qbce_watched_occ_add_or_remove_lits_seen;

    unsigned long long int qbcp_qbce_is_clause_sat_cache_accesses;
    unsigned long long int qbcp_qbce_is_clause_sat_cache_hits;
    unsigned long long int qbcp_qbce_is_clause_sat_found_sat;
    unsigned long long int qbcp_qbce_is_clause_sat_found_blocked;

    unsigned long long int qbcp_qbce_witness_is_clause_sat_cache_accesses;
    unsigned long long int qbcp_qbce_witness_is_clause_sat_cache_hits;
    unsigned long long int qbcp_qbce_witness_is_clause_sat_found_sat;
    unsigned long long int qbcp_qbce_witness_is_clause_sat_found_blocked;

    unsigned long long int qbcp_qbce_backtracks_to_toplevel;
    unsigned long long int qbcp_qbce_inprocessing_rounds;

    unsigned long long int qbcp_qbce_ignored_clauses_by_size_limit;
    unsigned long long int qbcp_qbce_ignored_maybe_blocking_literals_by_size_limit;
    unsigned long long int qbcp_qbce_ignored_maybe_blocking_literals_by_occ_limit;
    unsigned long long int qbcp_qbce_total_maybe_blocking_literals_seen;

    /* Number of clauses currently blocked. This is updated during backtracking. */
    unsigned int qbcp_qbce_current_blocked_clauses;
    /* Total number of clauses currently blocked summed up each time we
       produce an initial cube. */
    unsigned long long int qbcp_qbce_total_current_blocked_clauses;

    unsigned long long int initial_cubes;
    unsigned long long int initial_cubes_sizes;
    unsigned long long int initial_cubes_univ_lits;

    unsigned long long int empty_formula_watcher_total_update_calls;
    unsigned long long int empty_formula_watcher_effective_update_calls;
    unsigned long long int empty_formula_watcher_is_clause_sat_cache_accesses;
    unsigned long long int empty_formula_watcher_is_clause_sat_cache_hits;
    unsigned long long int empty_formula_watcher_is_clause_sat_found_sat;
    unsigned long long int empty_formula_watcher_is_clause_sat_found_blocked;

#if QBCP_QBCE_DYNAMIC_ASSIGNMENT_ELIM_UNIV_VARS
    unsigned long long int elim_univ_vars_calls;
    unsigned long long int elim_univ_vars_total_univ_vars;
    unsigned long long int elim_univ_vars_eliminated;
    unsigned long long int elim_univ_vars_clauses_seen;
#endif

    unsigned long long int trivial_falsity_detected;
    unsigned long long int trivial_falsity_max_decisions_per_call;
    unsigned long long int trivial_falsity_assumptions_passed;
    unsigned long long int trivial_falsity_assumptions_failed;
    unsigned long long int trivial_falsity_assumptions_failed_before_mus;
    unsigned long long int trivial_falsity_assumptions_failed_after_mus;
    double trivial_falsity_mus_assumptions_time;
    unsigned long long int trivial_falsity_lits_in_falsity_clause;
    /* Count how often we learn trivial falsity clause having size 0, 1, 2,
       3. Learning an empty clause will occur at most once, but may be more
       often in library use. */
    unsigned int trivial_falsity_empty_clauses_learned;
    unsigned int trivial_falsity_unit_clauses_learned;
    unsigned int trivial_falsity_binary_clauses_learned;
    unsigned int trivial_falsity_ternary_clauses_learned;

    unsigned long long int trivial_falsity_remove_inner_existentials_calls;
    unsigned long long int trivial_falsity_remove_inner_existentials_sat_calls;
    unsigned long long int trivial_falsity_remove_inner_existentials_removed;
    unsigned long long int trivial_falsity_remove_inner_existentials_reduced_univs;
    unsigned long long int trivial_falsity_remove_inner_existentials_rounds;
    unsigned long long int trivial_falsity_remove_inner_existentials_max_rounds;
    unsigned long long int trivial_falsity_deleted_clauses;
    unsigned long long int trivial_falsity_unit_clauses;
    unsigned long long int trivial_falsity_conflicting_clauses;

    unsigned long long int trivial_truth_detected;
    unsigned long long int trivial_truth_max_decisions_per_call;
    unsigned long long int trivial_truth_deleted_cubes;
    unsigned long long int trivial_truth_unit_cubes;
    unsigned long long int trivial_truth_satisfied_cubes;

    unsigned int dyn_nenofex_result_sat;
    unsigned int dyn_nenofex_result_unsat;
    unsigned int dyn_nenofex_cur_result_unknown_streak;
    unsigned int dyn_nenofex_max_result_unknown_streak;
    unsigned long long int dyn_nenofex_success_dlevels;
    unsigned long long int dyn_nenofex_unit_cubes;
    unsigned long long int dyn_nenofex_unit_clauses;
    unsigned long long int dyn_nenofex_deleted_cubes;
    unsigned long long int dyn_nenofex_deleted_clauses;
    unsigned long long int dyn_nenofex_satisfied_cubes;
    unsigned long long int dyn_nenofex_conflicting_clauses;
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
