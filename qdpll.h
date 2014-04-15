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

#ifndef QDPLL_H_INCLUDED
#define QDPLL_H_INCLUDED

#include <stdio.h>

typedef struct QDPLL QDPLL;
typedef int LitID;
typedef unsigned int VarID;
typedef unsigned int ConstraintID;
typedef unsigned int Nesting;

enum QDPLLResult
{
  QDPLL_RESULT_UNKNOWN = 0,
  QDPLL_RESULT_SAT = 10,
  QDPLL_RESULT_UNSAT = 20
};

typedef enum QDPLLResult QDPLLResult;

enum QDPLLQuantifierType
{
  QDPLL_QTYPE_EXISTS = -1,
  QDPLL_QTYPE_UNDEF = 0,
  QDPLL_QTYPE_FORALL = 1
};

typedef enum QDPLLQuantifierType QDPLLQuantifierType;

typedef int QDPLLAssignment;
#define QDPLL_ASSIGNMENT_FALSE -1
#define QDPLL_ASSIGNMENT_UNDEF 0
#define QDPLL_ASSIGNMENT_TRUE 1

/* Create and initialize solver instance. */
QDPLL *qdpll_create (void);

/* Delete and release all memory of solver instance. */
void qdpll_delete (QDPLL * qdpll);

/* Configure solver instance via configuration string. 
   Returns null pointer on success and error string otherwise.
*/
char *qdpll_configure (QDPLL * qdpll, char *configure_str);

/* Ensure var table size to be at least 'num'. */
void qdpll_adjust_vars (QDPLL * qdpll, VarID num);

/* Returns the nesting level of the current rightmost scope. */
Nesting qdpll_get_max_scope_nesting (QDPLL *qdpll);


/* Decrease the current frame index by one and disable all clauses associated
   to the old, popped off frame. Returns either the old frame index which was
   popped off or zero if there is no frame to be popped off. */
unsigned int qdpll_pop (QDPLL *qdpll);


/* Enforce the deletion of variables which have no occurrences left, and
   delete empty quantifier blocks. E.g. after 'qdpll_pop', a variable might
   not have any clauses left if all the clauses containing that variable were
   removed by the pop operation. However, the variable is still present in the
   prefix that was added by the user and 'is_var_declared' returns non-zero
   for these variables. The function 'qdpll_gc' cleans up the prefix and
   deletes variables which do not occur in the current formula and removes
   empty quantifier blocks. After 'qdpll_gc', is_var_declared' returns zero
   for variables which have been removed.
   NOTE: A 'qdpll_pop' does NOT delete variables and quantifier blocks, but only clauses. 
   IMPORTANT NOTE: do NOT call 'qdpll_gc' unless you want to remove variables
   and quantifier blocks which you have previously added to the formula. */
void qdpll_gc (QDPLL *qdpll);


/* Increase the current frame index by one. Every clause added by 'qdpll_add'
   is attached to the current frame. The clauses attached to a frame will be
   discarded if the frame is popped off by 'qdpll_pop'. Returns the current
   frame index resulting from the push operation. */
unsigned int qdpll_push (QDPLL *qdpll);


/* Open a new scope at the right end of the quantifier prefix, where variables
   can be added by 'qdpll_add'. The opened scope must be closed by adding '0'
   via 'qdpll_add'. Returns the nesting of the added scope, which should be
   used as a handle of this scope, and which can safely be passed to
   'qdpll_add_var_to_scope'.  NOTE: will fail if there is an opened scope
   already.  */
Nesting qdpll_new_scope (QDPLL * qdpll, QDPLLQuantifierType qtype);

/* Open a new scope at nesting level 'nesting >= 1' with quantifier type
   'qtype'. Variables can be added to the scope opened by the most recent call
   of this function by 'qdpll_add' (similar to 'qdpll_new_scope'). The opened
   scope must be closed by adding '0' via 'qdpll_add'. Returns the nesting of
   the added scope, which should be used as a handle of this scope, and which
   can safely be passed to 'qdpll_add_var_to_scope'.
   NOTE: the run time of this function is linear in the length of quantifier prefix. */
Nesting qdpll_new_scope_at_nesting (QDPLL * qdpll, QDPLLQuantifierType qtype, Nesting nesting);

/* Add a new variable with ID 'id' to the scope with nesting level
   'nesting'. The scope must exist, i.e. it must have been added by either
   'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'. The value of the parameter
   'nesting' of this function should be a value returned by a previous call of
   'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'. In any case, it must be
   smaller than or equal to the return value of 'qdpll_get_max_scope_nesting'. */
void qdpll_add_var_to_scope (QDPLL *qdpll, VarID id, Nesting nesting);

/* Returns non-zero if variable 'id' occurs in the formula with respect to the
   current assignment. That is, if all clauses where 'id' occurs are satisfied
   then 'id' has no active occurrences left. TODO: does not take universal
   reduction into account. */
int qdpll_has_var_active_occs (QDPLL *qdpll, VarID id);

/* Add variables or literals to clause or opened scope. Scopes are opened by
   either 'qdpll_new_scope' or 'qdpll_new_scope_at_nesting'. If scope is
   opened, then 'id' is interpreted as a variable ID, otherwise 'id' is
   interpreted as a literal. If 'id == 0' then the clause/scope is closed.
   IMPORTANT NOTE: added clauses are associated to the current frame. If
   'qdpll_push' has NOT been called before then the added clauses are
   permanently added to the formula. Otherwise, they are added to the current
   frame and can be remove from the formula by calling 'qdpll_push'.  NOTE:
   function will fail if a scope is opened and 'id' is negative.  NOTE: if a
   clause containing literals of undeclared variables is added by 'qdpll_add'
   then these literals by default will be existentially quantified and put in
   the leftmost scope. That is, the variable of these literals is interpreted
   as a free variable. See also function 'qdpll_is_var_declared' below. */
void qdpll_add (QDPLL * qdpll, LitID id);


/* Solve the formula. */
QDPLLResult qdpll_sat (QDPLL * qdpll);

/* Get assignment of variable. */
QDPLLAssignment qdpll_get_value (QDPLL * qdpll, VarID id);

/* Print QBF to 'out' using QDIMACS format. */
void qdpll_print (QDPLL * qdpll, FILE * out);

/* Print QDIMACS-compliant output. */
void qdpll_print_qdimacs_output (QDPLL * qdpll);

/* Initialize the current dependency manager. The dependency scheme is
   computed with respect to the clauses added by 'qdpll_add'. If the
   dependency scheme has been computed already then calling this function has
   no effect. The dependency manager can be reset and re-initialized by calling
   'qdpll_reset_deps' and then 'qdpll_init_deps'.*/
void qdpll_init_deps (QDPLL * qdpll);

/* Reset the current dependency manager. Dependencies can be re-initialized by
   calling 'qdpll_deps_init' or 'qdpll_sat'. */
void qdpll_reset_deps (QDPLL * qdpll);

/* Returns non-zero if variable 'id2' depends on variable 'id1', 
   i.e. if id1 < id2, with respect to the current dependency scheme. */
int qdpll_var_depends (QDPLL * qdpll, VarID id1, VarID id2);

/* Print zero-terminated list of dependencies for 
   given variable to 'stdout'. */
void qdpll_print_deps (QDPLL * qdpll, VarID id);

/* Return largest declared variable ID. */
VarID qdpll_get_max_declared_var_id (QDPLL * qdpll);

/* Returns non-zero if and only if (1) a variable with ID 'id' has been added
   to the solver by a previous call of 'qdpll_add' or
   'qdpll_add_var_to_scope'. For example, the function can be used to check if
   the variable of each literal in a clause to be added has been declared
   already. If not, then it can be declared by 'qdpll_add_var_to_scope' and
   put in the right scope.  NOTE: if a clause containing literals of
   undeclared variables is added by 'qdpll_add' then these literals by default
   will be existentially quantified and put in the leftmost scope. */
int qdpll_is_var_declared (QDPLL * qdpll, VarID id);

/* Returns the nesting level 'level' in the range '1 <= level <=
   qdpll_get_max_scope_nesting()' of the previously declared variable with ID
   'id'. Returns 0 if the variable with ID 'id' is free, i.e. not explicitly
   associated to a quantifier block. Fails if 'id' does not correspond to a
   declared variable, which should be checked with function
   'qdpll_is_var_declared()' before. */
Nesting qdpll_get_nesting_of_var (QDPLL * qdpll, VarID id);

/* Returns the quantifier type (i.e. either QDPLL_QTYPE_EXISTS or
   QDPLL_QTYPE_FORALL) of the scope at nesting level 'nesting'. 
   Returns zero if there is no scope with nesting level 'nesting'. */
QDPLLQuantifierType qdpll_get_scope_type (QDPLL *qdpll, Nesting nesting);

/* Dump dependency graph to 'stdout' in DOT format. */
void qdpll_dump_dep_graph (QDPLL * qdpll);

/* Print statistics to 'stderr'. */
void qdpll_print_stats (QDPLL * qdpll);

/* Reset internal solver state, keep clauses and variables. */
void qdpll_reset (QDPLL * qdpll);

/* Reset collected statistics. */
void qdpll_reset_stats (QDPLL * qdpll);

/* Discard all learned constraints. */
void qdpll_reset_learned_constraints (QDPLL * qdpll);

/* Assign a variable as assumption. A later call of 'qdpll_sat(...)' solves
   the formula under the assumptions specified before. If 'id' is negative
   then variable with ID '-id' will be assigned false, otherwise variable with
   ID 'id' will be assigned true.

   NOTE: added assumptions will be kept across calls of 'qdpll_sat' unless
   'qdpll_reset' is called. */
void qdpll_assume (QDPLL * qdpll, LitID id);

/* Returns a zero-terminated array of LitIDs of variables which can safely be
   assigned as assumptions by function 'qdpll_assume'. The array may contain
   both existential (positive LitIDs) and universal variables (negative
   LitIDs) which are not necessarily from the leftmost quantifier set in the
   prefix.

   NOTE: the caller is responsible to release the memory of the array returned
   by this function. */
LitID * qdpll_get_assumption_candidates (QDPLL * qdpll);

/* Returns a zero-terminated array of LitIDs representing those assumptions
   (passed to the solver using 'qdpll_assume()') which were used by the solver to
   determine (un)satisfiability by the most recent call of 'qdpll_sat'.

   NOTE: the caller is responsible to release the memory of the array returned
   by this function. */
LitID * qdpll_get_relevant_assumptions (QDPLL * qdpll);

#endif
