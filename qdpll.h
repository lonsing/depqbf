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



#ifndef QDPLL_H_INCLUDED
#define QDPLL_H_INCLUDED

#include <stdio.h>

typedef struct QDPLL QDPLL;
typedef int LitID;
typedef unsigned int VarID;
typedef unsigned int ConstraintID;

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

/* Open a new scope, where variables can be added by 'qdpll_add'.
   Returns nesting of new scope.
   Opened scope can be closed by adding '0' via 'qdpll_add'.
   NOTE: will fail if there is an opened scope already.
*/
unsigned int qdpll_new_scope (QDPLL * qdpll, QDPLLQuantifierType qtype);

/* Add variables or literals to clause or opened scope.
   If scope is opened, then 'id' is interpreted as a variable ID,
   otherwise 'id' is interpreted as a literal.
   NOTE: will fail if a scope is opened and 'id' is negative.
*/
void qdpll_add (QDPLL * qdpll, LitID id);

/* Decide formula. */
QDPLLResult qdpll_sat (QDPLL * qdpll);

/* Get assignment of variable. */
QDPLLAssignment qdpll_get_value (QDPLL * qdpll, VarID id);

/* Print QBF to 'out' using QDIMACS format. */
void qdpll_print (QDPLL * qdpll, FILE * out);

/* Print QDIMACS-compliant output. */
void qdpll_print_qdimacs_output (QDPLL * qdpll);

/* Initialize the current dependency manager. 
   This can be used e.g. to print dependencies. */
void qdpll_init_deps (QDPLL * qdpll);

/* Returns non-zero if variable 'id2' depends on variable 'id1', 
   i.e. if id1 < id2, with respect to the current dependency scheme. */
int qdpll_var_depends (QDPLL * qdpll, VarID id1, VarID id2);

/* Print zero-terminated list of dependencies for 
   given variable to 'stdout'. */
void qdpll_print_deps (QDPLL * qdpll, VarID id);

/* Declare and init new variable in same scope of 'id' and return its
   id. */
VarID qdpll_new_var (QDPLL * qdpll, VarID id);

/* Return largest declared variable ID. */
VarID qdpll_get_max_declared_var_id (QDPLL * qdpll);

/* Dump dependency graph to 'stdout' in DOT format. */
void qdpll_dump_dep_graph (QDPLL * qdpll);

/* Print statistics to 'stderr'. */
void qdpll_print_stats (QDPLL * qdpll);

/* Reset internal solver state, keep clauses and variables. */
void qdpll_reset (QDPLL * qdpll);


#endif
