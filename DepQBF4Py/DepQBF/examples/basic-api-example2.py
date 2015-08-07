#!/usr/bin/env python
#
# This file is part of DepQBF (DepQBF Python API).
#
# DepQBF, a solver for quantified boolean formulae (QBF).  
#
# DepQBF4Py Copyright 2015
#
# Johannes K. Fichte, Vienna University of Technology, Austria
#
# Copyright 2010, 2011, 2012, 2013, 2014, 2015 
#
# Florian Lonsing, Johannes Kepler University, Linz, Austria and
# Vienna University of Technology, Vienna, Austria.  
#
# Copyright 2012 Aina Niemetz, Johannes Kepler University, Linz,
# Austria.  
#
# DepQBF is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.  DepQBF is distributed in the
# hope that it will be useful, but WITHOUT ANY WARRANTY; without even
# the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
# PURPOSE.  See the GNU General Public License for more details.  You
# should have received a copy of the GNU General Public License along
# with DepQBF.  If not, see <http://www.gnu.org/licenses/>.
import logging
logging.basicConfig(format='%(message)s', level=logging.INFO)

from DepQBF import *

# =============================================================================
#  basic-api-example.py
# =============================================================================

# The API file 'DepQBF.py' has some comments regarding the usage of the API.
# The header file 'qdpll.h' has some comments regarding the usage of the API. 
# Please see also the file 'basic-manual-selectors.py'.

# Create solver instance.
qcdcl = QCDCL()

# --dep-man=simple ...  Use the linear ordering of the quantifier prefix.
# --incremental-use ... Enable incremental solving.
qcdcl.configure('--dep-man=simple', '--incremental-use')

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
qcdcl.add(1)
qcdcl.add(0)

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
qcdcl.add(3)
qcdcl.add(0)

qcdcl.add(3)
qcdcl.add(0)

qcdcl.push()

qcdcl.add(-1)
qcdcl.add(-2)
qcdcl.add(0)

qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.print_dimacs()

# Internally, variable 2 has universal-reduced from the added
#   clauses. See the output of the above 'print_dimacs'. However, the
#   variable is still present in the prefix of the formula. We can
#   check this by calling 'is_var_declared', passing the respective
#   variable ID.
assert (qcdcl.is_var_declared(1))
assert (qcdcl.is_var_declared(2))
assert (qcdcl.is_var_declared(3))

# For example, we did not declare a variable with ID 99.
assert (not qcdcl.is_var_declared(99))

# Some assertions which demonstrate how to inspect the current prefix.
assert (qcdcl.get_scope_type(1) == QDPLL_QTYPE_EXISTS)
assert (qcdcl.get_scope_type(2) == QDPLL_QTYPE_FORALL)
assert (qcdcl.get_scope_type(3) == QDPLL_QTYPE_EXISTS)

assert (qcdcl.get_max_declared_var_id() == 3)
assert (qcdcl.get_max_scope_nesting() == 3)
assert (qcdcl.get_nesting_of_var(1) == 1)
assert (qcdcl.get_nesting_of_var(2) == 2)
assert (qcdcl.get_nesting_of_var(3) == 3)

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.info("result is: %d\n", res)

qcdcl.reset()
qcdcl.pop()

# The previous 'pop' removed the clauses '-1 -2 0' and '-1 -2 0' and
# the variables 1 and 2 do not occur in clauses any more. However,
# these variables are still present in the prefix, and the prefix
# remains unchanged.
assert (qcdcl.is_var_declared(1))
assert (qcdcl.is_var_declared(2))
assert (qcdcl.is_var_declared(3))
assert (qcdcl.get_scope_type(1) == QDPLL_QTYPE_EXISTS)
assert (qcdcl.get_scope_type(2) == QDPLL_QTYPE_FORALL)
assert (qcdcl.get_scope_type(3) == QDPLL_QTYPE_EXISTS)
assert (qcdcl.get_max_declared_var_id() == 3)
assert (qcdcl.get_max_scope_nesting() == 3)

# IMPORTANT NOTE: we demonstrate the use of 'gc' and functions to
# manipulate the quantifier prefix. The function 'gc' cleans up the
# prefix and removes variables which do not occur in any clauses in
# the current formula. It also removes empty quantifier blocks. DO NOT
# call 'gc' unless you really want to clean up the quantifier prefix!

# If we call 'gc' here then the variables 1 and 2 will be removed from
# the prefix (and also their quantifier blocks because they become
# empty). Before we add the clauses "1 -2 0" and "-1 2 0" below, we
# must restore the original prefix.  Otherwise, when adding these
# clauses the solver will interpret the variables 1 and 2 (which do
# not occur in the prefix at the time when the clauses are added) as
# free variables. Free variables by default are put into an
# existential quantifier block at the left end of the quantifier
# prefix.

qcdcl.gc()

#  Variables 1 and 2 have been deleted by 'gc', including their
# quantifier blocks because these blocks became empty.
assert (not qcdcl.is_var_declared(1))
assert (not qcdcl.is_var_declared(2))

# Variable 3 still occurs in a clause and hence 'gc' does not clean it
# up.
assert (qcdcl.is_var_declared(3))

# The current prefix consists of the existential block containing
# variable 3 only. This block is now at nesting level 1 because the
# other blocks have been deleted by 'gc'.
assert (qcdcl.get_max_scope_nesting() == 1)
assert (qcdcl.get_nesting_of_var(3) == 1)
assert (qcdcl.get_max_declared_var_id() == 3)

# We have to restore the original prefix and insert variables 1 and 2
# and their respective quantifier blocks. Add new existential block
# at nesting level 1 and new variable with ID 1 to this block.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
qcdcl.add(1)
qcdcl.add(0)
assert (qcdcl.is_var_declared(1))

assert (qcdcl.get_nesting_of_var(1) == 1)
# The block of variable 3 now appears at nesting level 2 because we
# added a new existential block at nesting level 1.
assert (qcdcl.get_nesting_of_var(3) == 2)

# Add new universal block at nesting level 2 and new variable with ID 2 to
# this block.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
qcdcl.add(2)
qcdcl.add(0)
assert (qcdcl.is_var_declared(2))
assert (qcdcl.get_nesting_of_var(1) == 1)
assert (qcdcl.get_nesting_of_var(2) == 2)

# The block of variable 3 now appears at nesting level 3 because we added a
# new existential and universal block at nesting levels 1 and 2.
assert (qcdcl.get_nesting_of_var(3) == 3)
assert (qcdcl.get_scope_type(1) == QDPLL_QTYPE_EXISTS)
assert (qcdcl.get_scope_type(2) == QDPLL_QTYPE_FORALL)
assert (qcdcl.get_scope_type(3) == QDPLL_QTYPE_EXISTS)

# Now the original prefix is restored and we can proceed with adding
# further clauses containing variables 1 and 2.

qcdcl.add(1)
qcdcl.add(-2)
qcdcl.add(0)

qcdcl.add(-1)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.print_dimacs()

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.info("result is: %d\n", res)
