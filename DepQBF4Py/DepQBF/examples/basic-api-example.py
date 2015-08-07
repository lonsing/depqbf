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

# Add and open a new leftmost universal block at nesting level 1.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
# Add a fresh variable with 'id == 1' to the open block.
qcdcl.add(1)
# Close open scope.
qcdcl.add(0)

# Add a new existential block at nesting level 2. 
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
# Add a fresh variable with 'id == 2' to the existential block.
qcdcl.add(2)
# Close open scope. 
qcdcl.add(0)

# Add clause: 1 -2 0
qcdcl.add(1)
qcdcl.add(-2)
qcdcl.add(0)

# Add clause: -1 2 0
qcdcl.add(-1)
qcdcl.add(2)
qcdcl.add(0)

# At this point, the formula looks as follows:
#   p cnf 2 3 
#   a 1 0
#   e 2 0
#   1 -2 0
#  -1 2 0 

# Print formula.
qcdcl.print_dimacs()

res = qcdcl.evaluate()

# Expecting that the formula is satisfiable.
assert (res == QDPLL_RESULT_SAT)

# res == 10 means satisfiable, res == 20 means unsatisfiable.
logging.info("result is: %d", res)

# Must reset the solver before adding further clauses or variables.
qcdcl.reset()

# Open a new frame of clauses. Clauses added after the 'push' can be
# removed later by calling 'pop'.
qcdcl.push()

# Add clause: 1 2 0 
qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(0)

logging.info('added clause "1 2 0" to a new stack frame.')
logging.info('res=%s', res)

# At this point, the formula looks as follows:
#      p cnf 2 3 
#      a 1 0
#      e 2 0
#      1 -2 0
#      -1 2 0 
#      1 2 0 */
qcdcl.print_dimacs()

res = qcdcl.evaluate()
# Expecting that the formula is unsatisfiable due to the most recently added clause. 
assert (res == QDPLL_RESULT_UNSAT)

# res == 10 means satisfiable, res == 20 means unsatisfiable.
logging.info("result is: %d", res)

# Print partial countermodel as a value of the leftmost universal variable.
a = qcdcl.get_value(1)

logging.info("partial countermodel - value of 1: %s\n", assignment2str(a))

qcdcl.reset()

# Discard the clause '1 2 0' by popping off the topmost frame.
qcdcl.pop()
logging.info("discarding clause '1 2 0' by a 'pop'.\n")


# At this point, the formula looks as follows:
#     p cnf 2 3 
#     a 1 0
#     e 2 0
#     1 -2 0
#     -1 2 0
qcdcl.print_dimacs()

res = qcdcl.evaluate()

# The formula is satisfiable again because we discarded the clause '1 2 0'
#     by a 'pop'.

assert (res == QDPLL_RESULT_SAT)
logging.info("result after pop is: %d\n", res)
