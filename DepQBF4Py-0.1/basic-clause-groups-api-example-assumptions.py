from __future__ import print_function
from DepQBF import *

#=============================================================================
#  basic-clause-groups-api-example-assumptions.py
#=============================================================================

# The API file 'qdpll.py' has some comments regarding the usage of the API.
# The header file 'qdpll.h' has some comments regarding the usage of the API. 
#
# Please see also the file 'basic-api-example.py' for more
# comments. The example below is similar to 'basic-api-example.py' but
# it does not make use of the push/pop API functions. Instead, clauses
# are added to and deleted from the formula based on selector
# variables. The selector variables are existentially quantified in
# the leftmost quantifier block. Each added clause gets a selector
# variable, which is assigned as an assumption before the actual
# solving starts. This way, clauses are enabled and disabled by
# selector variables. We argue that the use of the push/pop API
# functions is less error-prone from the user's perspective.


# Create solver instance.
qcdcl = QCDCL()

# --dep-man=simple ...  Use the linear ordering of the quantifier prefix.
# --incremental-use ... Enable incremental solving.
qcdcl.configure('--dep-man=simple','--incremental-use')

# This example is similar to'basic-clause-groups-api-example.py'.
# However, instead of using DepQBF's clause group API, we emulate
# clause groups by augmenting the clauses of the formula with fresh
# selector variables.

# The use of selector variables is common in incremental SAT and QBF
# solving.

# ***********************************************************************
# PLEASE NOTE: the purpose of this example is to demonstrate the
# difference between incremental solving by selector variables and the
# clause group and push/pop APIs of DepQBF.
#
# For incremental solving by DepQBF, it is RECOMMENDED to ALWAYS use
# either the clause group API or the push/pop API. The clause group
# API is general enough to implement any tasks which can be
# implemented by selector variables but its use is more comfortable.
# ***********************************************************************

# Given the following unsatisfiable formula (same as in
# 'basic-clause-groups-api-example.py'):

# p cnf 4 3
# a 1 2 0
# e 3 4 0
# -1 -3 0
# 1 2 4 0
# 1 -4 0
     
# To effectively put the variables into groups, we add the variable
# '5' to the first clause and the variable '6' to the last two
# clauses. The fresh selector variables 5 and 6 are existentially
# quantified at the left end of the quantifier prefix.

# Formula with selector variables looks as follows:

# p cnf 6 3
# e 5 6 0
# a 1 2 0
# e 3 4 0
# 5 -1 -3 0
# 6 1 2 4 0
# 6 1 -4 0

# Add existential quantifier block with selector variables 5 and 6.

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
qcdcl.add(5)
qcdcl.add(6)
qcdcl.add(0)

# Add quantifier blocks and variables of the original formula.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
qcdcl.add(3)
qcdcl.add(4)
qcdcl.add(0)

# Add first clause augmented with selector variable 5.
qcdcl.add(5)
qcdcl.add(-1)
qcdcl.add(-3)
qcdcl.add(0)

# Add second and third clause augmented with selector variable 6.
qcdcl.add(6)
qcdcl.add(1)
qcdcl.add(2)  
qcdcl.add(4)
qcdcl.add(0)
#---------------------
qcdcl.add(6)
qcdcl.add(1)
qcdcl.add(-4)  
qcdcl.add(0)

#  By adding the selector variables to the clauses, we have
#  effectively separated the clauses into two separate groups.  In the
#  following, we must assign the selector variables MANUALLY as
#  assumptions through the solver API to enable/disable the desired
#  groups. This must be done before solving the formula by calling
#  'qcdcl.evaluate'.
qcdcl.qdpll_print()

# Enable both groups by setting both selector variables to false.
qcdcl.assume(-5)  
qcdcl.assume(-6)

# Formula is expected to be unsatisfiable.
res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.warn('result is %d'% res)
# Get a list of those selector variables which appear in clauses used
# by the solver to determine unsatisfiability.

relevant_assumptions=list(qcdcl.get_relevant_assumptions_as_generator())
qcdcl.reset()

#BUG?
#DOES NOT WORK IN PYTHON YIELDS
#[QDPLL] qdpll_get_relevant_assumptions at line 14742: Formula is undecided!
#Abort trap: 6
#assert (sum(1 for _ in qcdcl.get_relevant_assumptions()) == 1)
assert (sum(1 for _ in relevant_assumptions) == 1)
logging.warn('printing zero-terminated relevant assumptions:')
print(*relevant_assumptions, sep='\n')

#TODO
# Caller must free memory of array returned by
# 'qcdcl.get_relevant_assumptions'.
#lib.freeme(ptr)
#free (relevant_assumptions)

# Deactivate the group which contains the last two clauses by setting
# the selector variable to true. This way, these clauses will be
# permanently satisfied in the fortcoming solver run after calling
# 'qcdcl.sat' and hence are effectively removed from the formula. Note
# that selector variable 5 has to be set to false again to enable the
# first clause.

logging.warn('deactivating group 2 with clauses 1 2 4 0 and 1 -4 0 by assumption 6')

qcdcl.assume(-5)  
qcdcl.assume(6)

qcdcl.qdpll_print()

# The formula where the last two clauses are disabled is expected to
# be satisfiable.

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_SAT)
logging.warn('result is %d'% res)
qcdcl.reset()

# By setting the selector variables 5 to true and 6 to false,
# respectively, we deactivate the first clause and activate the last
# two, which results in an unsatisfiable formula.  

logging.warn('deactivating group 1 with clause -1 -3 0')

qcdcl.assume(5)  
qcdcl.assume(-6)

qcdcl.qdpll_print()

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.warn('result is %d'% res)
