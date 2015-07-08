from __future__ import print_function
from DepQBF import *
import logging

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

# Given the following unsatisfiable formula:
#
# p cnf 4 3
# a 1 2 0
# e 3 4 0
# -1 -3 0
# 1 2 4 0
# 1 -4 0
#
# The first clause will be put in one clause group and the last two
# clauses in another group. That last two clauses are unsatisfiable,
# thus deleting the first clause preserves unsatisfiability.


# Declare outermost universal block with variables 1 and 2.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(0)

# Declare existential block with variables 3 and 4.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
qcdcl.add(3)
qcdcl.add(4)
qcdcl.add(0)

# Create a new clause group with ID 'id1'. The ID of a clause group is
# used as its handle and can be passed to API functions.
id1 = qcdcl.new_clause_group()

# Newly created clause groups are closed.
assert (not qcdcl.get_open_clause_group())

# A clause group must be opened before clauses can be added to
# it. Only one clause group can be open at a time.
qcdcl.open_clause_group(id1)
assert (qcdcl.get_open_clause_group () == id1)

# Add the clause '-1 -3 0' to the currently open clause group 'id1'.
qcdcl.add(-1)
qcdcl.add(-3)
qcdcl.add(0)
# The currently open clause group must be closed before creating or
# opening another clause group.
qcdcl.close_clause_group(id1)
assert (not qcdcl.get_open_clause_group())

# Create another clause group 'id2'.
id2 = qcdcl.new_clause_group()
assert (not qcdcl.get_open_clause_group ())
qcdcl.open_clause_group(id2)
assert (qcdcl.get_open_clause_group() == id2)
# Add the clauses '1 2 4 0' and '1 -4 0' to the currently open clause
# group 'id2'.
qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(4)
qcdcl.add(0)
#---------------------
qcdcl.add(1)
qcdcl.add(-4)
qcdcl.add(0)
qcdcl.close_clause_group(id2)
assert (not qcdcl.get_open_clause_group())

qcdcl.print_dimacs()

# Solve the formula, which is unsatisfiable.
res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.warn('result is %d' % res)
  
# Get a list of those clause groups which contain clauses used by
# solver to determine unsatisfiability. This amounts to an
# unsatisfiable core of the formula.

#check for memory leak
#for i in xrange(100000000):
#    relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
#    assert (sum(1 for _ in relevant_clause_groups) == 1)

relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())

# We must reset the solver AFTER retrieving the relevant groups.
qcdcl.reset ()

# In our example, the clauses in the group 'id2' are relevant for
# unsatisfiability. (The clause '-1 -3 0' in 'id1' cannot be part of a
# resolution refutation found by the solver.)
assert (sum(1 for _ in relevant_clause_groups) == 1)
assert (relevant_clause_groups[0] == id2)

logging.warn('printing zero-terminated relevant clause group IDs:')
print(*relevant_clause_groups, sep='\n')

# Temporarily remove the clause group 'id2' by deactivating it.
logging.warn('deactivating group 2 with clauses 1 2 4 0 and 1 -4 0')
qcdcl.deactivate_clause_group(relevant_clause_groups[0])

# Calling 'qcdcl.gc()' removes superfluous variables and quantifiers
# from the prefix. HOWEVER, in this case, we have deactivated -- not
# deleted -- group 'id2' and hence calling 'qcdcl.gc()' has no effect.
qcdcl.gc()
qcdcl.print_dimacs()

# The formula where group 'id2' has been deactivated is satisfiable.
res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_SAT)
logging.warn('result is %d' % res)
qcdcl.reset()

# Activate group 'id2' again, which makes the formula unsatisfiable.
logging.warn('activating group 2 again')
qcdcl.activate_clause_group(relevant_clause_groups[0])

# Permanently remove the group 'id1'. This operation cannot be undone
# and is in contrast to deactivating a group.
logging.warn('deleting group 1 with clause -1 -3 0')
qcdcl.delete_clause_group(id1)
# Deleting a group invalidates its ID, which can be checked by
# 'qcdcl.exists_clause_group'.
assert (not qcdcl.exists_clause_group(id1))

# Different from the first call of 'qcdcl.gc' above, this time
# variable 3 will be removed from the quantifier prefix. We deleted
# group 'id1' which contains the only clause where variable 3
# occurs. Hence calling 'qcdcl.gc' removes variable 3 because it does
# not occur any more in the formula.
qcdcl.gc()
assert (not qcdcl.is_var_declared(3))
qcdcl.print_dimacs()

# After deleting the group 'id1', the formula consisting only of the
# clauses in group 'id2' is unsatisfiable.
res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.warn('result is %d\n' %res)
