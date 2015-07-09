from DepQBF import *

#=============================================================================
#  basic-manual-selectors.py
#=============================================================================

# The API file 'DepQBF.py' has some comments regarding the usage of the API.
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

# Add and open a new leftmost existential block at nesting level 1. 
#    Selector variables are put into this block. 

qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
# Add selector variables with IDs 100 and 200.
qcdcl.add(100)
qcdcl.add(200)
# Close open block.
qcdcl.add(0)

# Add and open a new leftmost universal block at nesting level 2.
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
# Add a variable with ID == 1, which is part of the actual encoding.
qcdcl.add(1)
qcdcl.add(0)

# Add and open a new existential block at nesting level 3. 
qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
# Add a variable with ID == 2, which is part of the actual encoding.
qcdcl.add(2)
qcdcl.add(0)

# Add clause: 100 1 -2 0 with selector variable 100.
qcdcl.add(100)
qcdcl.add(1)
qcdcl.add(-2)
qcdcl.add(0)

# Add clause: 200 -1 2 0 with selector variable 200.
qcdcl.add(200)
qcdcl.add(-1)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.print_dimacs()

# Enable all clauses: set selector variables to false as assumptions.
qcdcl.assume(-100)
qcdcl.assume(-200)

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_SAT)
# res == 10 means satisfiable, res == 20 means unsatisfiable.
logging.warn('result is: %d', res)

qcdcl.reset()

# Add new selector variable with ID == 300 to leftmost block.
qcdcl.add_var_to_scope(300, 1)

# Add clause: 300 1 2 0 with selector variable 300. This makes the
# formula unsatisfiable.
qcdcl.add(300)
qcdcl.add(1)
qcdcl.add(2)
qcdcl.add(0)

qcdcl.print_dimacs()

# Enable all clauses: set selector variables to false as assumptions.
qcdcl.assume(-100)
qcdcl.assume(-200)
qcdcl.assume(-300)

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_UNSAT)
logging.warn('result is: %d', res)

qcdcl.reset ()

# Discard the most recently added clause '300 1 2 0' by setting the
# selector variable 300 to true.

qcdcl.assume(-100)
qcdcl.assume(-200)
qcdcl.assume(300)

qcdcl.print_dimacs()

res = qcdcl.evaluate()
assert (res == QDPLL_RESULT_SAT)
logging.warn('result after disabling the clause "300 1 2 0" is: %d', res)

