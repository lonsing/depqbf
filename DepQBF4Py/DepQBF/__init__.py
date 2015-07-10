"""Activates all clauses in the group 'clause_group', which has been
deactivated before by 'deactivate_clause_group'. Clause groups
are activated at the time they are created and can be
deactivated by calling 'deactivate_clause_group'.

>>> from DepQBF import *

>>> qcdcl = QCDCL(lib_path=lib_path)
>>> 
>>> qcdcl.configure('--dep-man=simple','--incremental-use')
"""

# >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
# 1
# >>> qcdcl.add_lst([1,2])
# >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
# 2
# >>> qcdcl.add_lst([3,4])

# >>> id1 = qcdcl.new_clause_group()
# >>> qcdcl.open_clause_group(id1)
# >>> qcdcl.add_lst([-1,-3])
# >>> qcdcl.close_clause_group(id1)
# >>> id2 = qcdcl.new_clause_group()
# >>> qcdcl.open_clause_group(id2)
# >>> qcdcl.add_lst([1,2,4])
# >>> qcdcl.add_lst([1,-4,0])
# >>> qcdcl.close_clause_group(id2)

# >>> qcdcl.evaluate()
# 20
# >>> relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
# >>> qcdcl.reset()
# >>> qcdcl.deactivate_clause_group(relevant_clause_groups[0])
# >>> qcdcl.evaluate()
# 10
# >>> qcdcl.reset()
# >>> qcdcl.activate_clause_group(relevant_clause_groups[0])
# >>> qcdcl.evaluate()
# 20

__all__ = ['QCDCL','QDPLL',
           'QDPLL_P','QDPLL_QTYPE_EXISTS', 'QDPLL_QTYPE_UNDEF', 'QDPLL_QTYPE_FORALL',
           'QDPLL_RESULT_UNKNOWN','QDPLL_RESULT_SAT','QDPLL_RESULT_UNSAT',
           'QDPLL_ASSIGNMENT_FALSE','QDPLL_ASSIGNMENT_UNDEF','QDPLL_ASSIGNMENT_TRUE',
           'ClauseGroupID','c_int','ClauseGroupID_P','LitID','LitID_P','assignment2str','lib_path']

from QCDCL import *
from basic_types import *
