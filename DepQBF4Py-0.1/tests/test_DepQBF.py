import unittest
from DepQBF import *
from memory_profiler import memory_usage

avg=lambda L:float(sum(L))/len(L) if len(L) > 0 else float('nan')
usage=lambda:avg(memory_usage(-1, interval=.1, timeout=None))

class Test4MemoryLeaksInIters(unittest.TestCase):
    def test_assumption_candidates(self):
        qcdcl = QCDCL()
        qcdcl.configure('--dep-man=simple','--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        qcdcl.add_cls([1,2])
        qcdcl.add_cls([1])
        qcdcl.add_cls([2])
        initial_mem_usage = usage()
        for i in xrange(30000):
            cand=list(qcdcl.iter_assumption_candidates())
            assert (sum(1 for _ in cand) == 2)
        #assume that we do not need more than 0.1MB more after X runs
        #if it leaks then we need significantly more memory
        self.assertLess(usage()-initial_mem_usage, 0.1)

    def test_relevant_assumptions(self):
        qcdcl = QCDCL()
        qcdcl.configure('--dep-man=simple','--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        qcdcl.add_cls([5,6])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        qcdcl.add_cls([1,2])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        qcdcl.add_cls([3,4])
        qcdcl.add_cls([5,-1,-3])
        qcdcl.add_cls([6,1,2,4])
        qcdcl.add_cls([6,1,-4])
        qcdcl.assume(-5)
        qcdcl.assume(-6)
        res=qcdcl.evaluate()
        assert (res == QDPLL_RESULT_UNSAT)

        initial_mem_usage = usage()
        for i in xrange(30000):
            relevant_assumptions=list(qcdcl.iter_relevant_assumptions())
            assert(sum(1 for _ in relevant_assumptions) ==1)
        self.assertLess(usage()-initial_mem_usage, 0.1)

    def test_relevant_clause_groups(self):
        qcdcl = QCDCL()
        qcdcl.configure('--dep-man=simple','--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        qcdcl.add_cls([1,2])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        qcdcl.add_cls([3,4])
        id1 = qcdcl.new_clause_group()
        qcdcl.open_clause_group(id1)
        qcdcl.add_cls([-1,-3])
        qcdcl.close_clause_group(id1)
        id2 = qcdcl.new_clause_group()
        qcdcl.open_clause_group(id2)
        qcdcl.add_cls([1,2,4])
        qcdcl.add_cls([1,-4])
        qcdcl.close_clause_group(id2)
        res = qcdcl.evaluate()
        assert (res == QDPLL_RESULT_UNSAT)

        initial_mem_usage = usage()
        for i in xrange(30000):
            relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
            assert(sum(1 for _ in relevant_clause_groups)==1)
        self.assertLess(usage()-initial_mem_usage, 0.1)

if __name__ == '__main__':
    unittest.main()

# NOTE:
#   run the unit test with the following command
#   python -m tests.test_DepQBF
#   or
#   call the unit test from the setup
#
# REQUIREMENTS:
#   - memory_profiler
