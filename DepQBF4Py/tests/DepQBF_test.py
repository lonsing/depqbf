from setuptools.dist import Distribution
import DepQBF
from DepQBF import *
import distutils.command.build
from distutils.util import get_platform
import doctest
from glob import glob
import logging
from memory_profiler import memory_usage
from os import path
from sys import version_info
import unittest

base_path = path.realpath('%s/../' % path.dirname(path.realpath(__file__)))

#if we run from setup.py obtain paths from distutils
def get_lib_build_path():
    b = distutils.command.build.build(Distribution())
    b.initialize_options()
    b.finalize_options()
    return '%s/%s/DepQBF' % (base_path,b.build_purelib)

lib_path = get_lib_build_path()

#we cannot use the setuptools functions as they need to be initialized
#with a setup which does not work for a standalone run
def guess_lib_build_path():
    libs = glob('%s/build/lib*' %base_path)
    if len(libs)>1:
        libs = filter(lambda x: get_platform() in x and '%s.%s'
               %(version_info.major,version_info.minor) , libs)
    try:
        libs = '%s/DepQBF' % libs[0]
        return path.realpath(libs)
    except IndexError:
        print('File "%s" does not exist. Run "setup.py build" first' % '%s/%s' % (lib_path, 'libqdpll.so*'))
        exit(1)

avg = lambda L: float(sum(L)) / len(L) if len(L) > 0 else float('nan')
usage = lambda: avg(memory_usage(-1, interval=.1, timeout=None))

class TestDocTest(unittest.TestCase):
    def test_doctest(self):
        suite = unittest.TestSuite()
        suite.addTest(doctest.DocTestSuite("DepQBF.QCDCL", extraglobs={'lib_path': lib_path}))
        unittest.TextTestRunner(verbosity=1).run(suite)


class Test4MemoryLeaksInIters(unittest.TestCase):
    def test_assumption_candidates(self):
        qcdcl = QCDCL(lib_path)
        qcdcl.configure('--dep-man=simple', '--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        qcdcl.add_lst([1, 2])
        qcdcl.add_lst([1])
        qcdcl.add_lst([2])
        initial_mem_usage = usage()
        for i in xrange(30000):
            cand = list(qcdcl.iter_assumption_candidates())
            assert (sum(1 for _ in cand) == 2)
        # assume that we do not need more than 0.1MB more after X runs
        # if it leaks then we need significantly more memory
        # assume 0.2 otherwise we need psutil to be installed
        self.assertLess(usage() - initial_mem_usage, 0.2)
        del qcdcl

    def test_relevant_assumptions(self):
        qcdcl = QCDCL(lib_path)
        qcdcl.configure('--dep-man=simple', '--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        qcdcl.add_lst([5, 6])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        qcdcl.add_lst([1, 2])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        qcdcl.add_lst([3, 4])
        qcdcl.add_lst([5, -1, -3])
        qcdcl.add_lst([6, 1, 2, 4])
        qcdcl.add_lst([6, 1, -4])
        qcdcl.assume(-5)
        qcdcl.assume(-6)
        res = qcdcl.evaluate()
        assert (res == QDPLL_RESULT_UNSAT)

        initial_mem_usage = usage()
        for i in xrange(30000):
            relevant_assumptions = list(qcdcl.iter_relevant_assumptions())
            assert (sum(1 for _ in relevant_assumptions) == 1)
        self.assertLess(usage() - initial_mem_usage, 0.1)
        del qcdcl

    def test_relevant_clause_groups(self):
        qcdcl = QCDCL(lib_path)
        qcdcl.configure('--dep-man=simple', '--incremental-use')
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        qcdcl.add_lst([1, 2])
        qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        qcdcl.add_lst([3, 4])
        id1 = qcdcl.new_clause_group()
        qcdcl.open_clause_group(id1)
        qcdcl.add_lst([-1, -3])
        qcdcl.close_clause_group(id1)
        id2 = qcdcl.new_clause_group()
        qcdcl.open_clause_group(id2)
        qcdcl.add_lst([1, 2, 4])
        qcdcl.add_lst([1, -4])
        qcdcl.close_clause_group(id2)
        res = qcdcl.evaluate()
        assert (res == QDPLL_RESULT_UNSAT)

        initial_mem_usage = usage()
        for i in xrange(30000):
            relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
            assert (sum(1 for _ in relevant_clause_groups) == 1)
        self.assertLess(usage() - initial_mem_usage, 0.1)
        del qcdcl


logging.debug('lib_path is "%s"', lib_path)
lib_path = guess_lib_build_path()

if __name__ == '__main__':
    unittest.main()
    
