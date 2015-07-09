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

from ctypes import *
import sys
from glob import glob
import logging
from logging.config import fileConfig
#fileConfig('logging.conf')

from os import path
from DepQBF.file_helper import *
from DepQBF.stdout_helper import *
from DepQBF.basic_types import *

class QCDCL(object):
    __lib=None
    __LIB_NAME='libqdpll.so*'

    def __load_libs(self):
        if not self.__lib:
            if self.__lib_path:
                if path.isabs(self.__lib_path):
                    module_path = self.__lib_path
                else:
                    module_path = path.realpath('%s/%s' %(path.dirname(__file__),self.__lib_path))
            else:
                module_path = path.dirname(__file__)

            self.__lib_path = '%s/%s' %(module_path, self.__LIB_NAME)
            logging.info('Loading library from path=%s', self.__lib_path)
        
            libs = glob(self.__lib_path)
            assert(sum(1 for _ in libs) == 1)
            self.__LIB_NAME = libs[0]
            logging.debug('Shared Lib: Loading...')
            logging.debug('Shared Lib: %s', self.__LIB_NAME)
            self.__lib = cdll.LoadLibrary(self.__LIB_NAME)

    def __init__(self,lib_path=None):
        logging.debug('QCDCL: Initializing...')
        self.__lib_path=lib_path
        self.__load_libs()
        qdpll_create=self.__lib.qdpll_create
        qdpll_create.restype = QDPLL_P
        self.__depqbf = qdpll_create()
        logging.debug('QCDCL: Initialized')

    def __del__(self):
        logging.debug('QCDCL: Deleting...')
        self.__lib.qdpll_delete(self.__depqbf)
        logging.debug('QCDCL: Deleted')
        cdll.LoadLibrary(None).dlclose(self.__lib._handle)

    def activate_clause_group(self,clause_group_id):
        """Activates all clauses in the group 'clause_group', which has been
        deactivated before by 'deactivate_clause_group'. Clause groups
        are activated at the time they are created and can be
        deactivated by calling 'deactivate_clause_group'.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,-3])
        >>> qcdcl.close_clause_group(id1)
        >>> id2 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id2)
        >>> qcdcl.add_lst([1,2,4])
        >>> qcdcl.add_lst([1,-4,0])
        >>> qcdcl.close_clause_group(id2)

        >>> qcdcl.evaluate()
        20
        >>> relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
        >>> qcdcl.reset()
        >>> qcdcl.deactivate_clause_group(relevant_clause_groups[0])
        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset()
        >>> qcdcl.activate_clause_group(relevant_clause_groups[0])
        >>> qcdcl.evaluate()
        20

        """
        self.__lib.qdpll_activate_clause_group(self.__depqbf,clause_group_id)
        
    def add(self,var_id):
        """Add variables or literals to clause or opened scope. Scopes are
        opened by either 'new_scope' or
        'new_scope_at_nesting'. If scope is opened, then 'id' is
        interpreted as a variable ID, otherwise 'id' is interpreted as
        a literal. If 'id == 0' then the clause/scope is closed.

        IMPORTANT NOTE: added clauses are associated to the current
        frame. If 'push' has NOT been called before then the
        added clauses are permanently added to the formula. Otherwise,
        they are added to the current frame and can be remove from the
        formula by calling 'push'.

        Similarly, added clauses are associated to the clause group
        which has been opened before by calling
        'open_clause_group', if any. If
        'open_clause_group' has NOT been called before then the
        added clauses are permanently added to the formula.

        NOTE: function will fail if a scope is opened and 'id' is
        negative.

        NOTE: if a clause containing literals of undeclared variables
        is added by 'add' then these literals by default will be
        existentially quantified and put in the leftmost scope. That
        is, the variable of these literals is interpreted as a free
        variable. See also function 'is_var_declared' below.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(0)

        >>> qcdcl.new_scope_at_nesting (QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.add(1)
        >>> qcdcl.add(-2)
        >>> qcdcl.add(0)

        >>> qcdcl.add(-1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)
        
        >>> qcdcl.print_dimacs()
        p cnf 2 2
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        """
        logging.debug('QCDCL: add_variable=%i', var_id)
        self.__lib.qdpll_add(self.__depqbf, var_id)


    def add_lst(self,L):
        """Add clause or opened scope. Scopes are opened by either
        'new_scope' or 'new_scope_at_nesting'. If scope is
        opened, then 'id' is interpreted as a variable ID, otherwise
        'id' is interpreted as a literal.

        IMPORTANT NOTE: added clauses are associated to the current
        frame. If 'push' has NOT been called before then the
        added clauses are permanently added to the formula. Otherwise,
        they are added to the current frame and can be remove from the
        formula by calling 'push'.

        Similarly, added clauses are associated to the clause group
        which has been opened before by calling
        'open_clause_group', if any. If
        'open_clause_group' has NOT been called before then the
        added clauses are permanently added to the formula.

        NOTE: function will fail if a scope is opened and 'id' is
        negative.

        NOTE: if a clause containing literals of undeclared variables
        is added by 'add' then these literals by default will be
        existentially quantified and put in the leftmost scope. That
        is, the variable of these literals is interpreted as a free
        variable. See also function 'is_var_declared' below.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.new_scope_at_nesting (QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([2])
        >>> qcdcl.add_lst([1,-2])
        >>> qcdcl.add_lst([-1,2])
        
        >>> qcdcl.print_dimacs()
        p cnf 2 2
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0

        """
        for e in L:
            self.add(e)
        self.add(0)
        
    def add_var_to_scope (self,var_id,nesting):
        """Add a new variable with ID 'id' to the scope with nesting level
        'nesting'. The scope must exist, i.e. it must have been added
        by either 'new_scope' or
        'new_scope_at_nesting'. The value of the parameter
        'nesting' of this function should be a value returned by a
        previous call of 'new_scope' or
        'new_scope_at_nesting'. In any case, it must be smaller
        than or equal to the return value of
        'get_max_scope_nesting'.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([100,200])
        >>> qcdcl.print_dimacs()
        p cnf 200 0
        e 100 200 0
        >>> qcdcl.add_var_to_scope(300, 1)
        >>> qcdcl.print_dimacs()
        p cnf 300 0
        e 100 200 300 0
        """
        self.__lib.qdpll_add_var_to_scope(self.__depqbf,var_id,nesting)

    def adjust_vars (self, var_id):
        """Ensure var table size to be at least 'num'."""
        self.__lib.qdpll_adjust_vars(self.__depqbf,var_id)

    def assume(self,lit_id):
        """Assign a variable as assumption. A later call of 'evaluate(...)'
        solves the formula under the assumptions specified before. If
        'id' is negative then variable with ID '-id' will be assigned
        false, otherwise variable with ID 'id' will be assigned
        true.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.add_lst([1])
        >>> qcdcl.print_dimacs()
        p cnf 1 1
        e 1 0
        1 0

        >>> qcdcl.assume(-1)
        >>> qcdcl.evaluate()
        20
        >>> qcdcl.reset()

        >>> qcdcl.assume(1)
        >>> qcdcl.evaluate()
        10
        """
        self.__lib.qdpll_assume(self.__depqbf,lit_id)

    def close_scope(self):
        """Close open scope."""
        self.add(0)
    
    def close_clause_group(self,clause_group_id):
        """Close the clause group with ID 'clause_group'. That group must have
        been opened by a previous call of 'open_clause_group' and must
        be activated.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.get_open_clause_group()
        1
        >>> qcdcl.add_lst([-1,-3])
        >>> qcdcl.close_clause_group(id1)
        >>> qcdcl.get_open_clause_group()
        0
        """
        self.__lib.qdpll_close_clause_group(self.__depqbf,clause_group_id)

    def configure(self, *args):
        """Configure solver instance via configuration list of strings.
        Returns null pointer on success and error string otherwise.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('-dep-man=simple','--incremental-use')
        Traceback (most recent call last):
        ...
        ValueError: unknown option:-dep-man=simple

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=foo')
        Traceback (most recent call last):
        ...
        ValueError: expecting 'simple' or 'qdag' after '--dep-man=':--dep-man=foo
        """
        logging.debug('QCDCL: Configure Parameter')
        for e in args:
            logging.info('Parameter "%s"', e)
            configure=self.__lib.qdpll_configure
            configure.restype = c_char_p
            ret=configure(self.__depqbf, e)
            if ret:
                raise ValueError,"%s:%s" % (ret,e)
                
        
    def deactivate_clause_group(self,clause_group_id):
        """Deactivates all clauses in the group 'clause_group'. The ID of a
        deactivated group cannot be passed to any API functions except
        'activate_clause_group' and
        'exists_clause_group'. Clause groups are activated at
        the time they are created. When calling 'evaluate', clauses
        in deactivated groups are ignored. Thus deactivating a clause
        group amounts to temporarily deleting these groups from the
        formula. However, unlike 'delete_clause_group' which
        permanently deletes the clauses in a group, deactivated groups
        can be activated again by calling
        'activate_clause_group'. This adds the formerly
        deactivated clauses back to the formula.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,-3])
        >>> qcdcl.close_clause_group(id1)
        >>> id2 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id2)
        >>> qcdcl.add_lst([1,2,4])
        >>> qcdcl.add_lst([1,-4,0])
        >>> qcdcl.close_clause_group(id2)

        >>> qcdcl.evaluate()
        20
        >>> relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
        >>> qcdcl.reset()
        >>> qcdcl.deactivate_clause_group(relevant_clause_groups[0])
        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset()
        >>> qcdcl.activate_clause_group(relevant_clause_groups[0])
        >>> qcdcl.evaluate()
        20
        """
        self.__lib.qdpll_deactivate_clause_group(self.__depqbf,clause_group_id)
        
    def delete_clause_group(self,clause_group_id):
        """Delete the clause group with ID 'clause_group'. The group must be
        activated. The ID of the deleted group becomes invalid and
        must not be passed to the API functions anymore. All clauses
        in the deleted group are deleted from the formula.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.exists_clause_group(id1)
        1
        >>> qcdcl.delete_clause_group(id1)
        >>> qcdcl.exists_clause_group(id1)
        0
        """
        self.__lib.qdpll_delete_clause_group(self.__depqbf,clause_group_id)
        
    def dump_dep_graph(self):
        """Dump dependency graph to 'stdout' in DOT format.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2,3])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([4,5])
        >>> qcdcl.add_lst([1,4])
        >>> qcdcl.add_lst([2,-5])

        >>> qcdcl.init_deps()
        >>> qcdcl.dump_dep_graph()
        digraph qdag {
          { rank=same;
          }
          { rank=same;
            a1[shape=box];
            a2[shape=box, peripheries=2];
          }
          { rank=same;
            e4[shape=diamond];
            e5[shape=diamond, peripheries=2];
          }
        a2 -> e5[style=invisible, arrowhead=none]
          a2 -> e5[style=solid];
          a2 -> a1[style=solid, color=blue, arrowhead=none];
          e5 -> e4[style=solid, color=blue, arrowhead=none];
        }
        """
        with delayed_stdout():
            self.__lib.qdpll_dump_dep_graph(self.__depqbf)


    def evaluate(self):
        """Solve the formula."""
        return self.__lib.qdpll_sat(self.__depqbf)

    def exists_clause_group(self,clause_group_id):
        """Returns non-zero if and only if (1) a clause group with ID
        'clause_group' has been created before and (2) the ID
        'clause_group' was returned by 'new_clause_group' and
        (3) that clause group was not deleted by calling
        'delete_clause_group'.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.exists_clause_group(0)
        False

        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.exists_clause_group(id1)
        True
        """
        return bool(self.__lib.qdpll_exists_clause_group(self.__depqbf,clause_group_id))

    def _free(self,ptr):
        """Free memory manually, e.g., required for functions:
        get_relevant_clause_groups, get_relevant_assumptions,
        get_assumption_candidates

        """
        self.__lib.qdpll_freeme(ptr)

    def get_assumption_candidates(self):
        """Returns a zero-terminated array of LitIDs of variables which can
        safely be assigned as assumptions by function
        'assume'. The array may contain both existential
        (positive LitIDs) and universal variables (negative LitIDs)
        which are not necessarily from the leftmost quantifier set in
        the prefix.

        NOTE: the caller is responsible to release the memory of the
        array returned by this function by means of _free(ptr). You
        should use the iterator based method
        (iter_assumption_candidates) which does housekeeping.


        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.add_lst([1])
        >>> qcdcl.add_lst([2])

        >>> cand = qcdcl.get_assumption_candidates()
        >>> cand[0]
        2
        >>> cand[1]
        1
        >>> i = 0       
        >>> while cand[i]:
        ...     i+=1
        >>> i
        2
        >>> qcdcl._free(cand)

        """
        get_assumption_candidates=self.__lib.qdpll_get_assumption_candidates
        get_assumption_candidates.restype = LitID_P
        return get_assumption_candidates(self.__depqbf)

    def iter_assumption_candidates(self): 
        """Returns a zero-terminated array of LitIDs of variables which can
        safely be assigned as assumptions by function
        'assume'. The array may contain both existential
        (positive LitIDs) and universal variables (negative LitIDs)
        which are not necessarily from the leftmost quantifier set in
        the prefix.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.add_lst([1])
        >>> qcdcl.add_lst([2])

        >>> for i in qcdcl.iter_assumption_candidates():print(i)
        2
        1
        >>> cand=list(qcdcl.iter_assumption_candidates())
        >>> cand
        [2, 1]
        """
        res = self.get_assumption_candidates()
        i = 0
        while res[i]:
            yield res[i]
            i+=1
        # Free memory of array returned by
        # 'qcdcl.get_assumption_candidates'.  This is the caller's
        # responsibility.
        self.__lib.qdpll_freeme(res)


    def get_max_declared_var_id(self):
        """Return largest declared variable ID.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.add_lst([1])
        >>> qcdcl.add_lst([2])
        >>> qcdcl.get_max_declared_var_id()
        2
        >>> qcdcl.add_lst([3,4,5,6,7,8,9])

        >>> qcdcl.get_max_declared_var_id()
        9
        """
        return self.__lib.qdpll_get_max_declared_var_id(self.__depqbf)

    def get_max_scope_nesting(self):
        """Returns the nesting level of the current rightmost scope.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1

        >>> qcdcl.get_max_scope_nesting()
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        3
        >>> qcdcl.add_lst([5,6])
        >>> qcdcl.get_max_scope_nesting()
        3
        """
        return self.__lib.qdpll_get_max_scope_nesting(self.__depqbf)

    def get_nesting_of_var(self,var_id):
        """Returns the nesting level 'level' in the range '1 <= level <=
        get_max_scope_nesting()' of the previously declared
        variable with ID 'id'. Returns 0 if the variable with ID 'id'
        is free, i.e. not explicitly associated to a quantifier
        block. Fails if 'id' does not correspond to a declared
        variable, which should be checked with function
        'is_var_declared()' before.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        3
        >>> qcdcl.add_lst([5,6])
        >>> qcdcl.get_nesting_of_var(1)
        1
        >>> qcdcl.get_nesting_of_var(3)
        2
        >>> qcdcl.get_nesting_of_var(5)
        3
        """
        return self.__lib.qdpll_get_nesting_of_var(self.__depqbf,var_id)

    def get_open_clause_group(self):
        """Returns the ID of the currently open clause group, or NULL if no
        group is currently open. If there is currently no open group,
        then all clauses added via 'add' will be permanently
        added to the formula and cannot be removed.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.get_open_clause_group()
        0
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.get_open_clause_group () == id1
        True
        """
        return self.__lib.qdpll_get_open_clause_group(self.__depqbf)

    def get_relevant_assumptions(self):
        """Returns a zero-terminated array of LitIDs representing those
        assumptions (passed to the solver using 'assume()')
        which were used by the solver to determine (un)satisfiability
        by the most recent call of 'evaluate'.

        NOTE: the caller is responsible to release the memory of the
        array returned by this function by means of _free(ptr.)  You
        should use the iterator based method
        (iter_relevant_assumptions) which does housekeeping.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([5,6])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        2
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        3
        >>> qcdcl.add_lst([3,4])
        >>> qcdcl.add_lst([5,-1,-3])
        >>> qcdcl.add_lst([6,1,2,4])
        >>> qcdcl.add_lst([6,1,-4])
        
        >>> qcdcl.print_dimacs()
        p cnf 6 3
        e 5 6 0
        a 1 2 0
        e 3 4 0
        5 -1 -3 0
        6 1 2 4 0
        6 1 -4 0
        >>> qcdcl.assume(-5)
        >>> qcdcl.assume(-6)
        >>> qcdcl.evaluate()
        20

        >>> cand=qcdcl.get_relevant_assumptions()
        >>> cand[0]
        -6
        >>> cand[1]
        0
        >>> qcdcl._free(cand)

        """
        get_relevant_assumptions=self.__lib.qdpll_get_relevant_assumptions
        get_relevant_assumptions.restype = LitID_P
        return get_relevant_assumptions(self.__depqbf)

    def iter_relevant_assumptions(self):
        """Returns a zero-terminated array of LitIDs representing those
        assumptions (passed to the solver using 'assume()')
        which were used by the solver to determine (un)satisfiability
        by the most recent call of 'evaluate'.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([5,6])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        2
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        3
        >>> qcdcl.add_lst([3,4])
        >>> qcdcl.add_lst([5,-1,-3])
        >>> qcdcl.add_lst([6,1,2,4])
        >>> qcdcl.add_lst([6,1,-4])
        
        >>> qcdcl.print_dimacs()
        p cnf 6 3
        e 5 6 0
        a 1 2 0
        e 3 4 0
        5 -1 -3 0
        6 1 2 4 0
        6 1 -4 0
        >>> qcdcl.assume(-5)
        >>> qcdcl.assume(-6)
        >>> qcdcl.evaluate()
        20

        >>> relevant_assumptions=list(qcdcl.iter_relevant_assumptions())
        >>> relevant_assumptions
        [-6]
        >>> sum(1 for _ in relevant_assumptions)
        1
        """
        res = self.get_relevant_assumptions()
        i = 0
        while res[i]:
            yield res[i]
            i+=1
        # Free memory of array returned by
        # 'qcdcl.get_relevant_clause_groups'.  This is the caller's
        # responsibility.
        self.__lib.qdpll_freeme(res)

    def get_relevant_clause_groups(self):
        """Returns a zero-terminated array of clause group IDs representing
        those clause groups which contain clauses used by the solver
        to determine UNSATISFIABILITY by the most recent call of
        'evaluate'. That is, this function returns a subset of those
        clause groups which participiate in the resolution refutation
        of the current formula. This function can be called only if
        the most recent call of 'evaluate' returned
        QDPLL_RESULT_UNSAT. The groups returned by this function are
        all activated.

        NOTE: the caller is responsible to release the memory of the
        array returned by this function. You should use the iterator
        based method (iter_relevant_clause_groups) which does
        housekeeping.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,-3])
        >>> qcdcl.close_clause_group(id1)
        >>> id2 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id2)
        >>> qcdcl.add_lst([1,2,4])
        >>> qcdcl.add_lst([1,-4])
        >>> qcdcl.close_clause_group(id2)
        >>> res = qcdcl.evaluate()
        >>> assert (res == QDPLL_RESULT_UNSAT)

        >>> relevant_clause_groups = qcdcl.get_relevant_clause_groups()
        >>> relevant_clause_groups[0]
        2
        >>> relevant_clause_groups[1]
        0
        >>> qcdcl._free(relevant_clause_groups)
        """
        get_relevant_clause_groups=self.__lib.qdpll_get_relevant_clause_groups
        get_relevant_clause_groups.restype = ClauseGroupID_P
        return get_relevant_clause_groups(self.__depqbf)

    def iter_relevant_clause_groups(self):
        """Returns a zero-terminated array of clause group IDs representing
        those clause groups which contain clauses used by the solver
        to determine UNSATISFIABILITY by the most recent call of
        'evaluate'. That is, this function returns a subset of those
        clause groups which participiate in the resolution refutation
        of the current formula. This function can be called only if
        the most recent call of 'evaluate' returned
        QDPLL_RESULT_UNSAT. The groups returned by this function are
        all activated.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,-3])
        >>> qcdcl.close_clause_group(id1)
        >>> id2 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id2)
        >>> qcdcl.add_lst([1,2,4])
        >>> qcdcl.add_lst([1,-4])
        >>> qcdcl.close_clause_group(id2)
        >>> res = qcdcl.evaluate()
        >>> assert (res == QDPLL_RESULT_UNSAT)

        >>> relevant_clause_groups = list(qcdcl.iter_relevant_clause_groups())
        >>> relevant_clause_groups
        [2]
        >>> sum(1 for _ in relevant_clause_groups)
        1
        """
        res=self.get_relevant_clause_groups()
        i=0
        while res[i]:
            yield res[i]
            i+=1
        # Free memory of array returned by
        # 'qcdcl.get_relevant_clause_groups'.  This is the caller's
        # responsibility.
        self.__lib.qdpll_freeme(res)

    def get_scope_type(self,var_id):
        """Returns the quantifier type (i.e. either QDPLL_QTYPE_EXISTS or
        QDPLL_QTYPE_FORALL) of the scope at nesting level 'nesting'.
        Returns zero if there is no scope with nesting level
        'nesting'.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([5,6])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 2)
        2
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 3)
        3
        >>> qcdcl.get_scope_type(1)
        -1
        >>> qcdcl.get_scope_type(2)
        1
        >>> qcdcl.get_scope_type(3)
        -1
        >>> qcdcl.get_scope_type(4)
        0
        """
        return self.__lib.qdpll_get_scope_type(self.__depqbf,var_id)

    def get_value(self,var_id):
        """Get assignment of variable.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.get_value(1)
        0
        >>> qcdcl.get_value(2)
        0
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.assume(-1)

        >>> qcdcl.evaluate()
        10
        >>> qcdcl.get_value(1)
        -1
        >>> qcdcl.get_value(2)
        1
        >>> qcdcl.reset()

        """
        return self.__lib.qdpll_get_value(self.__depqbf,var_id)

    def gc(self):
        """Enforce the deletion of variables which have no occurrences left,
        and delete empty quantifier blocks. E.g. after 'pop',
        'delete_clause_group', a variable might not have any
        clauses left if all the clauses containing that variable were
        removed by the pop operation. However, the variable is still
        present in the prefix that was added by the user and
        'is_var_declared' returns non-zero for these variables. The
        function 'gc' cleans up the prefix and deletes variables
        which do not occur in the current formula and removes empty
        quantifier blocks. After 'gc', is_var_declared' returns
        zero for variables which have been removed.  

        NOTE: Calling 'pop' or 'delete_clause_group' does
        NOT delete variables and quantifier blocks, but only clauses.

        IMPORTANT NOTE: do NOT call 'gc' unless you want to
        remove variables and quantifier blocks which you have
        previously added to the formula.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,3])
        >>> qcdcl.close_clause_group(id1)
        >>> qcdcl.print_dimacs()
        p cnf 4 1
        a 1 2 0
        e 3 4 0
        -1 3 0
        >>> qcdcl.delete_clause_group(id1)

        >>> qcdcl.gc()
        >>> qcdcl.is_var_declared(3)
        False
        >>> qcdcl.print_dimacs()
        p cnf 0 0
        """
        self.__lib.qdpll_gc(self.__depqbf)
        
    def init_deps(self):
        """Initialize the current dependency manager. The dependency scheme is
        computed with respect to the clauses added by 'add'. If
        the dependency scheme has been computed already then calling
        this function has no effect. The dependency manager can be
        reset and re-initialized by calling 'reset_deps' and
        then 'init_deps'


        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2,3])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([4,5])
        >>> qcdcl.add_lst([1,4])
        >>> qcdcl.add_lst([2,-5])

        >>> qcdcl.init_deps()
        >>> qcdcl.dump_dep_graph()
        digraph qdag {
          { rank=same;
          }
          { rank=same;
            a1[shape=box];
            a2[shape=box, peripheries=2];
          }
          { rank=same;
            e4[shape=diamond];
            e5[shape=diamond, peripheries=2];
          }
        a2 -> e5[style=invisible, arrowhead=none]
          a2 -> e5[style=solid];
          a2 -> a1[style=solid, color=blue, arrowhead=none];
          e5 -> e4[style=solid, color=blue, arrowhead=none];
        }
        """
        self.__lib.qdpll_init_deps (self.__depqbf)

    def is_var_declared(self,var_id):
        """Returns non-zero if and only if (1) a variable with ID 'id' has
        been added to the solver by a previous call of 'add' or
        'add_var_to_scope'. For example, the function can be
        used to check if the variable of each literal in a clause to
        be added has been declared already. If not, then it can be
        declared by 'add_var_to_scope' and put in the right
        scope.  

        NOTE: if a clause containing literals of undeclared variables
        is added by 'add' then these literals by default will be
        existentially quantified and put in the leftmost scope.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.is_var_declared(1)
        True
        >>> qcdcl.is_var_declared(2)
        True
        >>> qcdcl.is_var_declared(3)
        False
        """
        return bool(self.__lib.qdpll_is_var_declared(self.__depqbf,var_id))

    def new_clause_group (self):
        """Creates a new clause group and returns its ID. The returned ID is a
        handle of the created clause group and should be passed to API
        functions to manipulate clause groups. Initially, the newly
        created clause group is empty (i.e. it does not contain any
        clauses) and it is closed. To add clauses to a group, the
        group must be opened by 'open_clause_group'. Only one clause
        group can be open at a time. Clauses can be added to the
        currently open group as usual by calling 'add'. To add
        clauses to a different group, the currently open group must be
        closed again by 'close_clause_group' and the other group must
        be opened. Clause groups are activated at the time they are
        created and can be deactivated by calling
        'deactivate_clause_group'.
        
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([3,4])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,3])
        >>> qcdcl.close_clause_group(id1)
        >>> qcdcl.exists_clause_group(id1)
        True
        """
        return self.__lib.qdpll_new_clause_group (self.__depqbf)

    def new_scope(self,qtype):
        """Open a new scope at the right end of the quantifier prefix, where
        variables can be added by 'add'. The opened scope must
        be closed by adding '0' via 'add'. Returns the nesting
        of the added scope, which should be used as a handle of this
        scope, and which can safely be passed to
        'add_var_to_scope'.

        NOTE: will fail if there is an opened scope already.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope(QDPLL_QTYPE_FORALL)
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.print_dimacs()
        p cnf 2 0
        a 1 2 0
        """
        return self.__lib.qdpll_new_scope(self.__depqbf,qtype)

    def new_scope_at_nesting(self,quantifier_type,level):
        """Open a new scope at nesting level 'nesting >= 1' with quantifier
        type 'qtype'. Variables can be added to the scope opened by
        the most recent call of this function by 'add' (similar
        to 'new_scope'). The opened scope must be closed by
        adding '0' via 'add'. Returns the nesting of the added
        scope, which should be used as a handle of this scope, and
        which can safely be passed to 'add_var_to_scope'.

        NOTE: the run time of this function is linear in the length of
        quantifier prefix.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        """
        logging.debug('QCDCL: open new scope')
        logging.debug('quantifier=%i nesting_level=%i ',quantifier_type,level)
        return self.__lib.qdpll_new_scope_at_nesting(self.__depqbf,
                                                     quantifier_type,
                                                     level)

    def open_clause_group(self,clause_group_id):
        """Open the clause group with ID 'clause_group'. That group must not
        be open already and must be activated. Only one group can be
        open at a time. Clauses can be added to the currently open
        group as usual by calling 'add'. An open group will stay
        open across calls of e.g. 'evaluate'. However, to add clauses
        to a another group, the currently open group must be closed
        again by 'close_clause_group' and the other group must be
        opened.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2])
        >>> id1 = qcdcl.new_clause_group()
        >>> qcdcl.open_clause_group(id1)
        >>> qcdcl.add_lst([-1,2])
        >>> qcdcl.close_clause_group(id1)
        """
        self.__lib.qdpll_open_clause_group(self.__depqbf,clause_group_id)

    def pop(self):
        """Decrease the current frame index by one and disable all clauses
        associated to the old, popped off frame. Returns either the
        old frame index which was popped off or zero if there is no
        frame to be popped off.
        
        IMPORTANT NOTE: calls of the push/pop API cannot be mixed with
        call of the clause group API. The solver will abort if a
        function of the clause group API is called after a call of
        either 'push' or 'pop', or vice versa.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.new_scope_at_nesting (QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([2])
        >>> qcdcl.add_lst([1,-2])
        >>> qcdcl.add_lst([-1,2])
        >>> qcdcl.print_dimacs()
        p cnf 2 2
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset()
        >>> qcdcl.push()
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.push()
        2
        >>> qcdcl.add_lst([1,3])
        >>> qcdcl.print_dimacs()
        p cnf 3 4
        e 3 0
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        1 2 0
        3 0
        >>> qcdcl.evaluate()
        20
        >>> qcdcl.reset()
        >>> qcdcl.pop()
        2
        >>> qcdcl.pop()
        1
        >>> qcdcl.print_dimacs()
        p cnf 3 4
        e 3 0
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        >>> qcdcl.evaluate()
        10
        """
        logging.debug('QCDCL: decreasing frame index by 1')
        logging.debug(' and disable all clauses associated to the old')
        return self.__lib.qdpll_pop(self.__depqbf)

    def push(self):
        """Increase the current frame index by one. Every clause added by
        'add' is attached to the current frame. The clauses
        attached to a frame will be discarded if the frame is popped
        off by 'pop'. Returns the current frame index resulting
        from the push operation.

        IMPORTANT NOTE: calls of the push/pop API cannot be mixed with
        call of the clause group API. The solver will abort if a
        function of the clause group API is called after a call of
        either 'push' or 'pop', or vice versa.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.new_scope_at_nesting (QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([2])
        >>> qcdcl.add_lst([1,-2])
        >>> qcdcl.add_lst([-1,2])
        >>> qcdcl.print_dimacs()
        p cnf 2 2
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset()
        >>> qcdcl.push()
        1
        >>> qcdcl.add_lst([1,2])
        >>> qcdcl.push()
        2
        >>> qcdcl.add_lst([1,3])
        >>> qcdcl.print_dimacs()
        p cnf 3 4
        e 3 0
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        1 2 0
        3 0
        >>> qcdcl.evaluate()
        20
        >>> qcdcl.reset()
        >>> qcdcl.pop()
        2
        >>> qcdcl.pop()
        1
        >>> qcdcl.print_dimacs()
        p cnf 3 4
        e 3 0
        a 1 0
        e 2 0
        1 -2 0
        -1 2 0
        >>> qcdcl.evaluate()
        10
        """
        logging.debug('QCDCL: increasing frame index by 1')
        return self.__lib.qdpll_push(self.__depqbf)

    def print_deps(self,var_id):
        """Print zero-terminated list of dependencies for 
        given variable to 'stdout'.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')

        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1,2,3])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([4,5])
        >>> qcdcl.add_lst([1,4])
        >>> qcdcl.add_lst([2,-5])
        
        >>> qcdcl.init_deps()
        >>> qcdcl.print_deps(1)
        4 5 0
        """
        with delayed_stdout():
            self.__lib.qdpll_print_deps(self.__depqbf,var_id)

    def print_dimacs(self,output=None):
        """
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.print_dimacs()
        p cnf 2 0
        a 1 2 0

        >>> qcdcl.print_dimacs(sys.stdout)
        p cnf 2 0
        a 1 2 0

        >>> qcdcl.print_dimacs('-')
        p cnf 2 0
        a 1 2 0

        >>> from tempfile import TemporaryFile
        >>> temp_f = TemporaryFile()
        >>> qcdcl.print_dimacs(temp_f)
        >>> temp_f.seek(0)
        >>> for line in temp_f.readlines():print line,
        p cnf 2 0
        a 1 2 0

        >>> qcdcl.print_dimacs('-')
        p cnf 2 0
        a 1 2 0
        >>> temp_f.close()
        """
        with wopen(output) as f:
             logging.debug('QCDCL: DIMACS formula goes to %s',output)
             sys.stdout.flush()
             self.__lib.qdpll_print(self.__depqbf, c_file(f))
             if is_stdout_redirected() and (not isinstance(output,str) or output=='-') and not isinstance(output,file):
                 logging.debug('QCDCL: DIMCAS formula goes to stdout')
                 f.seek(0)
                 [sys.stdout.write(line) for line in f.readlines()]

    def print_qdimacs_output(self):
        """Print QDIMACS-compliant output.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.print_qdimacs_output()
        s cnf -1 2 0
        """
        with delayed_stdout():
            self.__lib.qdpll_print_qdimacs_output(self.__depqbf)

    def print_stats(self):
        """Print statistics to 'stderr'.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.evaluate()
        10
        >>> qcdcl.print_stats() # doctest: +ELLIPSIS
        <BLANKLINE>
        ---------------- STATS ----------------
        ...
        """
        with delayed_stderr():
            self.__lib.qdpll_print_stats (self.__depqbf)

    def reset(self):
        """Reset internal solver state, keep clauses and variables.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.add_lst([1])
        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset()

        >>> qcdcl.assume(-1)
        >>> qcdcl.evaluate()
        20
        """
        logging.debug('QCDCL: reseting solver...')
        self.__lib.qdpll_reset(self.__depqbf)
        logging.debug('QCDCL: done')

    def reset_deps(self):
        """Reset the current dependency manager. Dependencies can be
        re-initialized by calling 'deps_init' or 'evaluate'.
        """
        self.__lib.qdpll_reset_deps(self.__depqbf)

    def reset_stats(self):
        """Reset collected statistics.  

        Note: Statistics need to be activated by setting '#define
        COMPUTE_STATS 1' in file 'qdpll_config.h' and recompiling the
        qdpll library. Alternatively, you can run the makefile of the
        python lib with options --with-stats.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.evaluate()
        10
        >>> qcdcl.print_stats() # doctest: +ELLIPSIS
        <BLANKLINE>
        ---------------- STATS ----------------
        ...
        >>> qcdcl.reset_stats()
        """
        self.__lib.qdpll_reset_stats(self.__depqbf)
        
    def reset_learned_constraints(self):
        """Discard all learned constraints.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add(1)
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        >>> qcdcl.evaluate()
        10
        >>> qcdcl.reset_learned_constraints()
        """
        self.__lib.qdpll_reset_learned_constraints(self.__depqbf)

    def var_depends(self,var_id1,var_id2):
        """Returns non-zero if variable 'id2' depends on variable 'id1',
        i.e. if id1 < id2, with respect to the current dependency
        scheme.
        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')
        
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_FORALL, 1)
        1
        >>> qcdcl.add_lst([1])
        >>> qcdcl.new_scope_at_nesting(QDPLL_QTYPE_EXISTS, 2)
        2
        >>> qcdcl.add_lst([2])
        >>> qcdcl.add_lst([1,2])

        >>> qcdcl.init_deps()
        >>> qcdcl.var_depends(1,2)
        True
        >>> qcdcl.var_depends(2,1)
        False
        """
        return bool(self.__lib.qdpll_var_depends(self.__depqbf, var_id1, var_id2))


if __name__ == "__main__":
    import doctest
    doctest.testmod()


