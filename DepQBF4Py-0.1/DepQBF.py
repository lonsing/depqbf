#TODO: lazy parameter loading
#TODO: documentation
#TODO: fix example files
#TODO: fix function naming in the docstrings

from ctypes import *
import sys
import logging
from logging.config import fileConfig
fileConfig("logging.conf")

from file_helper import *
from basic_types import *

class QCDCL(object):
    __lib=None
    __LIB_NAME='../libqdpll.so.1.0'

    def __load_libs(self):
        if not self.__lib:
            logging.debug('Shared Lib: Loading...')
            logging.debug('Shared Lib: %s' %self.__LIB_NAME)
            self.__lib = cdll.LoadLibrary(self.__LIB_NAME)

    def __init__(self):
        logging.debug('QCDCL: Initializing...')
        self.__load_libs()
        qdpll_create=self.__lib.qdpll_create
        qdpll_create.restype = QDPLL_P
        self.__depqbf = qdpll_create()
        logging.debug('QCDCL: Initialized')

    def __del__(self):
        logging.debug('QCDCL: Deleting...')
        self.__lib.qdpll_delete(self.__depqbf)
        logging.debug('QCDCL: Deleted')

    def activate_clause_group(self,clause_group_id):
        self.__lib.qdpll_activate_clause_group(self.__depqbf,clause_group_id)
        
    def add(self,var_id):
        """Add variables or literals to clause or opened scope. Scopes are
        opened by either 'qdpll_new_scope' or
        'qdpll_new_scope_at_nesting'. If scope is opened, then 'id' is
        interpreted as a variable ID, otherwise 'id' is interpreted as
        a literal. If 'id == 0' then the clause/scope is closed.

        IMPORTANT NOTE: added clauses are associated to the current
        frame. If 'qdpll_push' has NOT been called before then the
        added clauses are permanently added to the formula. Otherwise,
        they are added to the current frame and can be remove from the
        formula by calling 'qdpll_push'.

        Similarly, added clauses are associated to the clause group
        which has been opened before by calling
        'qdpll_open_clause_group', if any. If
        'qdpll_open_clause_group' has NOT been called before then the
        added clauses are permanently added to the formula.

        NOTE: function will fail if a scope is opened and 'id' is
        negative.

        NOTE: if a clause containing literals of undeclared variables
        is added by 'qdpll_add' then these literals by default will be
        existentially quantified and put in the leftmost scope. That
        is, the variable of these literals is interpreted as a free
        variable. See also function 'qdpll_is_var_declared' below. */
        
        If the result is small enough to fit in an int, return an int.
        Else return a long.

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
        logging.debug('QCDCL: add_variable=%i'%var_id)
        self.__lib.qdpll_add(self.__depqbf, var_id)
        
    def add_var_to_scope (self,var_id,nesting):
        """Add a new variable with ID 'id' to the scope with nesting level
        'nesting'. The scope must exist, i.e. it must have been added
        by either 'qdpll_new_scope' or
        'qdpll_new_scope_at_nesting'. The value of the parameter
        'nesting' of this function should be a value returned by a
        previous call of 'qdpll_new_scope' or
        'qdpll_new_scope_at_nesting'. In any case, it must be smaller
        than or equal to the return value of
        'qdpll_get_max_scope_nesting'.

        >>> qcdcl = QCDCL()
        >>> qcdcl.configure('--dep-man=simple','--incremental-use')        
        """
        self.__lib.qdpll_add_var_to_scope(self.__depqbf,var_id,nesting)

    def adjust_vars (self, var_id):
        """Ensure var table size to be at least 'num'.
        >>>
        
        """
        self.__lib.qdpll_adjust_vars(self.__depqbf,var_id)

    def assume(self,lit_id):
        """Assign a variable as assumption. A later call of 'qdpll_sat(...)'
        solves the formula under the assumptions specified before. If
        'id' is negative then variable with ID '-id' will be assigned
        false, otherwise variable with ID 'id' will be assigned
        true.
        """
        self.__lib.qdpll_assume(self.__depqbf,lit_id)

    def close_scope(self):
        """Close open scope."""
        self.add(0)
    
    def close_clause_group(self,clause_group_id):
        """Close the clause group with ID 'clause_group'. That group must have
        been opened by a previous call of 'open_clause_group' and must
        be activated.
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
            logging.info('Parameter "%s"'%e)
            configure=self.__lib.qdpll_configure
            configure.restype = c_char_p
            ret=configure(self.__depqbf, e)
            if ret:
                raise ValueError,"%s:%s" % (ret,e)
                
        
    def deactivate_clause_group(self,clause_group_id):
        """Deactivates all clauses in the group 'clause_group'. The ID of a
        deactivated group cannot be passed to any API functions except
        'qdpll_activate_clause_group' and
        'qdpll_exists_clause_group'. Clause groups are activated at
        the time they are created. When calling 'qdpll_sat', clauses
        in deactivated groups are ignored. Thus deactivating a clause
        group amounts to temporarily deleting these groups from the
        formula. However, unlike 'qdpll_delete_clause_group' which
        permanently deletes the clauses in a group, deactivated groups
        can be activated again by calling
        'qdpll_activate_clause_group'. This adds the formerly
        deactivated clauses back to the formula.
        """
        self.__lib.qdpll_deactivate_clause_group(self.__depqbf,clause_group_id)
        
    def delete_clause_group(self,clause_group_id):
        """Delete the clause group with ID 'clause_group'. The group must be
        activated. The ID of the deleted group becomes invalid and
        must not be passed to the API functions anymore. All clauses
        in the deleted group are deleted from the formula.
        """
        self.__lib.qdpll_delete_clause_group(self.__depqbf,clause_group_id)
        
    def dump_dep_graph(self):
        """Dump dependency graph to 'stdout' in DOT format."""
        self.__lib.qdpll_dump_dep_graph(self.__depqbf)

    def evaluate(self):
        """Solve the formula."""
        return self.__lib.qdpll_sat(self.__depqbf)

    def exists_clause_group(self,clause_group_id):
        """Returns non-zero if and only if (1) a clause group with ID
        'clause_group' has been created before and (2) the ID
        'clause_group' was returned by 'qdpll_new_clause_group' and
        (3) that clause group was not deleted by calling
        'qdpll_delete_clause_group'.
        """
        return self.__lib.qdpll_exists_clause_group(self.__depqbf,clause_group_id)

    def get_assumption_candidates(self):
        """Returns a zero-terminated array of LitIDs of variables which can
        safely be assigned as assumptions by function
        'qdpll_assume'. The array may contain both existential
        (positive LitIDs) and universal variables (negative LitIDs)
        which are not necessarily from the leftmost quantifier set in
        the prefix.

        NOTE: the caller is responsible to release the memory of the
        array returned by this function.
        """
        get_assumption_candidates=self.__lib.qdpll_get_assumption_candidates
        get_assumption_candidates.restype = LitID_P
        return get_assumption_candidates(self.__depqbf)

    def get_max_declared_var_id(self):
        """Return largest declared variable ID."""
        return self.__lib.qdpll_get_max_declared_var_id(self.__depqbf)

    def get_max_scope_nesting(self):
        """Returns the nesting level of the current rightmost scope."""
        return self.__lib.qdpll_get_max_scope_nesting(self.__depqbf)

    def get_nesting_of_var(self,var_id):
        """Returns the nesting level 'level' in the range '1 <= level <=
        qdpll_get_max_scope_nesting()' of the previously declared
        variable with ID 'id'. Returns 0 if the variable with ID 'id'
        is free, i.e. not explicitly associated to a quantifier
        block. Fails if 'id' does not correspond to a declared
        variable, which should be checked with function
        'qdpll_is_var_declared()' before.
        """
        return self.__lib.qdpll_get_nesting_of_var(self.__depqbf,var_id)

    def get_open_clause_group(self):
        """Returns the ID of the currently open clause group, or NULL if no
        group is currently open. If there is currently no open group,
        then all clauses added via 'qdpll_add' will be permanently
        added to the formula and cannot be removed.
        """
        return self.__lib.qdpll_get_open_clause_group(self.__depqbf)

    def get_relevant_assumptions(self):

        get_relevant_assumptions=self.__lib.qdpll_get_relevant_assumptions
        get_relevant_assumptions.restype = LitID_P
        return get_relevant_assumptions(self.__depqbf)

    def get_relevant_assumptions_as_generator(self):
        res = self.get_relevant_assumptions()
        i = 0
        while res[i]:
            yield res[i]
            i+=1

    def get_relevant_clause_groups(self):
        get_relevant_clause_groups=self.__lib.qdpll_get_relevant_clause_groups
        get_relevant_clause_groups.restype = ClauseGroupID_P
        return get_relevant_clause_groups(self.__depqbf)

    def get_relevant_clause_groups_as_generator(self):
        res=self.get_relevant_clause_groups()
        i=0
        while res[i]:
            yield res[i]
            i+=1
        
    def get_scope_type(self,var_id):
        return self.__lib.qdpll_get_scope_type(self.__depqbf,var_id)

    def get_value(self,var_id):
        return self.__lib.qdpll_get_value(self.__depqbf,var_id)

    def gc(self):
        self.__lib.qdpll_gc(self.__depqbf)
        
    def init_deps(self):
        self.__lib.qdpll_init_deps (self.__depqbf)

    def is_var_declared(self,var_id):
        return self.__lib.qdpll_is_var_declared(self.__depqbf,var_id)

    def new_clause_group (self):
        return self.__lib.qdpll_new_clause_group (self.__depqbf)

    def new_scope(self,qtype):
        return self.__lib.qdpll_new_scope(self.__depqbf,qtype)

    def new_scope_at_nesting(self,quantifier_type,level):
        logging.debug('QCDCL: open new scope')
        logging.debug('quantifier=%i nesting_level=%i '%(quantifier_type,level))
        return self.__lib.qdpll_new_scope_at_nesting(self.__depqbf,quantifier_type,level)

    def open_clause_group(self,clause_group_id):
        self.__lib.qdpll_open_clause_group(self.__depqbf,clause_group_id)

    def pop(self):
        logging.debug('QCDCL: decreasing frame index by 1')
        logging.debug(' and disable all clauses associated to the old')
        return self.__lib.qdpll_pop(self.__depqbf)

    def push(self):
        logging.debug('QCDCL: increasing frame index by 1')
        return self.__lib.qdpll_push(self.__depqbf)

    def print_deps(self,var_id):
        self.__lib.print_dimacs_deps(self.__depqbf,var_id)

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
             logging.debug('QCDCL: DIMACS formula goes to %s' %output)
             sys.stdout.flush()
             self.__lib.qdpll_print(self.__depqbf, c_file(f))
             if is_stdout_redirected() and (not isinstance(output,str) or output=='-') and not isinstance(output,file):
                 logging.debug('QCDCL: DIMCAS formula goes to stdout')
                 f.seek(0)
                 [sys.stdout.write(line) for line in f.readlines()]

    def print_qdimacs_output(self):
        self.__lib.print_dimacs_qdimacs_output(self.__depqbf)

    def print_dimacs_stats(self):
        self.__lib.print_dimacs_stats (self.__depqbf)

    def reset(self):
        logging.debug('QCDCL: reseting solver...')
        self.__lib.qdpll_reset(self.__depqbf)
        logging.debug('QCDCL: done')

    def reset_deps(self):
        self.__lib.qdpll_reset_deps(self.__depqbf)

    def reset_stats(self):
        self.__lib.qdpll_reset_stats(self.__depqbf)
        
    def reset_learned_constraints(self):
        self.__lib.qdpll_reset_learned_constraints(self.__depqbf)

    def var_depends(self,var_id1,var_id2):
        return self.__lib. qdpll_var_depends(self.__depqbf, var_id1, var_id2)


if __name__ == "__main__":
    import doctest
    doctest.testmod()


        #print sys.stdout, type(sys.stdout)
        # PyFile_AsFile = pythonapi.PyFile_AsFile
        # PyFile_AsFile.argtypes = [py_object]
        # PyFile_AsFile.restype = FILE_P
        # if is_stdout_redirected():
        #     #Note: redirected output yields segfault hence use
        #     #      temporary file here (important for doctest)
        #     if not isinstance(output,str) or output=='-':
        #         from tempfile import TemporaryFile
        #         with TemporaryFile() as f:
        #             stdout_file=PyFile_AsFile(f)
        #             logging.debug('QCDCL: DIMACS formula goes to tempfile')
        #             sys.stdout.flush()
        #             self.__lib.print_dimacs(self.__depqbf, stdout_file)
        #             logging.debug('QCDCL: DIMCAS formula goes to stdout')
        #             f.seek(0)
        #             [sys.stdout.write(line) for line in f.readlines()]
        #         with open(output,'rw') as f:
        #             stdout_file=PyFile_AsFile(f)
        #             logging.debug('QCDCL: DIMACS formula goes to file %s' %f.name)
        #             self.__lib.print_dimacs(self.__depqbf, stdout_file)
