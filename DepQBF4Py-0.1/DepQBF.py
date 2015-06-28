#TODO: logging default prefix
#TODO: lazy parameter loading
#TODO: documentation
#TODO: fix example files

from ctypes import *
import logging
from logging.config import fileConfig
import sys

fileConfig("logging.conf")

class QDPLL(Structure):
    pass

QDPLL_P=POINTER(QDPLL)

(QDPLL_QTYPE_EXISTS, QDPLL_QTYPE_UNDEF, QDPLL_QTYPE_FORALL) = (-1,0,1)

class QDPLLResult(Structure):
    pass

(QDPLL_RESULT_UNKNOWN,QDPLL_RESULT_SAT,QDPLL_RESULT_UNSAT) = (0,10,20)

class QDPLLAssignment(Structure):
    pass

(QDPLL_ASSIGNMENT_FALSE,QDPLL_ASSIGNMENT_UNDEF,QDPLL_ASSIGNMENT_TRUE) = (-1,0,1)

def assignment2str(a):
    if QDPLL_ASSIGNMENT_UNDEF:
        return 'undef'
    elif QDPLL_ASSIGNMENT_FALSE:
        return 'false'
    elif QDPLL_ASSIGNMENT_TRUE:
        return 'true'
    else:
        raise TypeError()

class FILE(Structure):
    pass

FILE_P=POINTER(FILE)

ClauseGroupID=c_int
ClauseGroupID_P=POINTER(ClauseGroupID)

LitID=c_int
LitID_P=POINTER(LitID)

#Helper Functions
from contextlib import contextmanager

@contextmanager
def stdout_redirector(stream):
    old_stdout = sys.stdout
    sys.stdout = stream
    try:
        yield
    finally:
        sys.stdout = old_stdout


#MAIN Thingie
class QCDCL(object):
    __lib=None
    __LIB_NAME='../libqdpll.so.1.0'

    def __load_libs(self):
        if not self.__lib:
            logging.debug('Shared Lib: Loading...')
            logging.debug('Shared Lib: %s' %self.__LIB_NAME)
            self.__lib = cdll.LoadLibrary(self.__LIB_NAME)
            logging.debug('Shared Lib: libc')
            self.__libc = CDLL(None)
            logging.debug('Shared Lib: Loaded')

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
        >>> qcdcl.add(2)
        >>> qcdcl.add(0)

        #TODO: yields segfault        
        >>> qcdcl.qdpll_print()
        s cnf -1 2 0
        """
        logging.debug('QCDCL: add_variable=%i'%var_id)
        self.__lib.qdpll_add(self.__depqbf, var_id)
        
    def add_var_to_scope (self,var_id,nesting):
        self.__lib.qdpll_add_var_to_scope(self.__depqbf,var_id,nesting)

    def adjust_vars (self, var_id):
        self.__lib.qdpll_adjust_vars(self.__depqbf,var_id)

    def assume(self,lit_id):
        self.__lib.qdpll_assume(self.__depqbf,lit_id)

    def close_scope(self):
        self.add(0)
    
    def close_clause_group(self,clause_group_id):
        self.__lib.qdpll_close_clause_group(self.__depqbf,clause_group_id)

    def configure(self, *args):
        logging.debug('QCDCL: Configure Parameter')
        for e in args:
            logging.info('Parameter "%s"'%e)
            self.__lib.qdpll_configure(self.__depqbf, e)
        
    def deactivate_clause_group(self,clause_group_id):
        self.__lib.qdpll_deactivate_clause_group(self.__depqbf,clause_group_id)
        
    def delete_clause_group(self,clause_group_id):
        self.__lib.qdpll_delete_clause_group(self.__depqbf,clause_group_id)
        
    def dump_dep_graph(self):
        self.__lib.qdpll_dump_dep_graph(self.__depqbf)

    def evaluate(self):
        return self.__lib.qdpll_sat(self.__depqbf)

    def exists_clause_group(self,clause_group_id):
        return self.__lib.qdpll_exists_clause_group(self.__depqbf,clause_group_id)

    def get_assumption_candidates(self):
        get_assumption_candidates=self.__lib.qdpll_get_assumption_candidates
        get_assumption_candidates.restype = LitID_P
        return get_assumption_candidates(self.__depqbf)

    def get_max_declared_var_id(self):
        return self.__lib.qdpll_get_max_declared_var_id(self.__depqbf)

    def get_max_scope_nesting(self):
        return self.__lib.qdpll_get_max_scope_nesting(self.__depqbf)

    def get_nesting_of_var(self,var_id):
        return self.__lib.qdpll_get_nesting_of_var(self.__depqbf,var_id)

    def get_open_clause_group(self):
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

    def qdpll_print(self):
        PyFile_AsFile = pythonapi.PyFile_AsFile
        PyFile_AsFile.argtypes = [py_object]
        PyFile_AsFile.restype = FILE_P        
        stdout_file=PyFile_AsFile(sys.stdout)
        logging.debug('QCDCL: DIMCAS formula goes to stdout')
        self.__lib.qdpll_print(self.__depqbf, stdout_file)

    def print_deps(self,var_id):
        self.__lib.qdpll_print_deps(self.__depqbf,var_id)

    def print_qdimacs_output(self):
        self.__lib.qdpll_print_qdimacs_output(self.__depqbf)

    def qdpll_print_stats(self):
        self.__lib.qdpll_print_stats (self.__depqbf)

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
