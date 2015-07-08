from ctypes import *

class QDPLL(Structure):
    pass

QDPLL_P=POINTER(QDPLL)

(QDPLL_QTYPE_EXISTS, QDPLL_QTYPE_UNDEF, QDPLL_QTYPE_FORALL) = (-1,0,1)
(QDPLL_RESULT_UNKNOWN,QDPLL_RESULT_SAT,QDPLL_RESULT_UNSAT) = (0,10,20)
(QDPLL_ASSIGNMENT_FALSE,QDPLL_ASSIGNMENT_UNDEF,QDPLL_ASSIGNMENT_TRUE) = (-1,0,1)

ClauseGroupID=c_int
ClauseGroupID_P=POINTER(ClauseGroupID)

LitID=c_int
LitID_P=POINTER(LitID)

def assignment2str(a):
    if a==QDPLL_ASSIGNMENT_UNDEF:
        return 'undef'
    elif a==QDPLL_ASSIGNMENT_FALSE:
        return 'false'
    elif a==QDPLL_ASSIGNMENT_TRUE:
        return 'true'
    else:
        raise TypeError()
