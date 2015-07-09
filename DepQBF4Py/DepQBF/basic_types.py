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
