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
from contextlib import contextmanager
from tempfile import TemporaryFile
from os import fdopen
import sys
from stdout_helper import is_stdout_redirected


class FILE(Structure):
    pass

FILE_P=POINTER(FILE)

def c_file(f):
    PyFile_AsFile = pythonapi.PyFile_AsFile
    PyFile_AsFile.argtypes = [py_object]
    PyFile_AsFile.restype = FILE_P
    return PyFile_AsFile(f)


@contextmanager
def wopen(output=None):
    if isinstance(output,str) and output != '-':
        f=open(output,'rw')
    else:
        if is_stdout_redirected() and not isinstance(output,file):
            #Note: redirected output yields segfault with ctypes hence use
            #      temporary file here (important for doctest)
            f = TemporaryFile()
        elif not is_stdout_redirected() and (not output or output is sys.stdout or output=='-'):
            f=sys.stdout
        elif isinstance(output,file):
            f=output
    try:
        yield f
    finally:
        if f is not sys.stdout and isinstance(output,str):
            f.close()


