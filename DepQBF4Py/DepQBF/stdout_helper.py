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

from ctypes import CDLL
from contextlib import contextmanager
from os import pipe, dup, dup2, read
from select import select
import sys


def is_stdout_redirected(stdout=sys.stdout):
    return stdout != sys.stdout


def read_stdout(pipe_out):
    out = ''
    # while there is still stuff in pipe_out
    while select([pipe_out], [], [], 0)[0]:
        out += read(pipe_out, 1024)
    return out


@contextmanager
def delayed_stdout():
    if is_stdout_redirected():
        # Note: we need a delayed output, e.g., first redirecting
        #      output to pipe and then printing otherwise doctest does
        #      not receive the stdout. Futher, we need to print
        #      something to c-stdout before redirecting; not clear
        #      why; bug?
        libc = CDLL(None)
        libc.printf('')
        pipe_out, pipe_in = pipe()
        stdout = dup(1)
        dup2(pipe_in, 1)
    try:
        yield
    finally:
        if is_stdout_redirected():
            dup2(stdout, 1)
            print(read_stdout(pipe_out)),


@contextmanager
def delayed_stderr():
    if is_stdout_redirected():
        # Note: we need a delayed output, e.g., first redirecting
        #      output to pipe and then printing otherwise doctest does
        #      not receive the stdout. Futher, we need to print
        #      something to c-stdout before redirecting; not clear
        #      why; bug?
        libc = CDLL(None)
        libc.printf('')
        pipe_out, pipe_in = pipe()
        stderr = dup(2)
        dup2(pipe_in, 2)
    try:
        yield
    finally:
        if is_stdout_redirected():
            dup2(stderr, 2)
            print(read_stdout(pipe_out)),
