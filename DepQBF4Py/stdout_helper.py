#from __future__ import print_function
from os import pipe,dup,dup2,read
from select import select
from contextlib import contextmanager
import sys
from ctypes import CDLL

def is_stdout_redirected(stdout=sys.stdout):
    return stdout != sys.stdout

def read_stdout(pipe_out):
    out = ''
    #while there is still stuff in pipe_out
    while select([pipe_out], [], [], 0)[0]:
        out += read(pipe_out, 1024)
    return out

@contextmanager
def delayed_stdout():
    if is_stdout_redirected():
        #Note: we need a delayed output, e.g., first redirecting
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
        #Note: we need a delayed output, e.g., first redirecting
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
