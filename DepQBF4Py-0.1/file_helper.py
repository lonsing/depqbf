from ctypes import *
from contextlib import contextmanager
from tempfile import TemporaryFile
from os import fdopen
import sys

class FILE(Structure):
    pass

FILE_P=POINTER(FILE)

#doctest._SpoofOut
def is_stdout_redirected(stdout=sys.stdout):
    return stdout != sys.stdout


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
