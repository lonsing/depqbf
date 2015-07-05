import os, sys, select

# the pipe would fail for some reason if I didn't write to stdout at some point
# so I write a space, then backspace (will show as empty in a normal terminal)
sys.stdout.write(' \b')
pipe_out, pipe_in = os.pipe()
# save a copy of stdout
stdout = os.dup(1)
# replace stdout with our write pipe
os.dup2(pipe_in, 1)

# check if we have more to read from the pipe
def more_data():
        r, _, _ = select.select([pipe_out], [], [], 0)
        return bool(r)

# read the whole pipe
def read_pipe():
        out = ''
        while more_data():
                out += os.read(pipe_out, 1024)

        return out

# testing print methods
import ctypes
libc = ctypes.CDLL(None)

print 'This text gets captured by myStdOut'
libc.printf('This text fails to be captured by myStdOut\n')

# put stdout back in place 
os.dup2(stdout, 1)
print 'Contents of our stdout pipe:'
print read_pipe()
