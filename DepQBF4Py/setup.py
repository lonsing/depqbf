#
# DepQBF4Py setup script 
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
"""A setuptools based setup module.

See:
https://packaging.python.org/en/latest/distributing.html
https://github.com/pypa/sampleproject
"""

# Always prefer setuptools over distutils
from setuptools import setup, find_packages
# To use a consistent encoding
from codecs import open
from os import path
from distutils.command.build_clib import build_clib
from distutils.command.build_ext import build_ext
from distutils.command.install_lib import install_lib
from distutils import log

here = path.abspath(path.dirname(__file__))

# Get the long description from the relevant file
with open(path.join(here, 'DESCRIPTION.rst'), encoding='utf-8') as f:
    long_description = f.read()

from subprocess import check_output, CalledProcessError, check_call

import os
import glob
import shutil

class build_external_clib(build_clib):
    def build_libraries(self, libraries):
        for (lib_name, build_info) in libraries:
            log.info('building external c library "%s" from source',lib_name)
            build_temp=self.build_temp
            log.info('*'*80)
            log.info('Running make on path "%s"',build_info['path'])
            # Run make install.
            check_call(['make'], cwd=os.path.realpath(build_info['path']))
            log.info('*'*80)

            generated_libs = glob.glob('../libqdpll.so*')
            assert(sum(1 for _ in generated_libs) == 1)
            lib = generated_libs[0]
            
            log.info('copying %s to %s', lib, build_info['dest'])
            self.mkpath(build_info['dest'])
            shutil.copy(lib,build_info['dest'] ) #self.build_temp)

setup(
    name='DepQBF4Py',
    version='4.0.1',
    description='API to the QBF solver DepQBF (includes shared solver libs)',
    long_description=long_description,
    url='https://github.com/lonsing/depqbf',
    author='Johannes K. Fichte',
    author_email='fichte@kr.tuwien.ac.at',
    license='GPLv3',
    # See https://pypi.python.org/pypi?%3Aaction=list_classifiers
    classifiers=[
        # How mature is this project? Common values are
        #   3 - Alpha
        #   4 - Beta
        #   5 - Production/Stable
        'Development Status :: 3 - Alpha',
        'Environment :: Console',
        'Intended Audience :: Developers',
        'Intended Audience :: Science/Research',
        'Topic :: Scientific/Engineering',
        'Topic :: Scientific/Engineering :: Artificial Intelligence',
        'Topic :: Scientific/Engineering :: Mathematics',
        'Topic :: Software Development :: Libraries :: Python Modules',
        'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',
        'Operating System :: MacOS',
        'Operating System :: POSIX :: Linux',
        'Programming Language :: Python :: 2.7',
    ],
    keywords='QBF SAT satisfiabily solving',
    packages=find_packages(exclude=['contrib', 'docs', 'tests*']),
    cmdclass = {'build_clib': build_external_clib},
    libraries= [('qdpll',{'sources':[], 'path': '..', 'dest': 'build/lib/DepQBF'})],
    # List run-time dependencies here.  These will be installed by pip when
    # your project is installed. For an analysis of "install_requires" vs pip's
    # requirements files see:
    # https://packaging.python.org/en/latest/requirements.html
    #install_requires=['ctypes'],

    # List additional groups of dependencies here (e.g. development
    # dependencies). You can install these using the following syntax,
    # for example:
    # $ pip install -e .[dev,test]
    extras_require={
        'dev': ['check-manifest'],
        'test': ['coverage','memory_profiler'],
    },
    include_package_data = True,
)

# # Mac OS X depedencies
# if platform.system() == 'Darwin':
#     extra_link_args = ["-framework", "CoreFoundation", 
#                        "-framework", "AudioToolbox"]
#     version = platform.mac_ver()[0].split(".")    
#     # OS X Lion (10.7.x) or above support
#     if version[0] == '10' and int(version[1]) >= 7:
#         extra_link_args += ["-framework", "AudioUnit"]
# else:
#     extra_link_args = []



