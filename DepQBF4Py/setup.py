#!/usr/bin/env python
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
from setuptools import setup, find_packages, Command
from setuptools.dist import Distribution
# To use a consistent encoding
from codecs import open
from fileinput import input as file_input
from glob import glob
from distutils import log
from distutils.command.build_clib import build_clib
import distutils.command.build
# required for unittest and clib execution
import multiprocessing
from shutil import copy
from subprocess import check_call
from os import path
import yaml

here = path.abspath(path.dirname(__file__))
# Get the long description from the relevant file
with open(path.join(here, 'DESCRIPTION.rst'), encoding='utf-8') as f:
    long_description = f.read()


def get_lib_build_path():
    b = distutils.command.build.build(Distribution())
    b.initialize_options()
    b.finalize_options()
    return b.build_purelib


class BuildClib(build_clib):
    without_stats = False
    config_file = '../qdpll_config.h'
    python_config_file = 'DepQBF/config.yaml'

    user_options = [
        ('without-stats', None, 'Build the shared library without statistics support'),
    ]

    def set_option(self, option, value):
        # search first, so that we do not screw autorebuild of make
        update = True
        search_for = '#define %s %s' % (option, value)
        with open(self.config_file, 'r') as f:
            if f.read().find(search_for) > 0:
                update = False
        if update:
            for line in file_input(self.config_file, inplace=True):
                if ' %s ' % option in line:
                    line = line[:-1]
                    line = line.split(' ')
                    line[2] = value
                    print(' '.join(line))
                else:
                    print(line),

        # update property in python config file
        config = yaml.load(file(self.python_config_file))
        if not config:
            config = {}
        config[option] = bool(int(value))
        with open(self.python_config_file, 'w') as outfile:
            outfile.write(yaml.dump(config, default_flow_style=True))

    def build_libraries(self, libraries):
        if self.without_stats:
            log.info('Turning statistics off in file "%s"', self.config_file)
            self.set_option('COMPUTE_STATS', '0')
            self.set_option('COMPUTE_TIMES', '0')
        else:
            log.info('Turning statistics on in file "%s"', self.config_file)
            self.set_option('COMPUTE_STATS', '1')
            self.set_option('COMPUTE_TIMES', '1')

        for (lib_name, build_info) in libraries:
            log.info('building external c library "%s" from source', lib_name)
            log.info('*' * 80)
            log.info('Running make on path "%s"', build_info['path'])
            # Run make install.
            check_call(['make'], cwd=path.realpath(build_info['path']))
            log.info('*' * 80)

            generated_libs = glob('../libqdpll.so*')
            assert (sum(1 for _ in generated_libs) == 1)
            lib = generated_libs[0]

            log.info('copying %s to %s', lib, build_info['dest'])
            self.mkpath(build_info['dest'])
            copy(lib, build_info['dest'])


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
    cmdclass={'build_clib': BuildClib},
    libraries=[('qdpll', {'sources': [], 'path': '..', 'dest': get_lib_build_path()})],

    # https://packaging.python.org/en/latest/requirements.html
    install_requires=['memory_profiler'],

    # List additional groups of dependencies here (e.g. development
    # dependencies). You can install these using the following syntax,
    # for example:
    # $ pip install -e .[dev,test]
    extras_require={
        'dev': ['check-manifest', 'memory_profiler'],
        'test': ['coverage', 'memory_profiler'],
    },
    include_package_data=True,
    test_suite='tests'
)
