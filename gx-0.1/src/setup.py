#!/usr/bin/env python

import os
import sys
from distutils.core import setup, Extension
from Cython.Build import cythonize

long_description="""\
    This package contains EXPERIMENTAL WORK IN PROGRESS STUFF...
"""

if not 'SAGE_SRC' in os.environ:
    import sage.env
    SAGE_SRC = sage.env.SAGE_SRC
else:
    SAGE_SRC = os.environ['SAGE_SRC']

extensions = [ Extension('gx', ['gx.pyx'], libraries = ['gmp'] ),
           #Extension('transversal_basis_matroid', ['transversal_basis_matroid.pyx'], libraries = ['gmp'] )
           ]

setup(
    ext_package='',
    name='gx',
    version='0.1',
    description='A SAGEMATH package with my tools for investigating gammoids and transversal matroids & stuff.',
    long_description=long_description,
    author='Immanuel Albrecht',
    license='GPLv3',

    ext_modules = cythonize(extensions, include_path = [ SAGE_SRC ])
)
