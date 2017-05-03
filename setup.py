#!/usr/bin/python

from setuptools import setup, find_packages

setup(
      name="pygments-cagda"
    , version = "0.1"
    , description = "A custom pygments lexer and style for Agda."
    , long_description = open('README.md').read()
    , keywords = "pygments lexer style agda cagda custom"
    , license  = "MIT"
    , author = "Jonathan Prieto-Cubides"
    , author_email = "jprieto9@eafit.edu.co"
    , url = "http://github.com/jonaprieto/pygments-custom-agda"
    , packages = find_packages()
    , install_requires = ['pygments >= 1.4']
    , entry_points = '''[pygments.lexers]
                        cagda=src.lexer:CustomAgdaLexer

                        [pygments.styles]
                        cagda=src.style:CustomAgdaStyle'''
    , classifiers =
      [ 'Development Status :: 4 - Beta',
        'Environment :: Plugins',
        'Intended Audience :: Developers',
        'License :: OSI Approved :: BSD License',
        'Operating System :: OS Independent',
        'Programming Language :: Python',
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 3',
        'Topic :: Software Development :: Libraries :: Python Modules',
       ]
    )
