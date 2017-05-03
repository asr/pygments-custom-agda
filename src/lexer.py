# -*- coding: utf-8 -*-
"""
    Agda lexer
    ~~~~~~~~~~~
    Pygments lexer for Agda + Custom Keywords
    :copyright: Copyright 2017 Jonathan Prieto-Cubides
    :license: MIT, see LICENSE for details.
"""

import re

from pygments.lexer          import Lexer, RegexLexer, bygroups, do_insertions
from pygments.lexers.haskell import HaskellLexer

from pygments.token          import String, Number, Punctuation, Generic
from pygments.token          import Text, Comment, Operator, Name, Keyword

line_re = re.compile('.*?\n')

class CustomAgdaLexer(RegexLexer):
    name      = 'CustomAgda'
    aliases   = ['cagda']
    filenames = ['*.agda'] # just to have one if you whant to use
    mimetypes = ['text/x-agda']


    reserved = ['abstract', 'codata', 'coinductive', 'constructor', 'data',
                'field', 'forall', 'hiding', 'in', 'inductive', 'infix',
                'infixl', 'infixr', 'instance', 'let', 'mutual', 'open',
                'pattern', 'postulate', 'primitive', 'private',
                'quote', 'quoteGoal', 'quoteTerm',
                'record', 'renaming', 'rewrite', 'syntax', 'tactic',
                'unquote', 'unquoteDecl', 'using', 'where', 'with']

    tokens = {
        'root': [
            # Declaration
            (r'^(\s*)([^\s(){}]+)(\s*)(:)(\s*)',
             bygroups(Text, Name.Function, Text, Operator.Word, Text)),
            # Comments
            (r'--(?![!#$%&*+./<=>?@^|_~:\\]).*?$', Comment.Single),
            (r'\{-', Comment.Multiline, 'comment'),
            # Holes
            (r'\{!', Comment.Directive, 'hole'),
            # Lexemes:
            #  Identifiers
            (r'\b(%s)(?!\')\b' % '|'.join(reserved), Keyword.Reserved),
            (r'(import|module)(\s+)', bygroups(Keyword.Reserved, Text), 'module'),
            (r'\b(Set|Prop|[A-Z]\w+)\b', Keyword.Type),
            #  Special Symbols
            (r'(\(|\)|\{|\})', Operator),
            (u'(\\.{1,3}|\\||\u039B|\u2200|\u2192|:|=|->)', Operator.Word),
            #  Numbers
            (r'\d+[eE][+-]?\d+', Number.Float),
            (r'\d+\.\d+([eE][+-]?\d+)?', Number.Float),
            (r'0[xX][\da-fA-F]+', Number.Hex),
            (r'\d+', Number.Integer),
            # Strings
            (r"'", String.Char, 'character'),
            (r'"', String, 'string'),
            (r'[^\s(){}]+', Text),
            (r'\s+?', Text),  # Whitespace
        ],
        'hole': [
            # Holes
            (r'[^!{}]+', Comment.Directive),
            (r'\{!', Comment.Directive, '#push'),
            (r'!\}', Comment.Directive, '#pop'),
            (r'[!{}]', Comment.Directive),
        ],
        'module': [
            (r'\{-', Comment.Multiline, 'comment'),
            (r'[a-zA-Z][\w.]*', Name, '#pop'),
            (r'[\W0-9_]+', Text)
        ],
        'comment'  : HaskellLexer.tokens['comment'],
        'character': HaskellLexer.tokens['character'],
        'string'   : HaskellLexer.tokens['string'],
        'escape'   : HaskellLexer.tokens['escape']
    }

    agdaMetis = [ 'atp-canonicalize'
                , 'atp-clausify'
                , 'atp-conjunct'
                , 'atp-conjunct'
                , 'atp-negate'
                , 'atp-resolve'
                , 'atp-simplify'
                , 'atp-splitGoal'
                , 'atp-strip'
                ]

    agdaProp = [  'eq'
                , 'assoc'
                , 'assume'
                , 'axiom'
                , 'bicon'
                , 'comm'
                , 'dist'
                , 'dmorgan'
                , 'e245b'
                , 'elim'
                , 'equiv'
                , 'ext'
                , 'here'
                , 'injective'
                , 'inside'
                , 'intro'
                , 'lem1'
                , 'lem2'
                , 'proj'
                , 'resolve'
                , 'subst'
                , 'there'
                , 'to'
                , 'trans'
                , 'vanDalen244a'
                , 'vanDalen244b'
                , 'vanDalen244c'
                , 'vanDalen244d'
                , 'vanDalen244e'
                , 'Var'
                , 'weaken'
                , 'nnf'
                , 'cnf'
                , 'dnf'
                ]


    def get_tokens_unprocessed(self, text):
        for index, token, wd in RegexLexer.get_tokens_unprocessed(self, text):
            if token is Text and any([ kw in wd for kw in self.agdaMetis ]):
                yield index, Keyword.Namespace, wd
            elif token is Text and any([ kw in wd for kw in self.agdaProp ]):
                yield index, Keyword.Pseudo, wd
            else:
                yield index, token, wd
