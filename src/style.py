# -*- coding: utf-8 -*-
"""
    Custom Agda color scheme
    ~~~~~~
    Custom Agda color scheme by jonaprieto
    :license: MIT, see LICENSE for details.
"""

from pygments.style import Style
from pygments.token import Comment, Error, Generic, Literal
from pygments.token import Name,  Operator, Text, String, Keyword


class CustomAgdaStyle(Style):
    """
    Custom Agda color scheme.
    """

    default_style = ''

    background_color = '#f0f8ff'

    styles = {
        Comment:                        '#82827c',
        Comment.Multiline:              '#82827c',
        Comment.Preproc:                '#999999',
        Comment.Single:                 '#82827c',
        Comment.Special:                '#999999',

        Error:                          'bg:#e3d2d2 #a61717',

        Generic.Deleted:                'bg:#ffdddd #000000',
        Generic.Emph:                   'italic #000000',
        Generic.Error:                  '#aa0000',
        Generic.Heading:                '#999999',
        Generic.Inserted:               'bg:#ddffdd #000000',
        Generic.Output:                 '#888888',
        Generic.Prompt:                 '#555555',
        Generic.Strong:                 'bold',
        Generic.Subheading:             '#aaaaaa',
        Generic.Traceback:              '#aa0000',

        Keyword:                        'bold #6D508B',
        Keyword.Constant:               'bold #6D508B',
        Keyword.Declaration:            'bold #6D508B',
        Keyword.Namespace:              'bold #564ea3', # agda-metis
        Keyword.Pseudo:                 'bold #642969', # agda-prop
        Keyword.Reserved:               'bold #6D508B',
        Keyword.Type:                   'bold #574EA4',

        Literal.Number.Float:           '#009999',
        Literal.Number.Hex:             '#009999',
        Literal.Number.Integer.Long:    '#009999',
        Literal.Number.Integer:         '#009999',
        Literal.Number.Oct:             '#009999',
        Literal.Number:                 '#009999',
        Literal.String.Backtick:        '#d14',
        Literal.String.Char:            '#d14',
        Literal.String.Doc:             '#d14',
        Literal.String.Double:          '#d14',
        Literal.String.Escape:          '#d14',
        Literal.String.Heredoc:         '#d14',
        Literal.String.Interpol:        '#d14',
        Literal.String.Other:           '#d14',
        Literal.String.Regex:           '#009926',
        Literal.String.Single:          '#d14',
        Literal.String.Symbol:          '#990073',
        Literal.String:                 '#d14',

        Name.Attribute:                 '#008080',
        Name.Builtin.Pseudo:            '#999999',
        Name.Builtin:                   '#0086B3',
        Name.Class:                     'bold #445588',
        Name.Constant:                  '#008080',
        Name.Decorator:                 'bold #3c5d5d',
        Name.Entity:                    '#800080',
        Name.Exception:                 'bold #990000',
        Name.Function:                  'bold #6D508B',
        Name.Label:                     'bold #990000',
        Name.Namespace:                 '#555555',
        Name.Tag:                       '#000080',
        Name.Variable.Class:            '#008080',
        Name.Variable.Global:           '#008080',
        Name.Variable.Instance:         '#008080',
        Name.Variable:                  '#008080',

        Operator.Word:                  'bold #6D508B',
        Operator:                       'bold #6D508B',

        String:                         '#CD5555',
        String.Heredoc:                 '#1c7e71 italic',
        String.Other:                   '#cb6c20',
        String.Regex:                   '#1c7e71',
        String.Regex:                   '#B452CD',

        Text:                           'bold #000',
        Text.Whitespace:                '#bbbbbb',
    }
