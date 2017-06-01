#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import category
import parser

"""from pytest import *"""


def test_words():
    assert parser.words('Fido barks.') == ['fido', 'barks']


def test_parse():
    assert (parser.parse('Fido eats cheese.') ==
            [parser.Item(category.S, 'eats(fido)(cheese)')])
