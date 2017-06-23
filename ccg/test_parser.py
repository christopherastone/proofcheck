#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import category
import parser


def test_words():
    assert parser.words('Fido barks.') == ['fido', 'barks']


def test_parse():
    ans = parser.parse('Fido eats cheese')
    assert len(ans) == 1
    assert ans[0].cat == category.S
    assert str(ans[0].sem) == 'eats(fido)(cheese)'

    ans = parser.parse('will eat cheese')
    assert len(ans) == 1
    assert ans[0].cat == category.VBI
    assert str(ans[0].sem) == "λx.will(eat(x)(cheese))"
