#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import category
import chartparser
import catparser


def test_words():
    assert parser.words('Fido barks.') == ['fido', 'barks']


def test_parse():
    ans = parser.parse('Fido eats cheese')
    assert len(ans) == 1
    assert ans[0].cat == category.S
    assert str(ans[0].sem) == 'eats(cheese)(fido)'

    ans = parser.parse('will eat cheese')
    assert len(ans) == 1
    assert ans[0].cat == category.VBI
    assert str(ans[0].sem) == "λx.will(eat(x)(cheese))"


def test_lexicon():
    lexicon_data = open('lexicon.txt').read()
    lexicon = catparser.do_parse(lexicon_data)
    chartparser.p('fido will eat cheese', lexicon)
    chartparser.p('bob defeated alice', lexicon)
    chartparser.dump('alice sat bob down', lexicon)


if __name__ == '__main__':
    test_lexicon()
