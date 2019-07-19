#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import chartparser
from category import *
import catparser
import slash
import sys


def test_words():
    assert parser.words('Fido barks.') == ['fido', 'barks']


def test_parse():
    ans = parser.parse('Fido eats cheese')
    assert len(ans) == 1
    assert ans[0].cat == S
    assert str(ans[0].sem) == 'eats(cheese)(fido)'

    ans = parser.parse('will eat cheese')
    assert len(ans) == 1
    assert ans[0].cat == VBI
    assert str(ans[0].sem) == "λx.will(eat(x)(cheese))"


def test_lexicon(filename):
    lexicon_data = open(filename).read().splitlines()
    lexicon, sentences = catparser.do_parses(lexicon_data)

    mv = Metavar("X")
    AND_MODE = slash.PHI   # APPLYONLY
    cat = SlashCategory(
        SlashCategory(mv, slash.mk_lslash(AND_MODE), mv),
        slash.mk_rslash(AND_MODE),
        mv)
    lexicon['and'].append((cat,
                           semantics.Lam(
                               "x",
                               semantics.Lam(
                                   "y",
                                   semantics.App(
                                       semantics.App(
                                           semantics.Const("and"),
                                           semantics.BoundVar(0)),
                                       semantics.BoundVar(1))))))
    for (label, sentence, category, expected_count) in sentences:
        chartparser.p(label, sentence, lexicon, category, expected_count)


if __name__ == '__main__':
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
