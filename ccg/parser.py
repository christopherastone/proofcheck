#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import re

import category
import semantics as sem
import rules
from item import Item

NP = category.NP
S = category.S
VBI = category.VBI
VBT = category.VBT
MODAL = category.MODAL


def words(s: str):
    """Strips the punctuation and just returns the words"""
    return re.sub(r'[^A-za-z]', ' ', s).lower().split()


def pn(wd):
    """Creates a NP entry for the lexicon, with the given name"""
    return Item(NP, sem.Const(wd), wd)


def intrans(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name"""
    return Item(VBI, sem.Const(vb), vb)


def trans(vb):
    """Creates a transitive-verb entry the lexicon, with the given name"""
    return Item(VBT,
                sem.Lam(sem.gensym("y"),
                        sem.Lam(sem.gensym("x"),
                                sem.App(sem.App(sem.Const(vb),
                                                sem.BoundVar(0)),
                                        sem.BoundVar(1)))),
                vb)


def modal(wd):
    return Item(MODAL,
                sem.Lam(sem.gensym("f"),
                        sem.Lam(sem.gensym("x"),
                                sem.App(sem.Const(wd),
                                        sem.App(sem.BoundVar(1),
                                                sem.BoundVar(0))))),
                wd)


LEXICON = {'fido': [pn('fido')],
           'cheese': [pn('cheese')],
           'barks': [intrans('barks')],
           'eats': [intrans('eats'), trans('eats')],
           'eat': [intrans('eat'), trans('eat')],
           'sees': [trans('sees')],
           'see': [trans('see')],
           'brazil': [pn('brazil')],
           'defeated': [trans('defeated')],
           'germany': [pn('germany')],
           'will': [modal('will')]}   # baldridge p. 24-25


def mkChart(wds):
    """Creates an initial chart for the given words, with just the
    lexicon information for each word/leaf"""
    chart = {}
    for i in range(len(wds)):
        # We clone the lexicon list because unary promotion rules can
        # add new items to single-word lists, but we don't want to
        # permanently change the static dictionary.
        chart[(i, i)] = LEXICON[wds[i]][:]
    return chart


def fillCell(chart, i, j, rules=rules.parsingRules):
    if (i, j) not in chart:
        chart[(i, j)] = []
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (1)')
    for d in range(j-i):
        # print(f'combining ({i},{i+d}) with ({i+d+1},{j})')
        cell1 = chart[(i, i + d)]
        cell2 = chart[(i + d + 1, j)]
        # print(f'cell1 = {cell1} and cell2 = {cell2}')
        for item1 in cell1:
            for item2 in cell2:
                # print(f'checking ({cat1},{sem1}) & ({cat2},{sem2})')
                for binaryRule in rules[1]:
                    binaryRule(item1, item2, chart[(i, j)])
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (2)')
    for item in chart[(i, j)][:]:
        for unaryRule in rules[0]:
            # print(f'considering {item} for unary rule {unaryRule}')
            unaryRule(item, chart[(i, j)])
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (3)')


def parse(sentence):
    wds = words(sentence)
    nwds = len(wds)
    chart = mkChart(wds)
    # print(f'starting chart = {chart}')
    for tot in range(0, nwds):
        for i in range(nwds-tot):
            j = i+tot
            fillCell(chart, i, j)
    # print(chart)
    return chart[(0, nwds-1)]


def p(sentence):
    items = parse(sentence)
    for item in items:
        print()
        item.display()
        print()

# p('fido barks')
# p('fido eats cheese')
# p('will eat')
# p('fido will eat cheese')
