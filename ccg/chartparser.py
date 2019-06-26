#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Created on Tue May 30 14:13:01 2017

@author: Chris Stone
"""

import re

from category import *
from item import Item
import pyrsistent
import semantics
import rules


# LEXICON CONSTRUCTION

def pn(wd, attr=pyrsistent.m()):
    """Creates a NP entry for the lexicon, with the given proper name
       and the semantics of a constant
    """
    return Item(mk_NP(attr), semantics.Const(wd), wd)


def intrans(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name
       and the semantics of a constant (or equivalently, λx. vb x )
    """
    return Item(VBI, semantics.Const(vb), vb)


def intrans3(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name
       and the semantics of a constant (or equivalently, λx. vb x )
    """
    return Item(VBI, semantics.Const(vb), vb)


def trans(vb):
    return Item(VBT, semantics.Const(vb), vb)


def trans3(vb):
    return Item(VBT, semantics.Const(vb), vb)


def modal(wd):
    """Creates a modal-verb entry in the lexicon, with the given name
       and the semantics λf. λx. wd(f x) """
    return Item(MODAL,
                semantics.Lam("f",
                              semantics.Lam("x",
                                            semantics.App(semantics.Const(wd),
                                                          semantics.App(semantics.BoundVar(1),
                                                                        semantics.BoundVar(0))))),
                wd)


def coord(wd, cat):
    return Item(mk_coord(cat),
                semantics.Lam("y",
                              semantics.Lam("x",
                                            semantics.App(semantics.App(semantics.Const(wd),
                                                                        semantics.BoundVar(0)),
                                                          semantics.BoundVar(1)))),
                wd)

################
# TEST LEXICON #
################


LEXICON = {'fido': [pn('fido', pyrsistent.m(num='sg'))],
           'cheese': [pn('cheese')],
           'geese': [Item(NPpl, semantics.Const('geese'), 'geese')],
           'barks': [intrans('barks')],
           'eats': [intrans3('eats'), trans3('eats')],
           'eat': [intrans('eat'), trans('eat')],
           'sees': [trans('sees')],
           'see': [trans('see')],
           'brazil': [pn('brazil')],
           'defeated': [trans('defeated')],
           'germany': [pn('germany')],
           'will': [modal('will')],   # baldridge p. 24-25
           'and': [coord('⊕', NP)],
           }


###########
# PARSING #
###########


def mkChart(wds, lexicon=LEXICON):
    """Creates an initial chart for the given list of words.
       It starts out near-empty, with just the
       lexicon information for each word/leaf."""
    chart = {}
    for i in range(len(wds)):
        # We clone the lexicon list because unary promotion rules can
        # add new items to single-word lists, but we don't want to
        # permanently change the static dictionary.
        word = wds[i]
        chart[(i, i)] = \
            [Item(SingletonCategory(word), semantics.Const('_'), word)]
        for info in lexicon[wds[i]]:
            if isinstance(info, Item):
                chart[(i, i)].append(info)
            else:
                cat, sem = info
                sem = sem if sem else semantics.Const(word)
                chart[(i, i)].append(Item(cat, sem, word))
    return chart


def fillCell(chart, i, j, rules=rules.parsingRules):
    """Update the chart to fill in cell (i,j), which covers
       the i-th word to the j-th word, INCLUSIVE. It works by
       applying all the binary rules to all possible ways to
       partition the range into two nonempty sub-segments,
       and then applies all the unary rules to the results."""
    if (i, j) not in chart:
        chart[(i, j)] = []
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (1)')
    for d in range(j-i):
        # print(f'combining ({i},{i+d}) with ({i+d+1},{j})')
        cell1 = chart[(i, i + d)]      # parse of the first d words of segment
        cell2 = chart[(i + d + 1, j)]  # parse of the remaining words
        # print(f'cell1 = {cell1} and cell2 = {cell2}')
        for item1 in cell1:
            for item2 in cell2:
                # print(f'checking ({cat1},{sem1}) & ({cat2},{sem2})')
                # Apply all the binary rules to the partial parses
                for binaryRule in rules[1]:
                    binaryRule(item1, item2, chart[(i, j)])
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (2)')
    # Iterate over a copy of the cell that we're adding to, so we don't
    # apply unary rules to unary-rule-results. [Is this ever a problem?]
    for item in chart[(i, j)][:]:
        for unaryRule in rules[0]:
            # print(f'considering {item} for unary rule {unaryRule}')
            unaryRule(item, chart[(i, j)])
    # print(f'chart[({i},{j})] = {[str(i) for i in chart[(i,j)]]} (3)')


def words(s: str):
    """Strip ALL punctuation and just returns the (lowercased) words
       as a list"""
    return re.sub(r'[^A-za-z]', ' ', s).lower().split()


def parse(sentence, lexicon=LEXICON):
    """parse the given string and return all complete parses"""
    wds = words(sentence)
    nwds = len(wds)
    chart = mkChart(wds, lexicon)
    # print(f'starting chart = {chart}')
    for tot in range(0, nwds):
        for i in range(nwds-tot):
            j = i+tot
            fillCell(chart, i, j)
    # print(chart)
    return chart[(0, nwds-1)]


def p(sentence, lexicon=LEXICON):
    """parse the given string, and pretty-print all complete parses"""
    items = parse(sentence, lexicon)
    for item in items:
        print()
        item.display()
        print()


def dump(sentence, lexicon=LEXICON):
    """parse the given string and return all complete parses"""
    wds = words(sentence)
    nwds = len(wds)
    chart = mkChart(wds, lexicon)
    # print(f'starting chart = {chart}')
    for tot in range(0, nwds):
        for i in range(nwds-tot):
            j = i+tot
            fillCell(chart, i, j)
    for i in chart.keys():
        print("# ", i)
        for item in chart[i]:
            item.display()
            print()
        print()


if __name__ == '__main__':
    dump('fido barks')
    # p('fido barks')
    # p('fido eats cheese')
    # p('will eat')
    # p('fido will eat cheese')
    # p('xxx barks')
