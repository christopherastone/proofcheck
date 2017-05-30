#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:13:01 2017

@author: stone
"""

import re

import category

NP = category.NP
S = category.S
VBI = category.mkL(S, NP)
VBT = category.mkR(VBI, NP)


def words(s: str):
    """Strips the punctuation and just returns the words"""
    return re.sub(r'[^A-za-z]', ' ', s).lower().split()


def pn(n):
    """Creates a NP entry for the lexicon, with the given name"""
    return (NP, n)


def intrans(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name"""
    return (VBI, lambda x: vb + '(' + x + ')')


def trans(vb):
    """Creates a transitive-verb entry the lexicon, with the given name"""
    return (VBT, lambda y: lambda x: vb + '(' + x + "," + y + ')')


LEXICON = {'fido': [pn('fido')],
           'cheese': [pn('cheese')],
           'barks': [intrans('barks')],
           'eats': [intrans('eats'), trans('eats')]}


def mkChart(wds):
    chart = {}
    for i in range(len(wds)):
        chart[(i, i)] = LEXICON[wds[i]]
    return chart


def fillCell(chart, i, j):
    chart[(i, j)] = []
    # print("chart(",i,',',j,') = ',chart[(i,j)])
    for d in range(j-i):
        # print(i,",",i+d,"...",i+d+1,",",j)
        cell1 = chart[(i, i + d)]
        cell2 = chart[(i + d + 1, j)]
        # print(i, d, cell1, cell2)
        for cat1, sem1 in cell1:
            for cat2, sem2 in cell2:
                # print("checking", cat1, cat2)
                if (category.isR(cat1) and category.dom(cat1) == cat2):
                    chart[(i, j)] += [(category.cod(cat1), sem1(sem2))]
                elif (category.isL(cat2) and category.dom(cat2) == cat1):
                    chart[(i, j)] += [(category.cod(cat2), sem2(sem1))]
    # print("chart(",i,',',j,') = ',chart[(i,j)])


def parse(sentence):
    wds = words(sentence)
    nwds = len(wds)
    chart = mkChart(wds)
    for tot in range(1, nwds):
        for i in range(nwds-tot):
            j = i+tot
            fillCell(chart, i, j)
    return chart[(0, nwds-1)]
