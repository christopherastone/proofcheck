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
VBI = category.SlashCategory(category.LEFT, S, NP)
VBT = category.SlashCategory(category.RIGHT, VBI, NP)


def words(s: str):
    """Strips the punctuation and just returns the words"""
    return re.sub(r'[^A-za-z]', ' ', s).lower().split()


class Item:
    def __init__(self, cat, sem, why=None):
        self.cat = cat
        self.sem = sem
        self.why = why

    def __str__(self):
        semString = self.sem if isinstance(self.sem, str) else "LAM"
        return f'({self.cat},{semString})'

    def __repr__(self):
        return f'Item({self.cat!r},{self.sem!r},{self.why!r})'

    def __eq__(self, other):
        """ignores the why argument, and checks sem for pointer equality"""
        return self.cat == other.cat and self.sem == other.sem


def pn(n):
    """Creates a NP entry for the lexicon, with the given name"""
    return Item(NP, n)


def intrans(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name"""
    return Item(VBI, lambda x: vb + '(' + x + ')')


def trans(vb):
    """Creates a transitive-verb entry the lexicon, with the given name"""
    return Item(VBT, lambda y: lambda x: vb + '(' + x + "," + y + ')')


LEXICON = {'fido': [pn('fido')],
           'cheese': [pn('cheese')],
           'barks': [intrans('barks')],
           'eats': [intrans('eats'), trans('eats')]}


def mkChart(wds):
    """Creates an initial chart for the given words, with just the
    lexicon information for each word/leaf"""
    chart = {}
    for i in range(len(wds)):
        chart[(i, i)] = LEXICON[wds[i]]
    return chart


def fillCell(chart, i, j):
    chart[(i, j)] = []
    # print("chart(",i,',',j,') = ',chart[(i,j)])
    for d in range(j-i):
        # print(f'combining ({i},{i+d}) with ({i+d+1},{j})')
        cell1 = chart[(i, i + d)]
        cell2 = chart[(i + d + 1, j)]
        # print(f'cell1 = {cell1} and cell2 = {cell2}')
        for item1 in cell1:
            cat1 = item1.cat
            sem1 = item1.sem
            for item2 in cell2:
                cat2 = item2.cat
                sem2 = item2.sem
                # print(f'checking ({cat1},{sem1}) & ({cat2},{sem2})')
                if (cat1.slash == category.RIGHT and cat1.dom == cat2):
                    chart[(i, j)] += [Item(cat1.cod, sem1(sem2))]
                elif (cat2.slash == category.LEFT and cat2.dom == cat1):
                    chart[(i, j)] += [Item(cat2.cod, sem2(sem1))]
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
