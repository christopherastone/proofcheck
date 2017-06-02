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
        print("cat:", str(self.cat), repr(self.cat))
        semString = Item.semToString(self.cat, self.sem)
        return f'({self.cat},{semString})'

    def __repr__(self):
        return f'Item({self.cat!r},{self.sem!r},{self.why!r})'

    def __eq__(self, other):
        """ignores the why argument, and checks sem for pointer equality"""
        return self.cat == other.cat and self.sem == other.sem

    @staticmethod
    def semToString(cat, sem, vars=['x', 'y', 'z', 'w', 'u', 'v'],
                    fns=['f', 'g', 'h', 'k']):
        # print(f'semToString:{cat}:{sem}')
        if isinstance(sem, str):
            return sem
        elif isinstance(cat, category.SlashCategory):
            # print(f'cat.dom={cat.dom}')
            if isinstance(cat.dom, category.SlashCategory):
                return ('λ' + fns[0] + '.' +
                        Item.semToString(cat.cod,
                                         sem(Item.varToSem(fns[0], cat.dom)),
                                         vars, fns[1:]))
            else:
                return ('λ' + vars[0] + '.' +
                        Item.semToString(cat.cod, sem(vars[0]), vars[1:], fns))
        else:
            return f'<BAD SEMANTICS:{cat}:{sem}>'

    @staticmethod
    def varToSem(x, cat):
        """eta-expand the given semantics for the given category"""
        if isinstance(cat, category.SlashCategory):
            return lambda y: Item.varToSem(x + "(" + y + ")", cat.cod)
        else:
            return x

    def toStrings(self):
        if isinstance(self.why, str):
            lines = [self.why]
        elif isinstance(self.why, list):
            reason = self.why[0]
            extra = 1+len(reason)
            leftLines = self.why[1].toStrings()
            rightLines = self.why[2].toStrings() if len(self.why) >= 2 else []
            lines = Item.mergeLines(leftLines, rightLines, extra)
            lines += ['-' * (len(lines[0])-extra) + ' ' + reason]
        else:
            lines = ["???"]
        lines += [str(self.cat)]
        lines += [Item.semToString(self.cat, self.sem)]
        return Item.centerlines(lines)

    @staticmethod
    def centerlines(lines):
        width = max(len(l) for l in lines)
        return [' ' * ((width-len(l)) // 2) + l + ' ' * ((width+1-len(l)) // 2)
                for l in lines]

    @staticmethod
    def mergeLines(lines1, lines2, extra=0):
        len1 = len(lines1)
        wid1 = len(lines1[0])
        len2 = len(lines2)
        wid2 = len(lines2[0])
        minlen = min(len1, len2)
        rmargin = ' ' * extra
        part1 = [lines1[i] + '  ' + lines2[i] + rmargin
                 for i in range(minlen)]
        part2 = [' ' * (wid1+2) + lines2[i] + rmargin
                 for i in range(minlen, len2)]
        part3 = [lines1[i] + '  ' * (wid2+2) + rmargin
                 for i in range(minlen, len1)]
        return part1 + part2 + part3

    def display(self):
        for l in self.toStrings():
            print(l)


def mk(cat, wd):
    return Item(cat, Item.varToSem(wd, cat), wd)


def pn(n):
    """Creates a NP entry for the lexicon, with the given name"""
    return mk(NP, n)


def intrans(vb):
    """Creates an intransitive-verb entry the lexicon, with the given name"""
    return mk(VBI, vb)


def trans(vb):
    """Creates a transitive-verb entry the lexicon, with the given name"""
    return Item(VBT, lambda y: lambda x: vb + '(' + x + ')(' + y + ')', vb)


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
                    chart[(i, j)] += [Item(cat1.cod, sem1(sem2),
                                           ['>', item1, item2])]
                elif (cat2.slash == category.LEFT and cat2.dom == cat1):
                    chart[(i, j)] += [Item(cat2.cod, sem2(sem1),
                                           ['<', item1, item2])]
    # print("chart(",i,',',j,') = ',chart[(i,j)])


def parse(sentence):
    wds = words(sentence)
    nwds = len(wds)
    chart = mkChart(wds)
    for tot in range(1, nwds):
        for i in range(nwds-tot):
            j = i+tot
            fillCell(chart, i, j)
    # print(chart)
    return chart[(0, nwds-1)]


def p(sentence):
    items = parse(sentence)
    for item in items:
        item.display()
        print()
