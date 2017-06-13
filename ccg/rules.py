"""
CCG Combinatory Rules
"""

import category
import semantics
from item import Item


def deconstruct(item1, item2):
    return (item1.cat, item1.sem, item2.cat, item2.sem)


normalize = True


def ForwardApplication(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)
    if (cat1.slash == category.RIGHT and cat1.dom == cat2 and
            # XXX: overly specific - won't extend to generalized composition
            (not normalize or (item1.why[0] != '>' and item1.why[0] != '>B'))):
        dest += [Item(cat1.cod,
                      semantics.App(sem1, sem2).reduce(),
                      ['>', item1, item2])]


def BackwardApplication(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)
    if (cat2.slash == category.LEFT and cat2.dom == cat1):
        dest += [Item(cat2.cod,
                      semantics.App(sem2, sem1).reduce(),
                      ['<', item1, item2])]


def HarmonicComposition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)
    if (cat1.slash == category.RIGHT and
        cat2.slash == category.RIGHT and
            cat1.dom == cat2.cod):
        dest += (
            [Item(category.SlashCategory(category.RIGHT,
                                         cat1.cod, cat2.dom),
                  semantics.Lam(
                      "z",
                      semantics.App(
                          sem1,
                          semantics.App(
                              sem2,
                              semantics.BoundVar(0))).reduce()),
                  ['>B', item1, item2])])


baldridgeRules = [[],
                  [ForwardApplication,
                   BackwardApplication,
                   HarmonicComposition]]
