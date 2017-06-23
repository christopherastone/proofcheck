"""
Created on Tue May 30 14:48:25 2017

@author: stone
"""

import pyrsistent


class Metavar:
    def __init__(self, hint: str):
        self.__hint = hint

    def __str__(self):
        return str(f'M[{self.__hint}{id(self)}]')

    def subst(self, sub):
        if self in sub:
            return sub[self]
        else:
            return self

    def unify(self, other, sub=pyrsistent.m()):
        if self in sub:
            return sub[self].unify(other, sub)
        else:
            # TODO: Implement an occurs check, to be safe?
            upd = {self: other}
            # replace all uses of this metavariable in the definition of other
            #   metavariables, and then add the definition of this metavariable
            #   to the resulting substitution.
            return sub.transform([pyrsistent.ny],  # apply to all keys
                                 lambda c: c.subst(upd)).update(upd)


class BaseCategory:
    """An atomic grammatical category, such as NP"""
    def __init__(self, nm: str):
        self.__name = nm

    def __str__(self):
        return self.__name

    def __repr__(self):
        return f'BaseCategory({self.__name!r})'

    def __eq__(self, other):
        return ((isinstance(other, BaseCategory) and
                 self.__name == other.__name))

    @property
    def dom(self):
        return None

    @property
    def cod(self):
        return None

    @property
    def slash(self):
        return None

    def subst(self, sub):
        return self

    def unify(self, other, sub=pyrsistent.m()):
        if isinstance(other, Metavar):
            return other.unify(self, sub)
        elif self == other:
            return sub
        else:
            return None


class SlashCategory:
    """A complex grammatical category, with a given codomain, domain,
       and slash type"""
    def __init__(self, slash, cod, dom, restr=None):
        self.__slash = slash
        self.__cod = cod
        self.__dom = dom
        self.__restr = {} if restr is None else restr

    def __eq__(self, other):
        return (isinstance(other, SlashCategory) and
                (self.__slash == other.__slash) and
                (self.__cod == other.__cod) and
                (self.__restr == other.__restr))

    def __repr__(self):
        return (f'SlashCategory({self.__slash!r},{self.__cod!r},' +
                f'{self.__dom!r}' +
                ("" if self.__restr == {} else f',{self.__restr}') +
                f')')

    def __str__(self):
        return f'({self.__cod}{self.__slash}{self.__dom})'

    @property
    def dom(self):
        return self.__dom

    @property
    def cod(self):
        return self.__cod

    @property
    def slash(self):
        return self.__slash

    def subst(self, sub):
        cod = self.__cod.subst(sub)
        dom = self.__dom.subst(sub)
        if ((cod is self.__cod) and (dom is self.__dom)):
            return self
        else:
            return SlashCategory(self.__slash, cod, dom, self.__restr)

    def unify(self, other, sub=pyrsistent.m()):
        if (isinstance(other, Metavar)):
            return other.unify(self, sub)
        elif (isinstance(other, SlashCategory) and
                self.__slash == other.__slash):
            # Try to unify the subexpressions
            sub1 = self.__cod.unify(other.__cod, sub)
            if sub1 is None:
                return None
            sub2 = self.__dom.unify(other.__dom, sub1)
            return sub2
        else:
            return None


########################
# SLASH-TYPE CONSTANTS #
########################

LEFT = '\\'
RIGHT = '/'


def invert(dir):
    """return the opposite of the given direction"""
    if dir == LEFT:
        return RIGHT
    if dir == RIGHT:
        return LEFT
    raise ValueError(f'bad direction {dir}')


############################
# USEFUL COMMON CATEGORIES #
############################

NP = BaseCategory("NP")                   # noun phrase
S = BaseCategory("S")                     # sentence
PP = BaseCategory("PP")                   # prepositional phrase
VBI = SlashCategory(LEFT, S, NP)          # intransitive verb, S\NP
VBT = SlashCategory(RIGHT, VBI, NP)       # transitive verb, (S\NP)/NP
MODAL = SlashCategory(RIGHT, VBI, VBI)    # modal verb, (S\NP)/(S\NP)


#####################
# Simple unit tests #
#####################

def test_eq():
    assert VBI != VBT
    assert VBI == SlashCategory(LEFT, S, NP)
    assert SlashCategory(LEFT, S, NP) == VBI
    assert MODAL.dom == MODAL.cod


def test_subst():
    m1 = Metavar("m1")
    m2 = Metavar("m2")

    cat1 = SlashCategory(RIGHT, m1, VBI)
    cat2 = SlashCategory(RIGHT, VBI, VBI)
    cat3 = SlashCategory(LEFT, VBI, VBI)
    assert cat1 != cat2
    assert cat2 != cat3

    assert cat1.subst({m1: VBI}) == cat2
    assert cat1.subst({m1: NP}) != cat2
    assert cat1.subst({m1: VBI}) != cat3
    assert cat2.subst({m1: VBI}) is cat2


def test_unify():
    m1 = Metavar("m1")
    m2 = Metavar("m2")

    cat1 = SlashCategory(RIGHT, m1, VBI)
    cat2 = SlashCategory(RIGHT, VBI, VBI)
    cat3 = SlashCategory(RIGHT, VBI, VBT)
    cat4 = SlashCategory(RIGHT, m2, m2)

    assert cat1.unify(cat2) is not None
    assert cat1.unify(cat3) is None
    assert cat1.unify(cat4) is not None
    assert cat2.unify(cat3) is None
    assert cat2.unify(cat4) is not None
    assert cat3.unify(cat4) is None

    assert cat1.unify(cat4, cat2.unify(cat4)) is not None
    assert cat2.unify(cat1, cat1.unify(cat4))[m1] == VBI
    assert cat2.unify(cat1, cat1.unify(cat4))[m2] == VBI
