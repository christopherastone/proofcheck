"""
CCG Categories.
"""

import pyrsistent
import slash as s
import semantic_types as sem


class BaseCategory:
    """An atomic grammatical category, such as NP,
       with optional fixed attributes"""

    def __init__(self, cat, semty, attrs=pyrsistent.m()):
        self.__cat = cat
        self.__attrs = attrs
        self.__semty = semty

    def __str__(self):
        suffix = \
            '[' + ', '.join(self.__attrs.values()) + ']' if self.attrs else ''
        return self.cat + suffix

    def __repr__(self):
        if self.__attrs:
            return \
                (f'BaseCategory({self.__cat!r},{self.__semty!r},'
                 f'{self.__attrs!r})')
        else:
            return f'BaseCategory({self.__cat!r},{self.__semty!r})'

    @property
    def cat(self):
        return self.__cat

    @property
    def attrs(self):
        return self.__attrs

    @property
    def semty(self):
        return self.__semty

    def with_parens(self):
        return str(self)

    def __eq__(self, other):
        # XXX Ignores features!
        return (self.cat == other.cat)

    def __le__(self, other):
        return self == other

    @property
    def spine(self):
        return (self, [])

    @property
    def slash(self):
        return None


class SlashCategory:
    """A complex grammatical category, with a given codomain, domain,
       and slash type"""

    def __init__(self, cod, slash, dom):
        assert isinstance(slash, s.Slash)
        self.__slash = slash
        self.__cod = cod
        self.__dom = dom

    @property
    def cod(self):
        return self.__cod

    @property
    def slash(self):
        return self.__slash

    @property
    def dom(self):
        return self.__dom

    def __eq__(self, other):
        return (isinstance(other, SlashCategory) and
                (self.slash == other.slash) and
                (self.dom == other.dom) and
                (self.cod == other.cod))

    def __repr__(self):
        return (f'SlashCategory({self.__cod!r},' +
                f'{self.__slash!r},' +
                f'{self.__dom!r}')

    def with_parens(self):
        return '(' + str(self) + ')'

    def __str__(self):
        return \
            f'{self.cod.with_parens()}{self.slash}{self.dom.with_parens()}'

    @property
    def semty(self):
        return sem.ArrowType(self.dom.semty, self.cod.semty)

    def __le__(self, other):
        return (isinstance(other, SlashCategory) and
                self.slash <= other.slash and
                self.dom >= other.dom and
                self.cod <= other.cod)

    @property
    def spine(self):
        h, t = self.cod.spine
        return (h, [(self.slash, self.dom)] + t)


############################
# USEFUL COMMON CATEGORIES #
############################
NP = BaseCategory("NP", sem.ett)                   # noun phrase
S = BaseCategory("S", sem.t)                     # sentence
PP = BaseCategory("PP", sem.t)                   # prepositional phrase
VBI = SlashCategory(S, s.LSLASH, NP)          # intransitive verb, S\NP
VBT = SlashCategory(VBI, s.RSLASH, NP)       # transitive verb, (S\NP)/NP
MODAL = SlashCategory(VBI, s.RSLASH, VBI)    # modal verb, (S\NP)/(S\NP)


def mk_NP(attr):
    return BaseCategory("NP", sem.ett, attr)


SINGULAR = pyrsistent.m(num='sg')
PLURAL = pyrsistent.m(num='pl')

NPsg = mk_NP(SINGULAR)
NPpl = mk_NP(PLURAL)


def mk_coord(cat):
    return SlashCategory(
        SlashCategory(cat, s.mk_lslash(s.APPLYONLY), cat),
        s.mk_rslash(s.APPLYONLY),
        cat)


print(VBT)


#####################
# Simple unit tests #
#####################


def test_eq():
    assert VBI != VBT
    assert VBI == SlashCategory(LEFT, S, NP)
    assert SlashCategory(LEFT, S, NP) == VBI
    assert MODAL.dom == MODAL.cod
