"""
CCG Categories.
"""

import pyrsistent
import slash as s
import semantic_types
import semantics


def extend_pmap(pmap1, map2):
    return pyrsistent.pmap(
        {a: b.subst(map2) for a, b in pmap1.items()}
    ).update(map2)


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
        return (isinstance(other, BaseCategory) and
                self.cat == other.cat)

    def sub_unify(self, other, sub=pyrsistent.m()):
        # print(f'BaseCategory: sub_unify of {self} and {other}')
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, CategoryMetavar):
            assert other not in sub
            answer = extend_pmap(sub, {other: self})
        elif isinstance(other, BaseCategory):
            # XXX ignores features!
            answer = sub if self == other else None
        else:
            answer = None
        # print(
        #     f'BaseCategory: sub_unify of {self} and {other}: '
        #     f'answer = {answer}')
        return answer

    # def __le__(self, other):
    #     print(f'BaseCategory: <= of {self} and {other}')
    #     sub = self.sub_unify(other)
    #     print(f'BaseCategory: <= of {self} and {other}: sub = {sub}')
    #     return (sub is not None)

    def subst(self, sub):
        # XXX: Ignores feature variables
        return self


class SingletonCategory:
    """A category containing a specific word(s) with
       no interesting semantics"""

    def __init__(self, word):
        self.__word = word

    def __str__(self):
        return f'"{self.word}"'

    def __repr__(self):
        return f'SingletonCategory({self.word!r})'

    @property
    def word(self):
        return self.__word

    def with_parens(self):
        return str(self)

    def __eq__(self, other):
        return (isinstance(other, SingletonCategory) and
                self.word == other.word)

    def __le__(self, other):
        return self == other

    @property
    def slash(self):
        return None

    @property
    def semty(self):
        return semantic_types.BaseType("1")

    def sub_unify(self, other, sub=pyrsistent.m()):
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, CategoryMetavar):
            assert other not in sub
            answer = extend_pmap(sub, {other: self})
        elif isinstance(other, SingletonCategory):
            # XXX ignores features!
            answer = sub if self == other else None
        else:
            answer = None
        return answer

    # def __le__(self, other):
    #     return self.sub_unify(other) is not None

    def subst(self, sub):
        # XXX: Ignores feature variables
        return self


class SlashCategory:
    """A complex grammatical category,
       with a given codomain, domain, and slash"""

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

    def __repr__(self):
        return f'SlashCategory({self.cod!r},' \
               f'{self.__slash!r},' \
               f'{self.__dom!r}'

    def __str__(self):
        return \
            f'{self.cod.with_parens()}{self.slash}{self.dom.with_parens()}'

    def with_parens(self):
        return '(' + str(self) + ')'

    @property
    def semty(self):
        if self.dom.semty:
            return semantic_types.ArrowType(self.dom.semty, self.cod.semty)
        else:
            return self.cod.semty

    def __eq__(self, other):
        """Checks for syntactic equality (not unifiability)"""
        return (isinstance(other, SlashCategory) and
                (self.slash == other.slash) and
                (self.dom == other.dom) and
                (self.cod == other.cod))

    def sub_unify(self, other, sub=pyrsistent.m()):
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, CategoryMetavar):
            assert(other not in sub)
            # XXX over-precise?
            answer = extend_pmap(sub, {other: self})
        elif isinstance(other, SlashCategory):
            if not (self.slash <= other.slash):
                # failure because slasheds don't match.
                # XXX update when we have variable slash modes!
                return None
            # If the slashes match we need the other domain to be smaller
            # (contravariant) and this codomain to be smaller (codomain)
            sub = self.cod.sub_unify(other.cod, sub)
            if sub is not None:
                sub = other.dom.subst(sub).sub_unify(self.dom.subst(sub), sub)
            answer = sub
        else:
            answer = None
        return answer

    # def __le__(self, other):
    #     return self.sub_unify(other) is not None

    def subst(self, sub):
        return SlashCategory(
            self.cod.subst(sub),
            self.slash,
            self.dom.subst(sub))


class CategoryMetavar:
    """An unknown category"""

    def __init__(self, hint):
        self.__hint = hint

    @property
    def hint(self):
        return self.__hint

    def __repr__(self):
        return f'SCategoryMetavar({self.hint!r})'

    def __str__(self):
        return f'{self.hint}'
        # f'M[{self.hint}:{id(self)}]'

    def with_parens(self):
        return str(self)

    @property
    def semty(self):
        return None

    def __eq__(self, other):
        """Checks for pointer equality (not unifiability)"""
        return self is other

    def sub_unify(self, other, sub=pyrsistent.m()):
        # print(f'CMV: sub_unify of {self} and {other}')

        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        else:
            # XXX over-precise?
            answer = extend_pmap(sub, {self: other})
        return answer

    # def __le__(self, other):
    #     return self.sub_unify(other) is not None

    def subst(self, sub):
        if self in sub:
            return sub[self]
        else:
            return self

    def __hash__(self):
        return id(self)


############################
# USEFUL COMMON CATEGORIES #
############################
NP = BaseCategory("NP", semantic_types.ett)                   # noun phrase
S = BaseCategory("S", semantic_types.t)                     # sentence
# prepositional phrase
PP = BaseCategory("PP", semantic_types.t)
VBI = SlashCategory(S, s.LSLASH, NP)          # intransitive verb, S\NP
VBT = SlashCategory(VBI, s.RSLASH, NP)       # transitive verb, (S\NP)/NP
MODAL = SlashCategory(VBI, s.RSLASH, VBI)    # modal verb, (S\NP)/(S\NP)


def mk_NP(attr):
    return BaseCategory("NP", semantic_types.ett, attr)


SINGULAR = pyrsistent.m(num='sg')
PLURAL = pyrsistent.m(num='pl')

NPsg = mk_NP(SINGULAR)
NPpl = mk_NP(PLURAL)


def mk_coord(cat):
    return SlashCategory(
        SlashCategory(cat, s.mk_lslash(s.APPLYONLY), cat),
        s.mk_rslash(s.APPLYONLY),
        cat)


#####################
# Simple unit tests #
#####################


def test_eq():
    assert VBI != VBT
    assert VBI == SlashCategory(LEFT, S, NP)
    assert SlashCategory(LEFT, S, NP) == VBI
    assert MODAL.dom == MODAL.cod
