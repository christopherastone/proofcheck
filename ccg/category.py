"""
CCG Categories.
"""

import collections
import pyrsistent
import slash
import semantic_types
import semantics


def extend_pmap(pmap1, map2):
    return pyrsistent.pmap(
        {a: b.subst(map2) for a, b in pmap1.items()}
    ).update(map2)


class Attr:
    __slots__ = ('__value')

    def __init__(self, value):
        self.__value = value

    def __eq__(self, other, mvs_l=None, mvs_r=None):
        return isinstance(other, Attr) and \
            self.__value == other.__value

    def __str__(self, mv_to_string=None):
        return self.__value

    def __repr__(self):
        return f'Attr({self.__value!r})'

    def __hash__(self):
        return hash(self.__value)

    def sub_unify(self, other, sub=pyrsistent.m()):
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, Metavar):
            assert id(other) not in sub
            return extend_pmap(sub, {id(other): self})
        elif isinstance(other, Attr) and self.__value == other.__value:
            return sub
        else:
            return None


class Metavar:
    """An unknown value"""

    __slots__ = ('__hint')

    def __init__(self, hint):
        self.__hint = hint

    @property
    def hint(self):
        return self.__hint

    def __repr__(self):
        return f'Metavar({self.__hint!r})'

    def __str__(self, mv_to_string=None):
        if mv_to_string is None:
            return f'{self.__hint}'
        else:
            return mv_to_string(self)

    def __hash__(self):
        return 42   # To make sure that T/T and U/U have the same
                   #  hash value, given that == does alpha-equivalence
                   #  and so T/T == U/U
                   # Fortunately, few categories have more than
                   #  one metavarible, so it's not really worse
                   #  than what we do for, say, the base category NP

    def with_parens(self, mv_to_string=None):
        return self.__str__(mv_to_string)

    @property
    def semty(self):
        return None

    @property
    def closed(self):
        return False

    def __eq__(self, other, mvs_l=None, mvs_r=None):
        if not (isinstance(other, Metavar)):
            return False

        if mvs_l is None or mvs_r is None:
            # short-circuit the code below, if we created
            # an empty dictionary, discovered neither was
            # present, and updated the dictionary,
            # and then threw it away.
            assert(False)  # I'm not sure that two isolated Metavars
                         # should default to being equal...
            return True

        id_self = id(self)
        id_other = id(other)
        key_l = mvs_l.get(id_self, None)
        key_r = mvs_r.get(id_other, None)
        if key_l != key_r:
            return False
        if key_l is None:
            # hence key_r is also None. Map both to the same "fresh" identifier.
            third = len(mvs_l)
            assert third == len(mvs_r)
            mvs_l[id_self] = third
            mvs_r[id_other] = third
        return True

    def sub_unify(self, other, sub=pyrsistent.m()):
        # print(f'CMV: sub_unify of {self} and {other}')
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, Metavar):
            third = Metavar(other.__hint)
            answer = extend_pmap(sub, {id(self):  third, id(other): third})
        else:
            answer = extend_pmap(sub, {id(self):  other})
        return answer

    def subst(self, sub):
        if sub is not None:
            return sub.get(id(self), self)
        else:
            # a past unification failed; just keep going
            return self

    def refresh(self, mv_map=None):
        if mv_map is None:
            mv_map = {}
        key = id(self)
        if key in mv_map:
            return mv_map[key]
        else:
            answer = Metavar(self.__hint)
            mv_map[key] = answer
            return answer


class BaseCategory:
    """An atomic grammatical category, such as NP,
       with optional fixed attributes"""

    __slots__ = ('__cat', '__attrs', '__semty', '__hash')

    def __init__(self, cat, semty, attrs=pyrsistent.m()):
        self.__cat = cat
        self.__attrs = attrs
        self.__semty = semty
        self.__hash = hash((cat, attrs))
        assert(not(isinstance(attr, str)) for attr in attrs.values())

    def __str__(self, mv_to_string=None):
        if self.__attrs:
            values_s = [attr.__str__(mv_to_string)
                        for attr in self.__attrs.values()]
            return f'{self.__cat}[{",".join(values_s)}]'
        else:
            return self.__cat

    def __repr__(self):
        if self.__attrs:
            return \
                (f'BaseCategory({self.__cat!r},{self.__semty!r},'
                 f'{self.__attrs!r})')
        else:
            return f'BaseCategory({self.__cat!r},{self.__semty!r})'

    def __hash__(self):
        return self.__hash

    @property
    def cat(self):
        return self.__cat

    @property
    def attrs(self):
        return self.__attrs

    @property
    def semty(self):
        return self.__semty

    @property
    def closed(self):
        return True

    def with_parens(self, mv_to_string=None):
        return self.__str__(mv_to_string)

    def __eq__(self, other, mvs_l=None, mvs_r=None):
        return (isinstance(other, BaseCategory) and
                self.__cat == other.__cat and
                len(self.__attrs) == len(other.__attrs) and
                all(k in other.__attrs and
                     self.__attrs[k].__eq__(other.__attrs[k], mvs_l, mvs_r)
                     for k in self.__attrs.keys()))

    def sub_unify(self, other, sub=pyrsistent.m()):
        #print(f'BaseCategory: sub_unify of {self} and {other}')
        if sub is None:
            # Short-circuit after failure in chained unifications.
            return None

        elif isinstance(other, Metavar):
            assert id(other) not in sub
            return extend_pmap(sub, {id(other): self})

        elif isinstance(other, BaseCategory):
            if self.__cat != other.__cat:
                return None

            for k, v in other.__attrs.items():
                if k not in self.__attrs.keys():
                    return None
                sub = v.sub_unify(other.__attrs[k], sub)

            return sub
        else:
            return None

    def subst(self, sub):
        # XXX: Ignores feature variables
        return self

    def refresh(self, mv_map=None):
        return self


class SingletonCategory:
    """A category containing a specific word(s) with
       no interesting semantics"""

    __slots__ = ('__word')

    def __init__(self, word):
        self.__word = word

    def __str__(self, mv_to_string=None):
        return f'"{self.__word}"'

    def __repr__(self):
        return f'SingletonCategory({self.__word!r})'

    def __hash__(self):
        return hash(self.__word)

    @property
    def word(self):
        return self.__word

    def with_parens(self, mv_to_string=None):
        return self.__str__(mv_to_string)

    def __eq__(self, other, mvs_l=None, mvs_r=None):
        return (isinstance(other, SingletonCategory) and
                self.__word == other.__word)

    def __le__(self, other):
        return self == other

    @property
    def slash(self):
        return None

    @property
    def semty(self):
        return semantic_types.BaseType("1")

    @property
    def closed(self):
        return True

    def sub_unify(self, other, sub=pyrsistent.m()):
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, Metavar):
            assert id(other) not in sub
            answer = extend_pmap(sub, {id(other): self})
        elif isinstance(other, SingletonCategory):
            answer = sub if self == other else None
        else:
            answer = None
        return answer

    def subst(self, sub):
        return self

    def refresh(self, mv_map=None):
        return self


class SlashCategory:
    """A complex grammatical category,
       with a given codomain, domain, and slash"""

    __slots__ = ('__slash', '__cod', '__dom', '__closed', '__hash')

    def __init__(self, cod, sl, dom):
        assert isinstance(sl, slash.Slash)
        self.__slash = sl
        self.__cod = cod
        self.__dom = dom
        self.__closed = cod.closed and dom.closed
        self.__hash = hash((cod, sl, dom))

    def __hash__(self):
        return self.__hash

    @property
    def cod(self):
        return self.__cod

    @property
    def slash(self):
        return self.__slash

    @property
    def dom(self):
        return self.__dom

    @property
    def closed(self):
        return self.__closed

    def __repr__(self):
        return f'SlashCategory({self.__cod!r},' \
               f'{self.__slash!r},' \
               f'{self.__dom!r}'

    def __str__(self, mv_to_string=None):
        answer = f'{self.__cod.__str__(mv_to_string)}' \
            f'{self.__slash}' \
                 f'{self.__dom.with_parens(mv_to_string)}'
        if len(answer) > 35 and mv_to_string is None:
            answer = "..."
        return answer

    def with_parens(self, mv_to_string=None):
        return f'({self.__str__(mv_to_string)})'

    @property
    def semty(self):
        return semantic_types.ArrowType(self.__dom.semty, self.__cod.semty)

    def __eq__(self, other, mvs_l=None, mvs_r=None):
        """Checks for syntactic equality (not unifiability)"""
        if not self.__closed and mvs_l is None:
            assert mvs_r is None  # both defined or both None
            mvs_l = {}
            mvs_r = {}
        return (isinstance(other, SlashCategory) and
                self.__dom.__eq__(other.__dom, mvs_l, mvs_r) and
                self.__cod.__eq__(other.__cod, mvs_l, mvs_r) and
                (self.__slash == other.__slash))

    def sub_unify(self, other, sub=pyrsistent.m()):
        if sub is None:
            # Short-circuit after failure in chained unifications.
            answer = None
        elif isinstance(other, Metavar):
            assert id(other) not in sub
            # XXX over-precise?
            answer = extend_pmap(sub, {id(other): self})
        elif isinstance(other, SlashCategory):
            if not (self.__slash <= other.__slash):
                # failure because slashes don't match.
                # XXX update when we have variable slash modes!
                sub = None
            # If the slashes match we need the other domain to be smaller
            # (contravariant) and this codomain to be smaller (codomain)
            sub = self.__cod.sub_unify(other.__cod, sub)
            sub = other.__dom.subst(sub).sub_unify(self.__dom.subst(sub), sub)
            answer = sub
        else:
            answer = None
        return answer

    def subst(self, sub):
        if self.__closed:
            return self
        else:
            return SlashCategory(
                self.__cod.subst(sub),
                self.__slash,
                self.__dom.subst(sub))

    def refresh(self, mv_map=None):
        if self.__closed:
            return self
        if mv_map is None:
            mv_map = {}
        return SlashCategory(
            self.__cod.refresh(mv_map),
            self.__slash,
            self.__dom.refresh(mv_map))



############################
# USEFUL COMMON CATEGORIES #
############################
NP = BaseCategory("NP", semantic_types.ett)                   # noun phrase
S = BaseCategory("S", semantic_types.t)                     # sentence
# prepositional phrase
PP = BaseCategory("PP", semantic_types.t)
VBI = SlashCategory(S, slash.LSLASH, NP)          # intransitive verb, S\NP
VBT = SlashCategory(VBI, slash.RSLASH, NP)       # transitive verb, (S\NP)/NP
MODAL = SlashCategory(VBI, slash.RSLASH, VBI)    # modal verb, (S\NP)/(S\NP)


def mk_NP(attr):
    return BaseCategory("NP", semantic_types.ett, attr)


SINGULAR = pyrsistent.m(num='sg')
PLURAL = pyrsistent.m(num='pl')

NPsg = mk_NP(SINGULAR)
NPpl = mk_NP(PLURAL)


def mk_coord(cat):
    return SlashCategory(
        SlashCategory(cat, slash.mk_lslash(slash.APPLYONLY), cat),
        slash.mk_rslash(slash.APPLYONLY),
        cat)


def explicit_string(cat):
    def f(mv):
        return f'{mv.hint}:{id(mv)}'
    return cat.__str__(f)


def alpha_normalized_string(cat):
    counter_map = collections.defaultdict(dict)

    def f(mv):
        nonlocal counter_map
        enumeration = counter_map[mv.hint]
        n = enumeration.setdefault(id(mv), len(enumeration))
        if n == 0:
            return mv.hint
        else:
            return f'{mv.hint}{n}'
    return cat.__str__(f)


#####################
# Simple unit tests #
#####################


def test_eq():
    assert VBI != VBT
    assert VBI == SlashCategory(S, slash.LSLASH, NP)
    assert SlashCategory(S, slash.LSLASH, NP) == VBI
    assert MODAL.dom == MODAL.cod
    print(MODAL)


def test_alpha_str():
    print(alpha_normalized_string(MODAL))

    mv1 = Metavar('A')
    mv2 = Metavar('A')

    cat1 = SlashCategory(mv1, slash.RSLASH, mv1)
    cat2 = SlashCategory(mv1, slash.RSLASH, mv2)
    cat3 = SlashCategory(mv2, slash.RSLASH, mv1)
    cat4 = SlashCategory(mv2, slash.RSLASH, mv2)

    cats = [cat1, cat2, cat3, cat4]

    for x in cats:
        for y in cats:
            print(explicit_string(x), explicit_string(y), alpha_normalized_string(x), alpha_normalized_string(y),
                  x is y, x == y)
            assert (x == y) == \
                (alpha_normalized_string(x) ==
                 alpha_normalized_string(y))

    for x in cats:
        xr = x.refresh()
        assert x == xr


if __name__ == '__main__':
    test_eq()
    test_alpha_str()
