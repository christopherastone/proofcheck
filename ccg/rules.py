"""
CCG Combinatory Rules
"""

import functools

import category
import semantics
from item import Item


def deconstruct(item1, item2):
    return (item1.cat, item1.sem, item2.cat, item2.sem)


normalize = True

"""
def forward_application(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)
    if (cat1.slash == category.RIGHT and cat1.dom == cat2 and
            # XXX: overly specific - won't extend to generalized composition
            (not normalize or (item1.why[0] != '>' and
                               (not item1.why[0].startswith('>B')) and
                               item1.why[0] != '>T'))):
        dest += [Item(cat1.cod,
                      semantics.App(sem1, sem2).reduce(),
                      ['>', item1, item2])]
"""


def backward_application(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)
    if (cat2.slash == category.LEFT and cat2.dom == cat1 and
            (not normalize or (item2.why[0] != '<' and
                               (not item2.why[0].startswith('<B')) and
                               item2.why[0] != '<T'))):
        dest += [Item(cat2.cod,
                      semantics.App(sem2, sem1).reduce(),
                      ['<', item1, item2])]


"""
def forward_composition(item1, item2, dest):
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
"""

c_arg = [category.NP, category.S, category.VBI]


def typeraise_right(T, item):
    return Item(
            category.SlashCategory(
                category.RIGHT, T,
                category.SlashCategory(category.LEFT, T, item.cat)),
            semantics.Lam("z",
                          semantics.App(semantics.BoundVar(0),
                                        item.sem.shift(1))),
            ['>T', item])


def typeraise_left(T, item):
    return Item(
            category.SlashCategory(
                category.LEFT, T,
                category.SlashCategory(category.RIGHT, T, item.cat)),
            semantics.Lam("z",
                          semantics.App(semantics.BoundVar(0),
                                        item.sem.shift(1))),
            ['<T', item])


def typeraise_easyccg(item, dest):
    """Lewis and Steedman, A* CCG Parsing with a Supertag-factored Model
       lists 3 specific instances of type raising used in EasyCCG, namely
            NP   ->    S / (S\\NP)
            NP   ->    (S\\NP) / ((S\\NP)\\NP)
            PP   ->    (S\\NP) / ((S\\NP)\\PP)
       but the github implementation seems to say
            NP   ->    S[X] / (S[X]\\NP)
            NP   ->    (S[X]\\NP) \\ ((S[X]\\NP)/NP)
            PP   ->    (S[X]\\NP) \\ ((S[X]\\NP)/PP)
       which (a) is more general, and (b) has slashes the other direction
       for the last two rules. [Curren and Clark use rules with slashes
       in the same direction as the implementation, so the paper is
       probably a typo.]
       We compromise by using the un-generalized rules, but with
       slashes in the C&C/github direction.
    """
    if item.cat == category.NP:
        dest += [typeraise_right(category.S, item),
                 typeraise_left(category.VBI, item)]

    elif item.cat == category.PP:
        dest += [typeraise_left(category.VBI, item)]


def typeraise_candc(item, dest):
    """Taken from Appendix A (p542) of Clark and Curran, 2007."""
    if item.cat == category.NP:
        dest += [typeraise_right(category.S, item),
                 typeraise_left(category.VBI, item),
                 typeraise_left(category.VBT, item),
                 typeraise_left(
                     # NP -> ((S\NP)/PP) \ ( ((S\NP)/PP) / NP )
                     category.SlashCategory(
                         category.RIGHT, category.VBI, category.PP), item),
                 # TODO: Add these when it's time
                 # typeraise_left((S\NP)/(S[to]\NP), item)
                 # typeraise_left((S\NP)/(S[adj]\NP), item)
                 ]
    elif item.cat == category.PP:
        dest += [typeraise_left(category.VBI, item)]

    # TODO: Add these when it's time
    # elif item.cat == (S[adj]\NP):
    #   dest += [typeraise_left(category.VBI, item)]


def compose_constraint_violation(item1, item2, n, dir='>'):
    # Hockenmaier and Bisk NF Constraint 1:
    # Forbid
    #   X/A  A/Y[1..k]/C
    #   -------------- >B(k+1)
    #      X/Y[1..k]/C            C
    #   ------------------------------ >
    #          X/Y[1..k]
    #
    # and
    #
    #   X/A  A/Y[1..k]/C
    #   -------------- >B(k+1)
    #      X/Y[1..k]/C            C/D
    #   ------------------------------ >B1
    #          X/Y[1..k]/D
    if (n == 0 or n == 1):
        if (item1.why and
                item1.why[0] != dir+'B0' and
                item1.why[0].startswith(dir+'B')):
            return True

    # Hockenmaier and Bisk NF Constraint 2:
    # Forbid
    #   A/B     B/C
    #   ----------- >B1
    #       A/C                C/D[1..n]
    #   ---------------------------------  >Bn  (n > 0)
    #                A/D[1..n]
    # because we prefer the right-branching tree
    #                B/C    C/D[1..n]
    #               ------------------ >Bn
    #   A/B              B/D[1..n]
    #  ---------------------------------  >Bn
    #           A/D[1..n]

    if (n > 1):
        if (item1.why and item1.why[0] == dir+'B1'):
            return True

    # Hockenmaier and Bisk NF Constraint 3:
    # Forbid
    #             B/C[1..k]/D          D/E[1..m]
    #             ------------------------------ >Bm   (m > 1, k>1)
    #    A/B               B/C[1..k]/E[1..m]
    #  ----------------------------------------- >B(k+m)
    #              A/C[1..k]/E[1..m]
    # because we prefer the [probably] lower-degree tree
    #    A/B     B/C[1..k]/D
    #   --------------------- >B(k+1)
    #        A/C[1..k]/D                    D/E[1..m]
    #   ------------------------------------------------ >Bm
    #                      A/C[1..k]/E[1..m]
    if (item2.why and item2.why[0].startswith(dir+'B') and
            int(item2.why[0][2:]) < n):
        return True

    # Hockenmaier and Bisk NF Constraint 4:
    #    TODO

    # Hockenmaier and Bisk NF Constraint 5:
    # Forbid
    #       X
    #    ------- >T
    #    A/(A\X)            (A\X)
    #    ------------------------ >
    #               A
    # because we could have just the single step
    #     X     (A\X)
    #    ------------- >
    #         A
    if (n == 0):
        if item1.why and item1.why[0] == dir+'T':
            return True

    return False


def generalized_forward_composition(item1, item2, dest):
    # print(f'GeneralizedForwardcomposition: {item1}, {item2}')

    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    # We are looking for item1 = (X/Y) and
    #                    item2 = Y/Z1/Z2.../Zk    (k >= 0)
    if cat1.slash != category.RIGHT:
        # print(f'Not applying a right slash')
        return

    zs = []
    right_cat = cat2
    # print(f'looking for {cat1.dom}')
    while (right_cat != cat1.dom):
        # print(f'loop: right_cat = {right_cat}')
        if right_cat.slash != category.RIGHT:
            # we haven't found Y, and we've run out of
            # Z's to pull off
            return
        zs.append(right_cat.dom)
        right_cat = right_cat.cod

    # Success... if we've gotten this far, the rule applies
    # But zs currently contains Zk, ..., Z2, Z1, so we need to reverse
    zs = list(reversed(zs))
    nargs = len(zs)
    # print(f'woohoo. zs = {zs}')

    if compose_constraint_violation(item1, item2, nargs, '>'):
        return

    # The output category will be (X/Z1)/.../Zn
    outcat = functools.reduce(
                lambda x, y: category.SlashCategory(category.RIGHT, x, y),
                [cat1.cod] + zs)

    # The output semantics should be
    #  \zn...\z2\z1. f (g z1 ... zn)

    # build f's argument.
    outsem = functools.reduce(
                semantics.App,
                [sem2] + [semantics.BoundVar(k)
                          for k in reversed(range(nargs))])

    # apply f
    outsem = semantics.App(sem1, outsem)
    # simplify body
    outsem = outsem.reduce()
    # lambda-abstract
    if len(zs) == 1:
        # Pick a nicer name than a0 for simple composition
        outsem = semantics.Lam("a", outsem)
    else:
        outsem = functools.reduce(
                    lambda x, y: semantics.Lam(y, x),
                    [outsem] + ["a" + str(i) for i in range(len(zs))])

    outwhy = ['>B' + str(nargs), item1, item2]

    dest += [Item(outcat, outsem, outwhy)]


###############################################
# TESTING SUPPORT
###############################################

# NP/S
np_s = category.SlashCategory(category.RIGHT, category.NP, category.S)
# S/NP
s_np = category.SlashCategory(category.RIGHT, category.S, category.NP)
# (S/NP)/S
s_np_s = category.SlashCategory(category.RIGHT, s_np, category.S)
# ((S/NP)/S)/NP
s_np_s_np = category.SlashCategory(category.RIGHT, s_np_s, category.NP)
# (S/NP) / (S/NP)
s_np__s_np = category.SlashCategory(category.RIGHT, s_np, s_np)


def dofwdcompose(cat1, cat2):
    out = []
    generalized_forward_composition(Item(cat1, semantics.Const("f"), None),
                                    Item(cat2, semantics.Const("g"), None),
                                    out)
    return out


def test_gfc():
    ans1 = dofwdcompose(category.NP, category.S)
    assert ans1 == []

    ans2 = dofwdcompose(np_s, category.S)
    assert len(ans2) == 1
    assert str(ans2[0].cat) == 'NP'
    assert str(ans2[0].sem) == 'f(g)'
    assert ans2[0].why[0] == '>B0'

    ans3 = dofwdcompose(np_s, s_np)
    assert len(ans3) == 1
    assert str(ans3[0].cat) == '(NP/NP)'
    assert str(ans3[0].sem) == 'λa.f(g(a))'
    assert ans3[0].why[0] == '>B1'

    ans4 = dofwdcompose(np_s, s_np_s)
    assert len(ans4) == 1
    assert str(ans4[0].cat) == '((NP/NP)/S)'
    assert str(ans4[0].sem) == 'λa1.λa0.f(g(a1)(a0))'
    assert ans4[0].why[0] == '>B2'

    ans5 = dofwdcompose(s_np_s, s_np)
    assert len(ans5) == 1
    assert str(ans5[0].cat == '((S/NP)/NP)')
    assert str(ans5[0].sem) == 'λa.f(g(a))'
    assert ans5[0].why[0] == '>B1'

    ans6 = dofwdcompose(s_np__s_np, s_np_s)
    assert len(ans6) == 1
    assert str(ans6[0].cat) == '((S/NP)/S)'
    assert str(ans6[0].sem) == 'λa.f(g(a))'
    assert ans6[0].why[0] == '>B1'

    ans7 = dofwdcompose(s_np__s_np, s_np_s_np)
    assert len(ans7) == 1
    assert str(ans7[0].cat) == '(((S/NP)/S)/NP)'
    assert str(ans7[0].sem) == 'λa1.λa0.f(g(a1)(a0))'
    assert ans7[0].why[0] == '>B2'

    ans8 = dofwdcompose(s_np__s_np, s_np__s_np)
    assert len(ans8) == 1
    assert str(ans8[0].cat) == '((S/NP)/(S/NP))'
    assert str(ans8[0].sem) == 'λa.f(g(a))'
    assert ans8[0].why[0] == '>B1'

    ans9 = dofwdcompose(s_np__s_np, s_np)
    assert len(ans9) == 1
    assert str(ans9[0].cat) == '(S/NP)'
    assert str(ans9[0].sem) == 'f(g)'
    assert ans9[0].why[0] == '>B0'


"""
parsingRules = [[],
                [forward_application,
                 backward_application,
                 forward_composition]]
"""

parsingRules = [[typeraise_candc],
                [backward_application,
                 generalized_forward_composition]]
