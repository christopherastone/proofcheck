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


def ForwardComposition(item1, item2, dest):
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


c_arg = [category.NP, category.S, category.VBI]

"""
def TypeRaise(item, dest):
    cat = item.cat
    sem = item.sem
    if cat in c_arg:
        dest += [
            Item(category.SlashCategory(
                category.Right, 
                category.SlashCategory(
                    category.LEFT,
                    cat, 
                category.
                
        )
"""

def NFConstraintViolation(item1, item2, n, dir='>'):
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

    return False


def GeneralizedForwardComposition(item1, item2, dest):
    # print(f'GeneralizedForwardcomposition: {item1}, {item2}')

    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    # We are looking for item1 = (X/Y) and
    #                    item2 = Y/Z1/Z2.../Zk    (k >= 0)
    if cat1.slash != category.RIGHT:
        # print(f'Not applying a right slash')
        return

    zs = []
    rightCat = cat2
    # print(f'looking for {cat1.dom}')
    while (rightCat != cat1.dom):
        # print(f'loop: rightCat = {rightCat}')
        if rightCat.slash != category.RIGHT:
            # we haven't found Y, and we've run out of
            # Z's to pull off
            return
        zs.append(rightCat.dom)
        rightCat = rightCat.cod

    # Success... if we've gotten this far, the rule applies
    # But zs currently contains Zk, ..., Z2, Z1, so we need to reverse
    zs = list(reversed(zs))
    nargs = len(zs)
    # print(f'woohoo. zs = {zs}')

    if NFConstraintViolation(item1, item2, nargs, '>'):
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
    outsem = functools.reduce(
                lambda x, y: semantics.Lam(y, x),
                [outsem] + [semantics.gensym() for z in zs])

    outwhy = ['>B' + str(nargs), item1, item2]

    dest += [Item(outcat, outsem, outwhy)]


def dofwdcompose(cat1, cat2):
    out = []
    GeneralizedForwardComposition(Item(cat1, semantics.Const("f"), None),
                                  Item(cat2, semantics.Const("g"), None),
                                  out)
    return out


# TESTING SUPPORT

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


def test_GeneralizedForwardComposition():
    oldcounter = semantics.counter

    semantics.counter = 0
    ans1 = dofwdcompose(category.NP, category.S)
    assert ans1 == []

    semantics.counter = 0
    ans2 = dofwdcompose(np_s, category.S)
    assert len(ans2) == 1
    assert str(ans2[0].cat) == 'NP'
    assert str(ans2[0].sem) == 'f(g)'
    assert ans2[0].why[0] == '>B0'

    semantics.counter = 0
    ans3 = dofwdcompose(np_s, s_np)
    assert len(ans3) == 1
    assert str(ans3[0].cat) == '(NP/NP)'
    assert str(ans3[0].sem) == 'λx0.f(g(x0))'
    assert ans3[0].why[0] == '>B1'

    semantics.counter = 0
    ans4 = dofwdcompose(np_s, s_np_s)
    assert len(ans4) == 1
    assert str(ans4[0].cat) == '((NP/NP)/S)'
    assert str(ans4[0].sem) == 'λx1.λx0.f(g(x1)(x0))'
    assert ans4[0].why[0] == '>B2'

    semantics.counter = 0
    ans5 = dofwdcompose(s_np_s, s_np)
    assert len(ans5) == 1
    assert str(ans5[0].cat == '((S/NP)/NP)')
    assert str(ans5[0].sem) == 'λx0.f(g(x0))'
    assert ans5[0].why[0] == '>B1'

    semantics.counter = 0
    ans6 = dofwdcompose(s_np__s_np, s_np_s)
    assert len(ans6) == 1
    assert str(ans6[0].cat) == '((S/NP)/S)'
    assert str(ans6[0].sem) == 'λx0.f(g(x0))'
    assert ans6[0].why[0] == '>B1'


    semantics.counter = 0
    ans7 = dofwdcompose(s_np__s_np, s_np_s_np)
    assert len(ans7) == 1
    assert str(ans7[0].cat) == '(((S/NP)/S)/NP)'
    assert str(ans7[0].sem) == 'λx1.λx0.f(g(x1)(x0))'
    assert ans7[0].why[0] == '>B2'

    semantics.counter = 0
    ans8 = dofwdcompose(s_np__s_np, s_np__s_np)
    assert len(ans8) == 1
    assert str(ans8[0].cat) == '((S/NP)/(S/NP))'
    assert str(ans8[0].sem) == 'λx0.f(g(x0))'
    assert ans8[0].why[0] == '>B1'

    semantics.counter = 0
    ans9 = dofwdcompose(s_np__s_np, s_np)
    assert len(ans9) == 1
    assert str(ans9[0].cat) == '(S/NP)'
    assert str(ans9[0].sem) == 'f(g)'
    assert ans9[0].why[0] == '>B0'

    semantics.counter = oldcounter

"""
baldridgeRules = [[],
                  [ForwardApplication,
                   BackwardApplication,
                   ForwardComposition]]
"""

baldridgeRules = [[],
                  [BackwardApplication,
                   GeneralizedForwardComposition]]

