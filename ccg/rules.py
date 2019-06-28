"""
CCG Combinatory Rules
"""

import functools

import category
# import formatting
import semantics
import slash
from item import Item


def deconstruct(item1, item2):
    return (item1.cat, item1.sem, item2.cat, item2.sem)


normalize = True


def forward_application(item1, item2, dest):
    cat1, sem1, cat2, sem2 = deconstruct(item1, item2)
    # print(f'forward_application trying {cat1} @ {cat2}')
    if not (isinstance(cat1, category.SlashCategory) and
            # XXX: ^^^ overspecific, but only if we want to apply metavars.
            slash.RSLASH <= cat1.slash):
        # print(f' forward_application: nope 1')
        return False  # not a function, or not looking rightwards

    if normalize and (  # item1.why[0] == '>' or
            item1.why[0].startswith('>B') or
            item1.why[0] == '>T'):
        # print(f'forward_application: nope 3')
        return False  # this would lead to redundancy

    sub = cat2.sub_unify(cat1.dom)
    if sub is None:
        # print(f'forward_application: {cat2} <= {cat1.dom}: nope 2')
        return False  # application category mismatch

    dest += [Item(cat1.cod,
                  semantics.App(sem1, sem2).reduce(),
                  ['>', item1, item2]).subst(sub)]
    return True


def backward_application(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not (isinstance(cat2, category.SlashCategory) and
            slash.LSLASH <= cat2.slash):
        return False  # not a function, or not looking leftwards

    sub = cat1.sub_unify(cat2.dom)
    if sub is None:
        return False  # application category mismatch

    if normalize and (  # item2.why[0] == '<' or
            item2.why[0].startswith('<B') or
            item2.why[0] == '<T'):
        return False  # this would lead to redundancy

    dest += [Item(cat2.cod,
                  semantics.App(sem2, sem1).reduce(),
                  ['<', item1, item2]).subst(sub)]
    return True


def forward_composition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.RCOMPOSE and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.RCOMPOSE):
        return False  # not both rightwards functions

    sub = cat2.cod.sub_unify(cat1.dom)
    if sub is None:
        return False  # not composeable

    dest += (
        [Item(category.SlashCategory(cat1.cod, slash.RSLASH, cat2.dom),
              semantics.Lam(
            "z",
            semantics.App(
                sem1,
                semantics.App(
                    sem2,
                    semantics.BoundVar(0))).reduce()),
              ['>B', item1, item2]).subst(sub)])
    return True


c_arg = [category.NP, category.S, category.VBI]


def typeraise_constraint_violation(item, dir='>'):
    # NF Constraint 6
    if item.rule() == 'Φ':
        return True
    return False


def typeraise_right(T, item, dest):
    if typeraise_constraint_violation(item, '>'):
        return
    dest += [Item(
        category.SlashCategory(
            T, slash.RSLASH,
            category.SlashCategory(T, slash.LSLASH, item.cat)),
        semantics.Lam("z",
                      semantics.App(semantics.BoundVar(0),
                                    item.sem.shift(1))),
        ['>T', item])
    ]


def typeraise_left(T, item, dest):
    if typeraise_constraint_violation(item, '<'):
        return
    dest += [Item(
        category.SlashCategory(
            T, slash.LSLASH,
            category.SlashCategory(T, slash.RSLASH, item.cat)),
        semantics.Lam("z",
                      semantics.App(semantics.BoundVar(0),
                                    item.sem.shift(1))),
        ['<T', item])
    ]


def typeraise_easyccg(item, dest):
    """Lewis and Steedman, A * CCG Parsing with a Supertag-factored Model
       lists 3 specific instances of type raising used in EasyCCG, namely
            NP -> S / (S\\NP)
            NP -> (S\\NP) / ((S\\NP)\\NP)
            PP -> (S\\NP) / ((S\\NP)\\PP)
       but the github implementation seems to say
            NP -> S[X] / (S[X]\\NP)
            NP -> (S[X]\\NP) \\ ((S[X]\\NP)/NP)
            PP -> (S[X]\\NP) \\ ((S[X]\\NP)/PP)
       which(a) is more general, and (b) has slashes the other direction
       for the last two rules. [Curren and Clark use rules with slashes
       in the same direction as the implementation, so the paper is
       probably a typo.]
       We compromise by using the un-generalized rules, but with
       slashes in the C & C/github direction.
    """
    if item.cat == category.NP:
        typeraise_right(category.S, item, dest)
        typeraise_left(category.VBI, item, dest)

    elif item.cat == category.PP:
        typeraise_left(category.VBI, item, dest)


def typeraise_candc(item, dest):
    """Taken from Appendix A (p542) of Clark and Curran, 2007."""
    print("C AND C")
    if item.cat == category.NP:
        typeraise_right(category.S, item, dest)
        typeraise_left(category.VBI, item, dest),
        typeraise_left(category.VBT, item, dest),
        typeraise_left(
            # NP -> ((S\NP)/PP) \ ( ((S\NP)/PP) / NP )
            category.SlashCategory(category.RIGHT, category.VBI, category.PP),
            item, dest)
        # TODO: Add these when it's time
        # typeraise_left((S\NP)/(S[to]\NP), item, dest)
        # typeraise_left((S\NP)/(S[adj]\NP), item, dest)

    elif item.cat == category.PP:
        typeraise_left(category.VBI, item, dest)

    # TODO: Add these when it's time
    # elif item.cat == (S[adj]\NP):
    #    typeraise_left(category.VBI, item, dest)


def typeraise_simple(item, dest):
    """Until we need something more"""
    if item.cat == category.NP:
        typeraise_right(category.S, item, dest)


def typeraise_generic(item, dest):
    T = category.CategoryMetavar("T")
    typeraise_right(T, item, dest)
    typeraise_left(T, item, dest)


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
        if item1.rule().startswith(dir+'B'):
            # possible violation; but check that it's B(k+1), not B0
            if item1.rule() != dir+'B0':
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
    # TBA

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
    if not (cat1.slash and cat1.slash.dir == slash.RIGHT):
        # print(f'Not applying a right slash')
        return

    zs = []
    right_cat = cat2
    # print(f'looking for {cat1.dom}')
    sub = cat1.dom.unify(right_cat)
    while (sub is None):
        print(f'loop: right_cat = {right_cat}, sub={sub}')
        if not (right_cat.slash and
                right_cat.slash.dir == slash.RIGHT):
            # we haven't found Y, and we've run out of
            # Z's to pull off
            return
        if ',' in cat1.slash or ',' in right_cat.slash:
            # We couldn't directly apply,
            # (otherwise we wouldn't be in the loop)
            # but a slash annotation forbids composition
            return
        zs.append(right_cat.dom)
        right_cat = right_cat.cod
        sub = cat1.dom.unify(right_cat)

    # Success... if we've gotten this far, the rule applies
    # But zs currently contains Zk, ..., Z2, Z1, so we need to reverse
    zs = list(reversed(zs))
    nargs = len(zs)
    # print(f'woohoo. zs = {zs}')

    if compose_constraint_violation(item1, item2, nargs, '>'):
        # print("constraint violated; skipping")
        return

    # The output category will be (X/Z1)/.../Zn
    outcat = functools.reduce(
        lambda x, y: category.SlashCategory(x, slash.RSLASH, y),
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

    dest += [Item(outcat, outsem, outwhy).subst(sub)]


###############################################
# TESTING SUPPORT
###############################################

# NP/S
np_s = category.SlashCategory(category.NP, slash.RSLASH, category.S)
# S/NP
s_np = category.SlashCategory(category.S, slash.RSLASH, category.NP)
# (S/NP)/S
s_np_s = category.SlashCategory(s_np, slash.RSLASH, category.S)
# ((S/NP)/S)/NP
s_np_s_np = category.SlashCategory(s_np_s, slash.RSLASH, category.NP)
# (S/NP) / (S/NP)
s_np__s_np = category.SlashCategory(s_np, slash.RSLASH, s_np)


def do_fwdcompose(cat1, cat2):
    out = []
    forward_composition(Item(cat1, semantics.Const("f"), None),
                        Item(cat2, semantics.Const("g"), None),
                        out)
    return out


do_fwdcompose(np_s, s_np)


def do_genfwdcompose(cat1, cat2):
    out = []
    generalized_forward_composition(Item(cat1, semantics.Const("f"), None),
                                    Item(cat2, semantics.Const("g"), None),
                                    out)
    return out


def test_gfc():
    ans1 = do_genfwdcompose(category.NP, category.S)
    assert ans1 == []

    ans2 = do_genfwdcompose(np_s, category.S)
    assert len(ans2) == 1
    assert str(ans2[0].cat) == 'NP'
    assert str(ans2[0].sem) == 'f(g)'
    assert ans2[0].why[0] == '>B0'

    ans3 = do_genfwdcompose(np_s, s_np)
    assert len(ans3) == 1
    assert str(ans3[0].cat) == '(NP/NP)'
    assert str(ans3[0].sem) == 'λa.f(g(a))'
    assert ans3[0].why[0] == '>B1'

    ans4 = do_genfwdcompose(np_s, s_np_s)
    assert len(ans4) == 1
    assert str(ans4[0].cat) == '((NP/NP)/S)'
    assert str(ans4[0].sem) == 'λa1.λa0.f(g(a1)(a0))'
    assert ans4[0].why[0] == '>B2'

    ans5 = do_genfwdcompose(s_np_s, s_np)
    assert len(ans5) == 1
    assert str(ans5[0].cat == '((S/NP)/NP)')
    assert str(ans5[0].sem) == 'λa.f(g(a))'
    assert ans5[0].why[0] == '>B1'

    ans6 = do_genfwdcompose(s_np__s_np, s_np_s)
    assert len(ans6) == 1
    assert str(ans6[0].cat) == '((S/NP)/S)'
    assert str(ans6[0].sem) == 'λa.f(g(a))'
    assert ans6[0].why[0] == '>B1'

    ans7 = do_genfwdcompose(s_np__s_np, s_np_s_np)
    assert len(ans7) == 1
    assert str(ans7[0].cat) == '(((S/NP)/S)/NP)'
    assert str(ans7[0].sem) == 'λa1.λa0.f(g(a1)(a0))'
    assert ans7[0].why[0] == '>B2'

    ans8 = do_genfwdcompose(s_np__s_np, s_np__s_np)
    assert len(ans8) == 1
    assert str(ans8[0].cat) == '((S/NP)/(S/NP))'
    assert str(ans8[0].sem) == 'λa.f(g(a))'
    assert ans8[0].why[0] == '>B1'

    ans9 = do_genfwdcompose(s_np__s_np, s_np)
    assert len(ans9) == 1
    assert str(ans9[0].cat) == '(S/NP)'
    assert str(ans9[0].sem) == 'f(g)'
    assert ans9[0].why[0] == '>B0'


parsingRules = [[typeraise_simple],
                [forward_application,
                 backward_application,
                 forward_composition]]


"""
parsingRules = [[typeraise_simple],
                [backward_application,
                 generalized_forward_composition]]
"""
