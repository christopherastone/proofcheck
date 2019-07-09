"""
CCG Combinatory Rules
"""

import functools

import category
import catparser
import semantics
import slash
from item import Item


def deconstruct(item1, item2):
    return (item1.cat, item1.sem, item2.cat, item2.sem)


#######################
# FORWARD APPLICATION #
#######################

#   A /* B   B
#     f      b
#  ------------ >  [a.k.a. >B0]
#       A
#      f(b)

#  But as a special case (i.e., the right-hand-side of and/or)
#  we rename the rule:

#   A /Φ B   B
#     f      b
#  ------------ >Φ
#       A
#      f(b)

# And as an even more special case (i.e., when the right-hand-side
# of an and/or was type-raised)

#              B
#              b
#             --- ≷T
#   A /Φ ↑B   ↑B
#     f       ↑b
#  ------------ >ΦT
#       A
#      f(↑b)

# UNFORTUNATELY, THIS ΦT labeling DOESN'T WORK AS WELL AS WE MIGHT HOPE, e.g.

#  In "met and marry" it can detect if met and marry are both lifted before the
#  conjunction, (and so the result of the composition shouldn't be applied
#  with an argument, because lifting + application just reverses a
#  pre-existing possible application)

#  But "met and might marry" where "might marry" has an intermediate
#  >B composition step, which can hide the fact that marry was
#  (unnecessarily) lifted.


def forward_application(item1, item2, dest):
    cat1, sem1, cat2, sem2 = deconstruct(item1, item2)
    # print(f'forward_application trying {cat1} @ {cat2}')
    if not (isinstance(cat1, category.SlashCategory) and
            # XXX: ^^^ overspecific, but only if we want to apply metavars.
            slash.RSLASH <= cat1.slash):
        # print(f' forward_application: nope 1')
        return False  # not a function, or not looking rightwards

    # NB: application is a special (zero-ary) case of composition,
    #     so we can use the same constraint checking-function.
    if compose_constraint_violation(item1, item2, 0, '>'):
        # print("forward application constraint violation")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '>'):
        return False

    sub = cat2.sub_unify(cat1.dom)
    if sub is None:
        # print(f'forward_application: {cat2} <= {cat1.dom}: nope 2')
        return False  # application category mismatch

    label = '>'
    if slash.PHI in cat1.slash.mode:
        label += slash.PHI
        if 'T' in item2.why[0]:
            label += 'T'

    dest += [Item(cat1.cod,
                  semantics.App(sem1, sem2).reduce(),
                  [label, item1, item2]).subst(sub)]
    return True

########################
# BACKWARD APPLICATION #
########################

#   B    A \* B
#   b      f
#  ------------ >  [a.k.a. <B0]
#       A
#      f(b)

#  But as a special case (i.e., the left-hand-side of and/or)
#  we rename the rule:

#   B    A \Φ B
#   b      f
#  ------------ <Φ
#       A
#      f(b)

# And as an even more special case (i.e., when the right-hand-side
# and the left-hand-side were both type-raised)

#     B
#     b
#    --- ≷T  -------- <ΦT
#     ↑B      A \Φ ↑B
#     ↑b         f
#  -------------------- <ΦT
#       A
#      f(↑b)


def backward_application(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not (isinstance(cat2, category.SlashCategory) and
            slash.LSLASH <= cat2.slash):
        return False  # not a function, or not looking leftwards

    if compose_constraint_violation(item2, item1, 0, '<'):
        # print(f"backward constraint violated; skipping")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '<'):
        return False

    sub = cat1.sub_unify(cat2.dom)
    if sub is None:
        return False  # application category mismatch

    label = '<'
    if slash.PHI in cat2.slash.mode:
        label += slash.PHI
        if 'T' in item1.why[0] and 'T' in item2.why[0]:
            label += 'T'

    dest += [Item(cat2.cod,
                  semantics.App(sem2, sem1).reduce(),
                  [label, item1, item2]).subst(sub)]
    return True


def forward_composition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.RCOMPOSE and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.RCOMPOSE):
        return False  # not both rightwards functions

    if compose_constraint_violation(item1, item2, 1, '>'):
        # print("forward composition constraint violation")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '>B'):
        return False

    sub = cat2.cod.sub_unify(cat1.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat2.slash
    dest += (
        [Item(category.SlashCategory(cat1.cod, final_slash, cat2.dom),
              semantics.Lam(
                "z",
                semantics.App(
                    sem1,
                    semantics.App(
                        sem2,
                        semantics.BoundVar(0))).reduce()),
                ['>B', item1, item2]).subst(sub)])
    return True


def forward_composition2(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.RCOMPOSE and
           isinstance(cat2, category.SlashCategory) and
           isinstance(cat2.cod, category.SlashCategory) and
           cat2.cod.slash <= slash.RCOMPOSE):
        return False  # not both rightwards functions

    if compose_constraint_violation(item1, item2, 2, '>'):
        # print("forward composition constraint violation")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '>B2'):
        return False

    sub = cat2.cod.cod.sub_unify(cat1.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat2.cod.slash
    dest += (
        [Item(category.SlashCategory(
            category.SlashCategory(cat1.cod, final_slash, cat2.cod.dom),
            cat2.slash,
            cat2.dom),
            (semantics.Lam(
                "w",
                semantics.Lam(
                    "z",
                    semantics.App(
                        sem1,
                        semantics.App(
                            semantics.App(
                                sem2,
                                semantics.BoundVar(1)),
                            semantics.BoundVar(0))))).reduce()),
            ['>B2', item1, item2]).subst(sub)])
    return True


def backwards_composition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.LCOMPOSE and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.LCOMPOSE):
        return False  # not both leftwards functions

    if compose_constraint_violation(item2, item1, 1, '<'):
        # print("<B constraint violation")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '<B1'):
        return False

    sub = cat1.cod.sub_unify(cat2.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat1.slash
    dest += (
        [Item(category.SlashCategory(cat2.cod, final_slash, cat1.dom),
              semantics.Lam(
                "z",
                semantics.App(
                    sem2,
                    semantics.App(
                        sem1,
                        semantics.BoundVar(0))).reduce()),
                ['<B', item1, item2]).subst(sub)])
    return True


def backwards_composition2(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           isinstance(cat1.cod, category.SlashCategory) and
           cat1.cod.slash <= slash.LCOMPOSE and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.LCOMPOSE):
        return False  # not both leftwards functions

    if compose_constraint_violation(item2, item1, 2, '<'):
        # print("<B constraint violation")
        # print(item1)
        # print(item2)
        # print()
        return False

    if forbidden_combination(item1.why, item2.why, '<B2'):
        return False

    sub = cat1.cod.cod.sub_unify(cat2.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat1.cod.slash
    dest += (
        [Item(category.SlashCategory(
                        category.SlashCategory(
                            cat2.cod, final_slash, cat1.cod.dom),
                        cat1.slash,
                        cat1.dom),
              semantics.Lam(
                "w",
                semantics.Lam(
                    "z",
                    semantics.App(
                        sem2,
                        semantics.App(
                            semantics.App(
                                sem1,
                                semantics.BoundVar(1)),
                            semantics.BoundVar(0))))).reduce(),
              ['<B2', item1, item2]).subst(sub)])
    return True


def forward_crossed_composition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.mk_rslash(slash.ALLOWBX) and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.mk_lslash(slash.ALLOWBX)):
        return False  # not appropriate slash categories

    if compose_constraint_violation(item1, item2, 1, '>'):
        return False

    if forbidden_combination(item1.why, item2.why, '>Bx'):
        return False

    sub = cat2.cod.sub_unify(cat1.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat2.slash
    dest += (
        [Item(category.SlashCategory(cat1.cod, final_slash, cat2.dom),
              semantics.Lam(
                "z",
                semantics.App(
                    sem1,
                    semantics.App(
                        sem2,
                        semantics.BoundVar(0))).reduce()),
                ['>Bx', item1, item2]).subst(sub)])
    return True


def backwards_crossed_composition(item1, item2, dest):
    (cat1, sem1, cat2, sem2) = deconstruct(item1, item2)

    if not(isinstance(cat1, category.SlashCategory) and
           cat1.slash <= slash.mk_rslash(slash.ALLOWBX) and
           isinstance(cat2, category.SlashCategory) and
           cat2.slash <= slash.mk_lslash(slash.ALLOWBX)):
        return False  # not both leftwards functions

    if compose_constraint_violation(item2, item1, 1, '<'):
        return False

    if forbidden_combination(item1.why, item2.why, '<Bx'):
        return False

    sub = cat1.cod.sub_unify(cat2.dom)
    if sub is None:
        return False  # not composeable

    final_slash = cat1.slash
    dest += (
        [Item(category.SlashCategory(cat2.cod, final_slash, cat1.dom),
              semantics.Lam(
                "z",
                semantics.App(
                    sem2,
                    semantics.App(
                        sem1,
                        semantics.BoundVar(0))).reduce()),
                ['<Bx', item1, item2]).subst(sub)])
    return True


c_arg = [category.NP, category.S, category.VBI]


def typeraise_constraint_violation(item, dir='>'):
    # NF Constraint 6
    if slash.PHI in item.why[0]:
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
    # print("C AND C")
    if item.cat == category.NP:
        typeraise_right(category.S, item, dest)
        typeraise_left(category.VBI, item, dest),
        typeraise_left(category.VBT, item, dest),
        typeraise_left(
            # NP -> ((S\NP)/PP) \ ( ((S\NP)/PP) / NP )
            category.SlashCategory(category.VBI, slash.RSLASH, category.PP),
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
    DEBUG = False
    if DEBUG:
        print(f'ccv {item1.cat} {item2.cat} {n} {dir}')
    # Hockenmaier and Bisk NF Constraint 1:
    # Forbid
    #   X/A  A/Y[1..k]/C
    #   -------------- >B(k+1)
    #      X/Y[1..k]/C            C
    #   ------------------------------ > (aka B0)
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
            if item1.rule() not in [dir+'B0', dir]:
                if DEBUG:
                    print("constraint 1")
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
        if (item1.why and item1.why[0] in [dir+'B', dir+'B1']):
            if DEBUG:
                print("constraint 2")
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
            ((not item2.why[0][-1].isdigit() and 1 < n) or
             (item2.why[0][-1].isdigit() and int(item2.why[0][-1]) < n))):
        if DEBUG:
            print("constraint 3")
        return True

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

    if (n > 0):
        opdir = '<' if dir == '>' else '>'
        if (item1.why and item1.why[0].startswith(dir+'T') and
            item2.why and item2.why[0].startswith(opdir+'B') and
                item2.why[0][-1].isdigit() and int(item2.why[0][-1]) > n):
            if DEBUG:
                print("constraint 4")
            return True

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
        if item1.why and item1.why[0].startswith(dir + 'T'):
            if DEBUG:
                print("constraint 5")
            return True

    # print("no constraint")
    return False

def forbidden_combination(why_left, why_right, conclusion_rulename):
    #
    #  Hockenmaier and Bisk 2004, page 467
    #
    # In order to prevent overgenerations of the form
    # "John speaks because Chinese, he enjoys Beijing.",
    # we assume a variant of CCG in which forward crossing
    # composition >Bx (e.g. of because:(S/S)/S) into
    # the result of backward type-raising <T
    # (e.g. Chinese:S\(S/NP)) ... are disallowed

    #                     A
    #                 ----------- <T
    #    X / Y        Y \ (Y / A)
    #   -------------------------- >Bx
    #         X \ (Y / A)

    if why_right is not None and \
        why_right[0].startswith('<T') and \
            conclusion_rulename.startswith('>Bx'):
        return True

    # and, similarly, <Bx into the result of >T [is] disallowed.
    #  (I think they mean <Bx, not <B^n, but there's a typo
    #  where they wrote <B^x. And I think "into" means
    #  the left premise)

    #        A
    #   ------------ >T
    #    Y / (Y \ A)           X \ Y
    #   ------------------------------ <Bx
    #             X / (Y \ A)

    if why_left is not None and \
        why_left[0].startswith('>T') and \
        conclusion_rulename.startswith('<Bx'):
        return True

    # otherwise, seems OK
    return False

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


parsingRules = [[typeraise_generic],
                [forward_application,
                 backward_application,
                 forward_composition,
                 forward_composition2,
                 backwards_composition,
                 backwards_composition2,
                 forward_crossed_composition,
                 backwards_crossed_composition]]


"""
parsingRules = [[typeraise_simple],
                [backward_application,
                 generalized_forward_composition]]
"""
