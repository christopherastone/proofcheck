import catparser
import category
import catset
import ccgbank
import collections
import functools
import heapq
import math
import os
import pickle
import pyrsistent
import random
import re
import semantic_types
import slash
import sys
import zlib

DEBUG = False
VERBOSE = True
MAX_CATEGORIES_GEN = 50
MAX_CATEGORIES_SHOW = 100
SKIP_NONNORMAL = True
MAX_COMPOSITION_ORDER = 3
SHOW_WHATS_NEW = True
ALSO_SHOW_WHATS_MISSING = True
DO_TYPERAISE = True

USE_PICKLES = False   # breaks things, because hashes are nondeterministic!

STRIP_ATTRIBUTES = True

assert(MAX_COMPOSITION_ORDER >= 1)

USE_CCGBANK_LEXICON = True


slashre = re.compile(r'[/|\\]')


def sort_key(s):
    s_nondirected, num_slashes = re.subn(slashre, "|", s)
    return (num_slashes, len(s), s_nondirected, s)


def pp_info(cats):
    strs = [category.alpha_normalized_string(cat) for cat in cats]
    strs.sort(key=lambda s: (len(s), s))
    return "  ".join(strs)


def make_hierarchy(cat_to_rules):
    return catset.CatSet([(cat, cat, rules)
                          for cat, rules in cat_to_rules.items()])


# mapping from level number n to the set of
#    categories inhabited by (1 or more) n-word phrase
inhabited = {}
productions = {}
hierarchies = {}
lexicon_hash = -1


def reset(filename):
    global inhabited, productions, lexicon_hash

    inhabited1 = collections.defaultdict(set)
    productions1 = collections.defaultdict(set)
    if USE_CCGBANK_LEXICON:
        cat_dict = ccgbank.process_lexicon(
            'data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon')
        for _, s in ccgbank.categories_by_all_words(cat_dict)[:44]:
            cat = catparser.catparser.parse(s)
            if cat is not None:
                if STRIP_ATTRIBUTES:
                    cat = category.strip_attributes(cat)
                inhabited1[cat].add('LEX')
                productions1[cat].add((tuple(), 'LEX'))
            else:
                print("oops: ", s)
    else:
        lexicon_data = open(filename).read().splitlines()
        lexicon = catparser.do_parses(lexicon_data)[0]
        for infos in lexicon.values():
            for cat, _ in infos:
                if STRIP_ATTRIBUTES:
                    cat = category.strip_attributes(cat)
                inhabited1[cat].add('LEX')
                productions1[cat].add((tuple(), 'LEX'))

    if DO_TYPERAISE:
        type_raised = []
        for cat in inhabited1.keys():
            # if not cat.closed:
            #    continue
            type_raised += typeraise(cat, [])
        for cat, rule, whence in type_raised:
            inhabited1[cat].add(rule)
            productions1[cat].add((tuple(whence), rule))

    inhabited = {1: inhabited1}
    productions = {1: productions1}

    cat_names = [category.alpha_normalized_string(cat)
                 for cat in inhabited1.keys()]
    cat_names.sort(key=len)
    print(", ".join(cat_names))
    lexicon_hash = zlib.adler32(";".join(cat_names).encode('utf8'))
    print(lexicon_hash)


categories_seen = set()


def populate_inhabited(filename, max_n):
    global inhabited, hierarchies, categories_seen

    for n in range(1, max_n + 1):
        print(f"inhabited({n}) starting")

        if n == 1:
            reset(filename)
            inhabited_n = inhabited[1]
            productions_n = productions[1]
        else:
            pickle_file = f'pickles/inhabited.{lexicon_hash}.{n}.out'
            if USE_PICKLES and os.path.isfile(pickle_file):
                with open(pickle_file, 'rb') as f:
                    print("...recovering from pickle file...")
                    (inhabited_n, productions_n) = pickle.load(f)
            else:
                inhabited_n = collections.defaultdict(set)
                productions_n = collections.defaultdict(set)
                for k in range(1, n):
                    cats_left = hierarchies[k]
                    cats_right = hierarchies[n-k]

                    def run_rule(rule_fn):
                        #print(f"run rule {rule_fn.__name__} for {k} and {n-k}")
                        nonlocal cats_left, cats_right
                        nonlocal inhabited_n, productions_n
                        for cat, rule, whence in rule_fn(cats_left, cats_right):
                            #print(n, cat, rule, [str(x) for x in whence])
                            inhabited_n[cat].add(rule)
                            productions_n[cat].add((tuple(whence), rule))

                    run_rule(forward_applies)
                    run_rule(backward_applies)
                    run_rule(forward_composition1)
                    run_rule(forward_composition2)
                    run_rule(forward_composition3)
                    run_rule(backward_composition1)
                    run_rule(backwards_cross_compose)

                type_raised = []
                for cat in inhabited_n.keys():
                    # if not cat.closed:
                    #    continue
                    type_raised += typeraise(cat, [])
                for cat, rule, whence in type_raised:
                    inhabited_n[cat].add(rule)
                    productions_n[cat].add((tuple(whence), rule))

                os.makedirs('pickles', exist_ok=True)
                with open(pickle_file, 'wb') as f:
                    pickle.dump((inhabited_n, productions_n), f)

        inhabited[n] = inhabited_n
        productions[n] = productions_n

        print(f"inhabited({n}) done. Found {len(inhabited_n)} categories")

        # What's new?
        if SHOW_WHATS_NEW:
            these_categories = set(inhabited_n.keys())
            new_categories = list(these_categories - categories_seen)
            #new_categories = list(these_categories)

            new_categories.sort(key=lambda c: sort_key(str(c)))

            print(" new categories include: ")
            for cat in new_categories[:25]:
                for operands, rule in productions_n[cat]:
                    print(
                        f"    {cat}    {'  '.join([category.alpha_normalized_string(c) for c in operands])}   {rule}")

            missing_categories = list(categories_seen - these_categories)
            if ALSO_SHOW_WHATS_MISSING and missing_categories:
                print(" missing categories include ",
                      ",  ".join([category.alpha_normalized_string(c) for c in missing_categories]))

            categories_seen.update(these_categories)

        #print("these categories", pp_info(inhabited_n))

        hierarchies[n] = make_hierarchy(inhabited_n)

        production_graph = build_graph(productions)
        visited = bfs(production_graph)

    with open('rules.out', 'w') as f:
        for cat in visited:
            #print(f"rules for category {cat}")
            for whence, rule in set.union(*[productions[n][cat] for n in range(1, max_n+1)]):
                whence_s = [
                    category.alpha_normalized_string(c) for c in whence]
                f.write(f"{cat} -> {' '.join(whence_s)}  {rule}\n")

    with open('rules.noncircular.out', 'w') as f:
        for cat in visited:
            #print(f"rules for category {cat}")
            for whence, rule in set.union(*[productions[n][cat] for n in range(1, max_n+1)]):
                if cat in whence:
                    continue
                whence_s = [
                    category.alpha_normalized_string(c) for c in whence]
                f.write(f"{cat} -> {' '.join(whence_s)}  {rule}\n")

    return productions


def forward_applies(cats_left, cats_right):
    results = []

    if SKIP_NONNORMAL:
        cats1 = cats_left.has_slash[slash.RAPPLY] \
            .without_rules({'>T', '>B', '>B1', '>B2', '>B3', '>B4'}).all
    else:
        cats1 = cats_left.has_slash[slash.RAPPLY].all
    for cat1 in cats1:
        if cat1.dom.shape is not None:
            cats2 = cats_right.with_shape[cat1.dom.shape].all + \
                cats_right.with_shape[None].all
        else:
            cats2 = cats_right.all
        for cat2 in cats2:
            sub = cat2.sub_unify(cat1.dom)
            if sub is not None:
                functor = cat1.subst(sub)
                argument = cat2.subst(sub)
                result = functor.cod
                rule = '>'
                # self.__graph[result].update([functor, argument])
                results.append((result, rule, (functor, argument)))
                # print(f"AFA applying {functor} to {argument}")
                # if cat1.closed:
                # If the functor was closed, all we care about
                # is finding *one* valid argument. Other
                # valid sub-categories just give us the same
                # value for result.
                # break

    return results


def backward_applies(cats_left, cats_right):
    results = []

    if SKIP_NONNORMAL:
        cats2 = cats_right.has_slash[slash.LAPPLY].\
            without_rules({'<T', '<B', '<B1', '<B2', '<B3', '<B4'}).all
    else:
        cats2 = cats_right.has_slash[slash.LAPPLY].all

    for cat2 in cats2:
        if cat2.dom.shape is not None:
            cats1 = cats_left.with_shape[cat2.dom.shape].all + \
                cats_left.with_shape[None].all
        else:
            cats1 = cats_left.all
        for cat1 in cats1:
            sub = cat1.sub_unify(cat2.dom)
            if sub is not None:
                functor = cat2.subst(sub)
                argument = cat1.subst(sub)
                result = functor.cod
                # self.__graph[result].update([functor, argument])
                results.append((result, '<', (argument, functor)))
                # print(f"ABA passing {argument} to {functor}")
                # if cat2.closed:
                # If the functor was closed, all we care about
                # is finding *one* valid argument. Other
                # valid sub-categories just give us the same
                # value for result.
                # break

    return results


def forward_composition1(cats_left, cats_right):
    results = []

    cats1 = cats_left.has_slash[slash.RCOMPOSE]
    if SKIP_NONNORMAL:
        cats1 = cats1.without_rules({'>B', '>B1', '>B2', '>B3', '>B4'})

    for cat1 in cats1.all:
        common_shape = cat1.dom.shape
        assert(common_shape is not None)

        cats2 = cats_right.has_slash[slash.RCOMPOSE] \
            .left.with_shape[common_shape].all
        for cat2 in cats2:
            sub = cat2.cod.sub_unify(cat1.dom)
            if sub is not None:
                primary = cat1.subst(sub)
                secondary = cat2.subst(sub)
                composition = category.SlashCategory(
                    primary.cod,
                    secondary.slash,
                    secondary.dom)
                results.append(
                    (composition, '>B', (primary, secondary)))
                # print(f"B1  {composition}  -->  "
                #       f"{primary} {secondary}")

    return results


def forward_composition2(cats_left, cats_right):
    results = []

    cats1 = cats_left.has_slash[slash.RCOMPOSE]
    if SKIP_NONNORMAL:
        cats1 = cats1.without_rules({'>B', '>B1'})

    for cat1 in cats1.all:
        common_shape = cat1.dom.shape
        assert(common_shape is not None)

        cats2 = cats_right.left.has_slash[slash.RCOMPOSE] \
            .left.with_shape[common_shape].all
        for cat2 in cats2:
            sub = cat2.cod.cod.sub_unify(cat1.dom)
            if sub is not None:
                primary = cat1.subst(sub)
                secondary = cat2.subst(sub)
                composition = category.SlashCategory(
                    category.SlashCategory(
                        primary.cod, secondary.cod.slash, secondary.cod.dom),
                    secondary.slash, secondary.dom)
                results.append(
                    (composition, '>B2', (primary, secondary)))

    return results


def forward_composition3(cats_left, cats_right):
    results = []

    cats1 = cats_left.has_slash[slash.RCOMPOSE]
    if SKIP_NONNORMAL:
        cats1 = cats1.without_rules({'>B', '>B1'})

    for cat1 in cats1.all:
        common_shape = cat1.dom.shape
        assert(common_shape is not None)
        cats2 = cats_right.left.left.has_slash[slash.RCOMPOSE] \
            .left.with_shape[common_shape]
        if SKIP_NONNORMAL:
            cats2 = cats2.without_rules({'>B2'})
        for cat2 in cats2.all:
            sub = cat2.cod.cod.cod.sub_unify(cat1.dom)
            if sub is not None:
                primary = cat1.subst(sub)
                secondary = cat2.subst(sub)
                composition = category.SlashCategory(
                    category.SlashCategory(
                        category.SlashCategory(
                            primary.cod, secondary.cod.cod.slash, secondary.cod.cod.dom),
                        secondary.cod.slash, secondary.cod.dom),
                    secondary.slash, secondary.dom)
                results.append(
                    (composition, '>B3', (primary, secondary)))

    return results


def backward_composition1(cats_left, cats_right):
    results = []

    cats2 = cats_right.has_slash[slash.LCOMPOSE]
    if SKIP_NONNORMAL:
        cats2 = cats2.without_rules({'<B', '<B1', '<B2', '<B3', '<B4'})

    for cat2 in cats2.all:
        common_shape = cat2.dom.shape
        assert(common_shape is not None)
        cats1 = cats_left.has_slash[slash.LCOMPOSE] \
            .left.with_shape[common_shape]
        for cat1 in cats1.all:
            sub = cat1.cod.sub_unify(cat2.dom)
            if sub is not None:
                secondary = cat1.subst(sub)
                primary = cat2.subst(sub)
                composition = category.SlashCategory(
                    primary.cod,
                    secondary.slash,
                    secondary.dom)
                results.append(
                    (composition, '<B', (secondary, primary)))
                # print(f"B1  {composition}  -->  "
                #       f"{primary} {secondary}")

    return results


def backwards_cross_compose(cats_left, cats_right):
    results = []

    for cat1 in cats_left.has_slash[slash.RCROSS].without_rules({'>T'}).all:
        common_shape = cat1.cod.shape
        assert(common_shape is not None)
        cats2 = cats_right.has_slash[slash.LCROSS]. \
            right.with_shape[common_shape].all
        for cat2 in cats2:
            sub = cat1.cod.sub_unify(cat2.dom)
            if sub is not None:
                primary = cat2.subst(sub)
                secondary = cat1.subst(sub)
                composition = category.SlashCategory(
                    primary.cod, secondary.slash, secondary.dom)
                results.append(
                    (composition, '<Bx', (secondary, primary)))

    return results


def bad_compose(lrule, rrule, dir, compose_order):
    assert(compose_order >= 1)

    def extract_compose_order(rule, expected_dir=dir):
        if rule.startswith(expected_dir + 'B'):
            if len(rule) > 2:
                return int(rule[2:])
            else:
                return 1
        else:
            return None

    # H&F NF Constraint 1
    left_order = extract_compose_order(lrule)
    if (compose_order == 1 and
        left_order is not None and
            left_order >= 1):
        return True

    # H&F NF Constraint 2
    if (left_order is not None and
            left_order == 1):
        return True

    # H&F NF Constraint 3
    right_order = extract_compose_order(rrule)
    if (right_order is not None and
        right_order > 1 and
            compose_order > right_order):
        return True

    # H&F NF Constraint 4
    if lrule == '>T':
        right_order_rev = extract_compose_order(
            rrule, '>' if dir == '<' else '<')
        if (right_order_rev is not None and
                right_order_rev > compose_order):
            return True

    return False


def typeraise(cat, rules):
    def mk_fwd(t):
        return (category.SlashCategory(
            t, slash.RSLASH, category.SlashCategory(
                t, slash.LSLASH, cat)), ">T", [t])

    def mk_back(t):
        return (category.SlashCategory(
            t, slash.LSLASH, category.SlashCategory(
                t, slash.RSLASH, cat)), "<T", [t])

    if STRIP_ATTRIBUTES:
        generic_S = category.S
    else:
        generic_S = category.BaseCategory('S', semantic_types.t,
                                          pyrsistent.m(it=category.Metavar('X')))

    if cat.sub_unify(category.NP) is not None:
        answer = [mk_fwd(generic_S), mk_back(generic_S),
                  mk_fwd(category.SlashCategory(
                      generic_S, slash.LSLASH, category.NP)),
                  mk_fwd(category.SlashCategory(
                      generic_S, slash.LSLASH, category.NP))]

        return answer

    if cat.sub_unify(category.PP) is not None:
        return [mk_fwd(category.S), mk_back(category.S)]

    return []

    # self.__graph[fwd].add(cat)
    # self.__graph[back].add(cat)
    # return [(fwd, '>T', (cat,)), (back, '<T', (cat,))]


def build_graph(productions):
    graph = collections.defaultdict(set)

    for n, productions_n in productions.items():
        for cat, sources in productions_n.items():
            for whence, rule in sources:
                graph[cat].update(whence)

    return graph


def bfs(production_graph):
    print("Useful (reachable) inhabited categories from S")

    # print(f'for constructing S   : {production_graph[category.S]}')
    print(
        f'for constructing S/NP: {" ".join([category.alpha_normalized_string(c) for c in production_graph[category.SlashCategory(category.S, slash.RSLASH, category.NP)]])}')

    visited = set()
    queue = [category.S]

    while queue:
        next = queue.pop(0)
        assert(isinstance(next, category.BaseCategory) or isinstance(
            next, category.SlashCategory) or isinstance(next, category.SingletonCategory))
        if next in visited:
            continue

        visited.add(next)
        queue += list(production_graph[next])

    all_visited = [category.alpha_normalized_string(c) for c in visited]
    all_visited.sort(key=sort_key)
    # print(all_visited)
    print('   ', '  '.join(all_visited[:100]))
    print('   ', len(all_visited))

    return visited


def test_lexicon(filename):

    productions = populate_inhabited(filename, 10)

    # for c in inhabited[2]:
    #     print(c)

    for n in range(1, len(inhabited)+1):
        all_rules = set()
        for rules in inhabited[n].values():
            all_rules.update(rules)
        print(f"{n} words : {len(inhabited[n])}/{len(categories_seen)} categories via "
              f"{', '.join(sorted(list(all_rules)))}")


if __name__ == '__main__':
    random.seed()
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('demo.txt')
