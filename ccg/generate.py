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

USE_PICKLES = False

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
hierarchies = {}
lexicon_hash = -1


def reset(filename):
    global inhabited, lexicon_hash

    inhabited1 = collections.defaultdict(set)
    if USE_CCGBANK_LEXICON:
        cat_dict = ccgbank.process_lexicon(
            'data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon', 50)
        for s in cat_dict.keys():
            cat = catparser.catparser.parse(s)
            if cat is not None:
                inhabited1[cat].add('LEX')
            else:
                print("oops: ", s)
    else:
        lexicon_data = open(filename).read().splitlines()
        lexicon = catparser.do_parses(lexicon_data)[0]
        for infos in lexicon.values():
            for cat, _ in infos:
                inhabited1[cat].add('LEX')

    type_raised = []
    for cat in inhabited1.keys():
        # if not cat.closed:
        #    continue
        type_raised += typeraise(cat, [])
    for cat, rule, _ in type_raised:
        inhabited1[cat].add(rule)

    inhabited = {1: inhabited1}

    cat_names = [category.alpha_normalized_string(cat)
                 for cat in inhabited1.keys()]
    cat_names.sort(key=len)
    print(", ".join(cat_names))
    lexicon_hash = zlib.adler32(";".join(cat_names).encode('utf8'))
    print(lexicon_hash)


categories_seen = set()


def populate_inhabited(filename, n):
    global inhabited, hierarchies, categories_seen
    global SKIP_NONNORMAL, NO_DOUBLE_TYPERAISE
    SKIP_NONNORMAL = False
    NO_DOUBLE_TYPERAISE = False

    print(f"inhabited({n}) starting")

    if n == 1:
        reset(filename)
        inhabited_n = inhabited[1]
        productions_n = {cat: [([], 'LEX')] for cat in inhabited_n.keys()}
    else:
        pickle_file = f'pickles/inhabited.{lexicon_hash}.{n}.out'
        if USE_PICKLES and os.path.isfile(pickle_file):
            with open(pickle_file, 'rb') as f:
                print("...recovering from pickle file...")
                inhabited_n = pickle.load(f)
        else:
            inhabited_n = collections.defaultdict(set)
            productions_n = collections.defaultdict(list)
            for k in range(1, n):
                cats_left = hierarchies[k]
                cats_right = hierarchies[n-k]
                for cat, rule, whence in forward_applies(cats_left, cats_right):
                    #print(cat, rule, [str(x) for x in whence])
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))
                for cat, rule, whence in backward_applies(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))
                for cat, rule, whence in forward_composition1(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))
                for cat, rule, whence in forward_composition2(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))
                for cat, rule, whence in forward_composition3(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))
                for cat, rule, whence in backward_composition1(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))

                for cat, rule, whence in backwards_cross_compose(cats_left, cats_right):
                    inhabited_n[cat].add(rule)
                    productions_n[cat].append((whence, rule))

            type_raised = []
            for cat in inhabited_n.keys():
                # if not cat.closed:
                #    continue
                type_raised += typeraise(cat, [])
            for cat, rule, whence in type_raised:
                inhabited_n[cat].add(rule)
                productions_n[cat].append((whence, rule))

            os.makedirs('pickles', exist_ok=True)
            with open(pickle_file, 'wb') as f:
                pickle.dump(inhabited_n, f)

    inhabited[n] = inhabited_n
    print(f"inhabited({n}) done. Found {len(inhabited_n)} categories")

    # What's new?
    these_categories = set(inhabited_n.keys())
    new_categories = list(these_categories - categories_seen)
    new_categories.sort(key=lambda c: len(str(c)))
    print(" new categories include: ")
    for cat in new_categories[:25]:
        for operands, rule in productions_n[cat]:
            print(
                f"    {cat}    {'  '.join([category.alpha_normalized_string(c) for c in operands])}   {rule}")
    categories_seen.update(these_categories)
    # print(pp_info(inhabited_n))

    hierarchies[n] = make_hierarchy(inhabited_n)


def forward_applies(cats_left, cats_right):
    global hierarchies
    results = []

    for cat1 in cats_left.has_slash[slash.RAPPLY].without_rules({'>T'}).all:
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

    for cat2 in cats_right.has_slash[slash.LAPPLY].without_rules({'<T'}).all:
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

    for cat1 in cats_left.has_slash[slash.RCOMPOSE].all:
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

    for cat1 in cats_left.has_slash[slash.RCOMPOSE].all:
        common_shape = cat1.dom.shape
        assert(common_shape is not None)
        cats2 = cats_right.left.has_slash[slash.RCOMPOSE].left.with_shape[common_shape].all
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

    for cat1 in cats_left.has_slash[slash.RCOMPOSE].all:
        common_shape = cat1.dom.shape
        assert(common_shape is not None)
        cats2 = cats_right.left.left.has_slash[slash.RCOMPOSE] \
            .left.with_shape[common_shape].all
        for cat2 in cats2:
            sub = cat2.cod.cod.cod.sub_unify(cat1.dom)
            if sub is not None:
                primary = cat1.subst(sub)
                secondary = cat2.subst(sub)
                composition = \
                    category.SlashCategory(
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

    for cat1 in cats_left.has_slash[slash.LCOMPOSE].all:
        common_shape = cat1.cod.shape
        assert(common_shape is not None)
        cats2 = cats_right.has_slash[slash.LCOMPOSE] \
            .right.with_shape[common_shape].all
        for cat2 in cats2:
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


def try_backward_compose(left, left_rules, right, right_rules):
    """Consider the given combination of categories to see if
        application might be possible(in the appropriate order,
        depending on the direction of the functor's slash)"""
    if isinstance(left, category.SlashCategory) \
            and isinstance(right, category.SlashCategory):
        # Try backward composition
        if (left.slash <= slash.LCOMPOSE) and \
                (right.slash <= slash.LCOMPOSE):
            # shape is right. Do they match up?
            sub = left.cod.sub_unify(right.dom)
            if sub is None:
                return []

            primary = right.subst(sub)
            secondary = left.subst(sub)
            composition = category.SlashCategory(
                primary.cod,
                secondary.slash,
                secondary.dom)
            rule = '<B'

            # self.__graph[composition].update([primary, secondary])
            return [(composition, rule, (secondary, primary))]

    return []


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

    generic_S = category.BaseCategory('S', semantic_types.t,
                                      pyrsistent.m(it=category.Metavar('X')))
    assert(not generic_S.closed)

    if cat.sub_unify(category.NP) is not None:
        answer = [mk_fwd(generic_S), mk_back(generic_S),
                  mk_fwd(category.SlashCategory(
                      generic_S, slash.LSLASH, category.NP)),
                  mk_fwd(category.SlashCategory(
                      generic_S, slash.LSLASH, category.NP))]
        assert(all(not x[0].closed for x in answer))

        return answer

    if cat.sub_unify(category.PP) is not None:
        return [mk_fwd(category.S), mk_back(category.S)]

    return []

    # self.__graph[fwd].add(cat)
    # self.__graph[back].add(cat)
    # return [(fwd, '>T', (cat,)), (back, '<T', (cat,))]


"""
class CategoryEnumerator:
    def __init__(self, filename):
        global DEBUG

        if USE_CCGBANK_LEXICON:
            cat_dict = ccgbank.process_lexicon(
                'data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon', 500)
            self.__original_cats = set()
            for s in cat_dict.keys():
                cat = catparser.catparser.parse(s)
                if cat is not None:
                    self.__original_cats.add(cat)
                else:
                    print("oops: ", s)
        else:
            lexicon_data = open(filename).read().splitlines()
            lexicon = catparser.do_parses(lexicon_data)[0]
            self.__original_cats = set(
                cat for infos in lexicon.values() for cat, _ in infos)

        # XX XXX: For now, assume there are no singletons!
        # self.__singletons = set()
        # for cat in all_cats:
        #     self.add_singletons(cat)
        # for word in self.__singletons:
        #    self.__rules.append(Rule(category.SingletonCategory(word), [word]))

        worklist = []  # empty heap!

        self.__graph = collections.defaultdict(set)

        # map from category to
        #   map from creating rules to justifications
        self.__categories = collections.defaultdict(
            lambda: collections.defaultdict(list))

        # initialize worklist with lexical itmes
        self.add_to_worklist(
            [(cat, 'LEX', ['-']) for cat in self.__original_cats],
            worklist)

        # map of categories to rules
        #   (specifically, all the data we've pulled off the worklist)
        processed = collections.defaultdict(list)

        num_heappops = 0
        while worklist:
            new, new_rule = heapq.heappop(worklist).data
            processed[new].append(new_rule)
            if not new.closed:
                new = new.refresh()
            # if "/*" in new_str or "\\*" in new_str:
            #     DEBUG = True
            if VERBOSE:
                num_heappops += 1
                print(f"{new} {new_rule} ({num_heappops})")
            for old, old_rules in processed.items():
                # print(f"    {old} {old_rules}")
                delta = []
                if old != new:
                    if DEBUG:
                        print(
                            f"trying rule order {old} {old_rules} {new} {new_rule}")
                    delta += self.try_rules(old, old_rules, new, [new_rule])
                    if DEBUG:
                        print(
                            f"trying rule order {new} {new_rule} {old} {old_rules} ")
                    delta += self.try_rules(new, [new_rule], old, old_rules)
                else:
                    new2 = new if new.closed else new.refresh()
                    delta += self.try_rules(old,
                                            old_rules, new2, [new_rule])

                if delta:
                    if DEBUG:
                        print(f'    vs. {old}')
                        print("      adding: ", ", ".join([category.alpha_normalized_string(c) + " " + r + " " + pp_info(info)
                                                           for c, r, info in delta]))

                    self.add_to_worklist(delta, worklist)

            delta = self.typeraise(new, [new_rule])
            if DEBUG:
                print("  adding: ", ", ".join(
                    [category.alpha_normalized_string(c) + " " + r
                     for c, r, _ in delta]))
            self.add_to_worklist(delta, worklist)

            if num_heappops > MAX_CATEGORIES_GEN:
                print("...etc...")
                break

            # DEBUG = False

    def print_inhabited(self):
        if (MAX_CATEGORIES_SHOW == 0):
            return

        print("\n\nINHABITED CATEGORIES\n")

        for c, infomap in self.__categories.items():
            print(c)
            for rule, reasons in infomap.items():
                print(f'  {rule}')
                for reason in reasons:
                    print(f'    {"  ".join(str(cat) for cat in reason)}')
        exit(0)

        inhabited = [(category.alpha_normalized_string(c),
                      ", ".join(" ".join([key]+values for key, values in infomap.items())))
                     for c, infomap in self.__categories.items()][:MAX_CATEGORIES_SHOW]

        inhabited.sort(key=lambda x: sort_key(x[0]))
        for s, rule in inhabited:
            print(s, "\t", rule)
        print(len(inhabited), "/", len(self.__categories))

    def add_to_worklist(self, cat_rule_info_list, worklist):
        for cat, rule, info in cat_rule_info_list:
            if (self.__categories[cat][rule] == []):
                heapq.heappush(worklist, HeapItem(cat, rule))
            self.__categories[cat][rule].append(info)

    def print_graph(self):
        for start, ends in self.__graph.items():
            for end in ends:
                print(f'{start} -> {end}')

    def bfs(self):
        print("\n\nUseful (reachable) inhabited categories from S\n")

        print(f'for constructing S   : {self.__graph[category.S]}')
        # print(f'for constructing S/NP: {self.__graph[category.]}')

        visited = set()
        queue = [category.S]

        while queue:
            next = queue.pop(0)
            if next in visited:
                continue

            visited.add(next)
            queue += list(self.__graph[next])

        all_visited = [str(c) for c in visited]
        all_visited.sort(key=sort_key)
        print(all_visited)
        for cat in all_visited:
            print(cat)
        print(len(all_visited))
"""


def test_lexicon(filename):

    for n in range(1, 5):
        populate_inhabited(filename, n)

    # for c in inhabited[2]:
    #     print(c)

    for n in range(1, len(inhabited)+1):
        all_rules = set()
        for rules in inhabited[n].values():
            all_rules.update(rules)
        print(f"{n} words : {len(inhabited[n])} categories via "
              f"{', '.join(sorted(list(all_rules)))}")


if __name__ == '__main__':
    random.seed()
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
