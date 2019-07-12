import catparser
import category
import collections
import functools
import heapq
import math
import random
import slash
import sys

DEBUG = False
VERBOSE = True
MAX_CATEGORIES_GEN = 200
MAX_CATEGORIES_SHOW = 50
SKIP_NONNORMAL = True


def count_slashes(s):
    return sum(c == '/' or c == '\\' for c in s)


class CategoryEnumerator:
    def __init__(self, filename):
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

        @functools.total_ordering
        class HeapItem:
            def __init__(self, cat, rule):
                self.data = (cat, rule)
                cat_s = category.alpha_normalized_string(cat)
                self.key = (count_slashes(cat_s), len(cat_s), cat_s, rule)

            def __eq__(self, other):
                return (isinstance(other, HeapItem) and
                        self.key == other.key)

            def __lt__(self, other):
                return (isinstance(other, HeapItem) and
                        self.key < other.key)

            def __str__(self):
                return f'{self.key[3]}'

        worklist = []  # empty heap!

        def add_to_worklist(cat_rule_list):
            nonlocal worklist
            for cat, rule in cat_rule_list:
                heapq.heappush(worklist, HeapItem(cat, rule))

        # initialize worklist with lexical itmes
        add_to_worklist([(cat, 'LEX') for cat in self.__original_cats])

        self.__graph = collections.defaultdict(set)

        # map from category to creating rules
        self.__categories = collections.defaultdict(set)

        # set of (category string, rule) pairs
        #   kept for improved redundency checks
        self.__redundant = set()
        num_heappops = 0
        while worklist:
            new, new_rule = heapq.heappop(worklist).data
            new = new.refresh()
            new_str = category.alpha_normalized_string(new)
            if (new_str, new_rule) in self.__redundant:
                if DEBUG:
                    print(f"    {new_str} is a duplicate for {new_rule}")
                continue
            self.__categories[new].add(new_rule)
            self.__redundant.add((new_str, new_rule))
            if VERBOSE:
                num_heappops += 1
                print(f"{new_str} {new_rule} ({num_heappops})")
            for old, old_rules in self.__categories.items():
                # print(f"    {old} {old_rules}")
                delta = []
                if not category.alpha_equal(old, new):
                    delta += self.try_rules(old, old_rules, new, [new_rule])
                    delta += self.try_rules(new, [new_rule], old, old_rules)
                else:
                    new2 = new.refresh()
                    delta += self.try_rules(old,
                                            old_rules, new2, [new_rule])

                if delta:
                    if DEBUG:
                        print(f'    vs. {old}')
                        print("      adding: ", ", ".join([category.alpha_normalized_string(c) + " " + r
                                                           for c, r in delta]))

                    add_to_worklist(delta)

            delta = self.typeraise(new)
            if DEBUG:
                print("  adding: ", ", ".join(
                    [category.alpha_normalized_string(c) + " " + r
                     for c, r in delta]))
            add_to_worklist(delta)

            if len(self.__categories) > MAX_CATEGORIES_GEN:
                print("...etc...")
                for w, r in [item.data for item in worklist]:
                    self.__categories[w].add(r)
                break

    def print_inhabited(self):
        if (MAX_CATEGORIES_SHOW == 0):
            return

        print("\n\nINHABITED CATEGORIES\n")

        inhabited = [(category.alpha_normalized_string(c), ", ".join(rs))
                     for c, rs in self.__categories.items()][:MAX_CATEGORIES_SHOW]

        def sort_key(s):
            num_slashes = sum(c == '/' or c == '\\' for c in s[0])
            return (num_slashes, len(s[0]), s)

        inhabited.sort(key=sort_key)
        for s, rule in inhabited:
            print(s, "\t", rule)
        print(len(inhabited), "/", len(self.__categories))

    def try_apply(self, left_cat, left_rules, right_cat, right_rules):
        """Consider the given combination of categories to see if
           application might be possible(in the appropriate order,
           depending on the direction of the functor's slash)"""
        assert(left_rules)
        if isinstance(left_cat, category.SlashCategory) and \
                left_cat.slash <= slash.RAPPLY:
            # Possible instance of >
            if SKIP_NONNORMAL and set(left_rules) <= {'>T', '>B'}:
                return []
            sub = right_cat.sub_unify(left_cat.dom)
            if sub is not None:
                functor = left_cat.subst(sub)
                argument = right_cat.subst(sub)
                result = functor.cod.subst(sub)
                rule = '>'
                functor_s = category.alpha_normalized_string(functor)
                argument_s = category.alpha_normalized_string(argument)
                result_s = category.alpha_normalized_string(result)
                if DEBUG:
                    print(f"    DEBUG trying {left_cat} {right_cat}")
                    print(f"          {functor_s} {argument_s} {rule}")
                    print(f"          {left_rules} {right_rules}")
                self.__graph[result_s].update([functor_s, argument_s])
                if (result_s, rule) not in \
                        self.__redundant:
                    return [(result, rule)]
                else:
                    if DEBUG:
                        print("      built duplicate: ",
                              category.alpha_normalized_string(result))

        if isinstance(right_cat, category.SlashCategory) and \
                right_cat.slash <= slash.LAPPLY:
            # possible instance of <
            if SKIP_NONNORMAL and set(right_rules) <= {'<T', '<B'}:
                return []
            sub = left_cat.sub_unify(right_cat.dom)
            if sub is not None:
                functor = right_cat.subst(sub)
                functor_s = category.alpha_normalized_string(functor)
                argument_s = \
                    category.alpha_normalized_string(left_cat.subst(sub))
                result = functor.cod.subst(sub)
                result_s = category.alpha_normalized_string(result)
                rule = '<'
                if DEBUG:
                    print(f"    DEBUG trying {left_cat} {right_cat} <")
                    print(f"          {argument_s} {functor_s}")
                    print(f"          {left_rules} {right_rules}")

                self.__graph[result_s].update([functor_s, argument_s])
                if (result_s, rule) in \
                        self.__redundant:
                    if DEBUG:
                        print("      built duplicate: ",
                              result_s, rule)

                    return []
                else:
                    return [(result, rule)]

        return []

    def try_compose(self, left_cat, left_rules, right_cat, right_rules):
        """Consider the given combination of categories to see if
           application might be possible(in the appropriate order,
           depending on the direction of the functor's slash)"""
        if isinstance(left_cat, category.SlashCategory) \
                and isinstance(right_cat, category.SlashCategory):
            # Try forward composition
            if (left_cat.slash <= slash.RCOMPOSE) and \
                    (right_cat.slash <= slash.RCOMPOSE):
                # shape is right. Do they match up?
                sub = right_cat.cod.sub_unify(left_cat.dom)
                if sub is not None:
                    primary = left_cat.subst(sub)
                    secondary = right_cat.subst(sub)
                    composition = category.SlashCategory(
                        primary.cod,
                        right_cat.slash,
                        secondary.dom)
                    primary_s = \
                        category.alpha_normalized_string(primary)
                    secondary_s = \
                        category.alpha_normalized_string(secondary)
                    composition_s = \
                        category.alpha_normalized_string(composition)
                    rule = ">B"

                    if DEBUG:
                        print(f"    DEBUG trying >B")
                        print(f"          {left_cat} {right_cat}")
                        print(
                            f"          {primary_s} {secondary_s}")
                        print(f"          {composition_s}")

                    self.__graph[composition_s].update([
                        primary_s, secondary_s])
                    if (composition_s, rule) in self.__redundant:
                        if DEBUG:
                            print("      built duplicate: ",
                                  composition_s, rule)
                        return []
                    else:

                        return [(composition, rule)]

            # Try backward composition
            if (left_cat.slash <= slash.LCOMPOSE) and \
                    (right_cat.slash <= slash.LCOMPOSE):
                # shape is right. Do they match up?
                sub = left_cat.cod.sub_unify(right_cat.dom)
                if sub is not None:
                    secondary = left_cat.subst(sub)
                    primary = right_cat.subst(sub)
                    composition = category.SlashCategory(
                        primary.cod,
                        right_cat.slash,
                        secondary.dom)
                    primary_s = \
                        category.alpha_normalized_string(primary)
                    secondary_s = \
                        category.alpha_normalized_string(secondary)
                    composition_s = \
                        category.alpha_normalized_string(composition)
                    rule = '<B'

                    self.__graph[composition_s].update([
                        primary_s, secondary_s])
                    if (composition_s, rule) in self.__redundant:
                        if DEBUG:
                            print("      built duplicate: ",
                                  composition_s, rule)
                        return []
                    else:
                        return [(composition, rule)]

        return []

    def try_rules(self, left, left_rules, right, right_rules):
        return (self.try_apply(left, left_rules, right, right_rules) + self.try_compose(left, left_rules, right, right_rules))

    def typeraise(self, cat):
        t = category.CategoryMetavar("T")
        fwd = category.SlashCategory(
            t, slash.RSLASH, category.SlashCategory(
                t, slash.LSLASH, cat))
        back = category.SlashCategory(
            t, slash.LSLASH, category.SlashCategory(
                t, slash.RSLASH, cat))
        fwd_s = category.alpha_normalized_string(fwd)
        back_s = category.alpha_normalized_string(back)
        cat_s = category.alpha_normalized_string(cat)
        self.__graph[fwd_s].add(cat_s)
        self.__graph[back_s].add(cat_s)

        return [(fwd, '>T'), (back, '<T')]

    def print_graph(self):
        for start, ends in self.__graph.items():
            for end in ends:
                print(f'{start} -> {end}')

    def bfs(self):
        print("\n\nUseful (reachable) inhabited categories from S\n")

        print(f'for constructing S   : {self.__graph["S"]}')
        print(f'for constructing S/NP: {self.__graph["S/NP"]}')

        visited = set()
        queue = ['S']

        while queue:
            next = queue.pop(0)
            if next in visited:
                continue

            print(next)
            visited.add(next)
            queue += list(self.__graph[next])

    def find_shortest_paths(self):
        self.__shortest_path_dist = collections.defaultdict(lambda: math.inf)
        for cat in self.__categories:
            self.__shortest_path_dist[(cat, cat)] = 0
        for src in self.__categories:
            for _, _, dst in self.__graph[src]:
                self.__shortest_path_dist[(src, dst)] = 1
        for mid in self.__categories:
            for src in self.__categories:
                for dst in self.__categories:
                    alt_len = self.__shortest_path_dist[(src, mid)] + \
                        self.__shortest_path_dist[(mid, dst)]
                    if (self.__shortest_path_dist[(src, dst)] > alt_len):
                        self.__shortest_path_dist[(src, dst)] = alt_len

    def print_shortest_paths(self):
        for (src, dst), distance in self.__shortest_path_dist.items():
            if distance != 0 and distance != math.inf:
                print(f'{src} --- {distance} --> {dst}')


def test_lexicon(filename):
    ccgrammar = CategoryEnumerator(filename)
    ccgrammar.print_inhabited()

#    ccgrammar.print_graph()
    ccgrammar.bfs()


if __name__ == '__main__':
    random.seed()
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
