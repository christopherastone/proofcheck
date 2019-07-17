import catparser
import category
import ccgbank
import collections
import functools
import heapq
import math
import random
import re
import slash
import sys

DEBUG = False
VERBOSE = False
MAX_CATEGORIES_GEN = 1000
MAX_CATEGORIES_SHOW = 100
SKIP_NONNORMAL = True
MAX_COMPOSITION_ORDER = 3

DO_TYPERAISE = True
NO_DOUBLE_TYPERAISE = True

assert(MAX_COMPOSITION_ORDER >= 1)

USE_CCGBANK_LEXICON = True


slashre = re.compile(r'[/|\\]')


def sort_key(s):
    s_nondirected, num_slashes = re.subn(slashre, "|", s)
    return (num_slashes, len(s), s_nondirected, s)


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

        @functools.total_ordering
        class HeapItem:
            def __init__(self, cat, rule):
                self.data = (cat, rule)
                cat_s = category.alpha_normalized_string(cat)
                self.key = (rule != 'LEX', sort_key(cat_s), rule)

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
        self.__categories = collections.defaultdict(list)

        # set of (category string, rule) pairs
        #   kept for improved redundency checks
        self.__redundant = set()
        num_heappops = 0
        while worklist:
            new, new_rule = heapq.heappop(worklist).data
            if not new.closed:
                new = new.refresh()
            # if "/*" in new_str or "\\*" in new_str:
            #     DEBUG = True
            if (new, new_rule) in self.__redundant:
                if DEBUG:
                    print(f"    {new} is a duplicate for {new_rule}")
                continue
            self.__categories[new].append(new_rule)
            self.__redundant.add((new, new_rule))
            if VERBOSE:
                num_heappops += 1
                print(f"{new} {new_rule} ({num_heappops})")
            for old, old_rules in self.__categories.items():
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
                        print("      adding: ", ", ".join([category.alpha_normalized_string(c) + " " + r
                                                           for c, r in delta]))

                    add_to_worklist(delta)

            delta = self.typeraise(new, [new_rule])
            if DEBUG:
                print("  adding: ", ", ".join(
                    [category.alpha_normalized_string(c) + " " + r
                     for c, r in delta]))
            add_to_worklist(delta)

            if len(self.__categories) > MAX_CATEGORIES_GEN:
                print("...etc...")
                for w, r in [item.data for item in worklist]:
                    rule_list = self.__categories[w]
                    if r not in rule_list:
                        rule_list.append(r)
                break

            # DEBUG = False

    def print_inhabited(self):
        if (MAX_CATEGORIES_SHOW == 0):
            return

        print("\n\nINHABITED CATEGORIES\n")

        inhabited = [(category.alpha_normalized_string(c), ", ".join(rs))
                     for c, rs in self.__categories.items()][:MAX_CATEGORIES_SHOW]

        inhabited.sort(key=lambda x: sort_key(x[0]))
        for s, rule in inhabited:
            print(s, "\t", rule)
        print(len(inhabited), "/", len(self.__categories))

    def try_forward_apply(self, left, left_rules, right, right_rules):
        """Consider the given combination of categories to see if
           forward application is possible"""
        assert(left_rules)
        if isinstance(left, category.SlashCategory) and \
                left.slash <= slash.RAPPLY:
            # Possible instance of >
            if SKIP_NONNORMAL and all(
                    rule.startswith('>T') or
                    rule.startswith('>B') for rule in left_rules):
                return []
            sub = right.sub_unify(left.dom)
            if sub is not None:
                functor = left.subst(sub)
                argument = right.subst(sub)
                result = functor.cod.subst(sub)
                rule = '>'

                if DEBUG:
                    print(f"    DEBUG trying {left} {right}")
                    print(f"          {functor} {argument} {rule}")
                    print(f"          {left_rules} {right_rules}")
                self.__graph[result].update([functor, argument])
                if (result, rule) not in \
                        self.__redundant:
                    return [(result, rule)]
                else:
                    if DEBUG:
                        print("      built duplicate: ",
                              category.alpha_normalized_string(result))

        return []

    def try_backward_apply(self, left, left_rules, right, right_rules):
        """Consider the given combination of categories to see if
           backward application is possible"""
        assert(right_rules)
        if isinstance(right, category.SlashCategory) and \
                right.slash <= slash.LAPPLY:
            # possible instance of <
            if SKIP_NONNORMAL and all(
                    rule.startswith('<T') or
                    rule.startswith('<B') for rule in right_rules):
                if DEBUG:
                    print(
                        f"< rule: skipping {left} {left_rules} {right} {right_rules}")
                return []
            # print(f'trying to unify {left} <= {right.dom}')
            sub = left.sub_unify(right.dom)
            # print(sub is not None)
            if sub is not None:
                functor = right.subst(sub)
                argument = left.subst(sub)
                result = functor.cod.subst(sub)
                rule = '<'
                if DEBUG:
                    print(f"    DEBUG trying {left} {right} <")
                    print(f"          {argument} {functor}")
                    print(f"          {left_rules} {right_rules}")

                self.__graph[result].update([functor, argument])
                if (result, rule) in \
                        self.__redundant:
                    if DEBUG:
                        print("      built duplicate: ",
                              result, rule)

                    return []
                else:
                    return [(result, rule)]

        return []

    def try_backward_compose(self, left, left_rules, right, right_rules):
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

                self.__graph[composition].update([primary, secondary])
                if (composition, rule) in self.__redundant:
                    if DEBUG:
                        print("      built duplicate: ",
                              composition, rule)
                    return []
                else:
                    return [(composition, rule)]

        return []

    def try_backwards_cross_compose(self, left, left_rules, right, right_rules):
        if (isinstance(left, category.SlashCategory) and
                isinstance(right, category.SlashCategory) and
                left.slash <= slash.RCROSS and
                right.slash <= slash.LCROSS):

            # H&B Stipulation p. 467
            # See comments for forbidden_combination() in rules.py
            assert(left_rules)
            if all(rule.startswith('>T') for rule in left_rules):
                return []

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
            rule = '<xB'

            self.__graph[composition].update([primary, secondary])
            if (composition, rule) in self.__redundant:
                if DEBUG:
                    print("      built duplicate: ",
                          composition, rule)
                return []
            else:
                # print("aha: <Bx applies")
                # print(f"  {left} {left_rules} {right} {right_rules}")
                # print(f"  {secondary} {left_rules} {primary} {right_rules}")
                # print(f"  {composition}")
                return [(composition, rule)]

        return []

    def bad_compose(self, lrule, rrule, dir, compose_order):
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

    def try_general_forward_compose(self,
                                    left, left_rules, right, right_rules,
                                    max_order=1, spine=[]):

        # Were there too many extra arguments?
        order_of_this_composition = len(spine) + 1
        if order_of_this_composition > max_order:
            return []

        # This code doesn't work if one of the sides is an actual
        # metavariable.
        assert(not (isinstance(left, category.CategoryMetavar)))
        assert(not (isinstance(right, category.CategoryMetavar)))

        if not (isinstance(left, category.SlashCategory) and
                left.slash <= slash.RCOMPOSE and
                isinstance(right, category.SlashCategory)):
            # Left side doesn't have a composible right-slash,
            # or right side doesn't have any slash, so
            # there's no hope of applying a B rule.
            return []

        # Note: In the presence of metavariables, it's easy
        # to see that more than one composition might be legal,
        # e.g.,  X / T  can compose with  A / B / C
        #    resulting in   X / C     (>B)
        #                   X / B / C (>B2)
        #   (not to mention X  via application a.k.a. >B0)
        # So we need to check higher-order compositions
        #  even if a simple >B direct composition would work.

        # Do the recursive checking
        compositions_found = []
        if (isinstance(right.cod, category.SlashCategory)):
            compositions_found += self.try_general_forward_compose(
                left, left_rules, right.cod, right_rules,
                max_order, [(right.slash, right.dom)] + spine)

        # if compositions_found and left.dom.closed:
        #    return compositions_found

        # OK, let's finally try to do *this* composition.

        if not (right.slash <= slash.RCOMPOSE):
            # not a composeable slash on the right
            return compositions_found

        # two composeable right slashes. Confirm they match up
        sub = right.cod.sub_unify(left.dom)
        if sub is None:
            return compositions_found

        # Note that just because we can't do an order-1 composition
        # doesn't mean higher-order compositions weren't legal
        # E.g., if a / T      came from >B1
        #          b / d / f  came from <
        # Then a / f via >B1 is forbidden, but a / d / f by >B2 would be ok

        # So even if this composition is forbidden due to normal forms,
        # we should still return any valid compositions that we discovered
        # recursively.

        # In theory, the same category could be arrived at in more than
        # one way. Beacuse of that, we need to check that no possible
        # ways of deriving the left-hand-side and the right-hand-side
        # could produce a normal derivation.
        if SKIP_NONNORMAL:
            validity_checks = [
                self.bad_compose(lrule, rrule, '>', order_of_this_composition)
                for lrule in left_rules for rrule in right_rules]
            # validity_checks has False for any *valid* composition and
            #   True for any invalid composition. We abort only if
            #   there were zero valid compositions.
            if all(validity_checks):
                return compositions_found

        # Put together the final composition
        # (using un-substituted categories!)
        composition = \
            category.SlashCategory(left.cod, right.slash, right.dom)
        for sl, cat in spine:
            composition =  \
                category.SlashCategory(composition, sl, cat)

        primary = left.subst(sub)
        secondary = right.subst(sub)
        composition = composition.subst(sub)

        rule = '>B'
        if (order_of_this_composition > 1):
            rule += str(order_of_this_composition)

        if DEBUG:
            print(f"    DEBUG trying >B" + str(order_of_this_composition))
            print(f"          {left} {left_rules} {right} {right_rules}")
            print(f"          {primary} {secondary}")
            print(f"          {composition}")

        self.__graph[composition].update([primary, secondary])
        if (composition, rule) in self.__redundant:
            if DEBUG:
                print("      built duplicate: ",
                      composition, rule)
        else:
            compositions_found.append((composition, rule))
        return compositions_found

    def try_rules(self, left, left_rules, right, right_rules):
        return (self.try_forward_apply(left, left_rules, right, right_rules) +
                self.try_backward_apply(left, left_rules, right, right_rules) +
                # self.try_forward_compose(left, left_rules, right, right_rules) +
                self.try_backward_compose(left, left_rules, right, right_rules) +
                self.try_general_forward_compose(left, left_rules, right, right_rules, MAX_COMPOSITION_ORDER) +
                self.try_backwards_cross_compose(left, left_rules, right, right_rules))

    def typeraise(self, cat, rules):
        if not DO_TYPERAISE:
            return []

        if NO_DOUBLE_TYPERAISE and \
            all(rule.startswith('>T') or
                rule.startswith('<T') for rule in rules):
            return []

        t = category.CategoryMetavar("T")

        fwd = category.SlashCategory(
            t, slash.RSLASH, category.SlashCategory(
                t, slash.LSLASH, cat))
        back = category.SlashCategory(
            t, slash.LSLASH, category.SlashCategory(
                t, slash.RSLASH, cat))

        self.__graph[fwd].add(cat)
        self.__graph[back].add(cat)

        return [(fwd, '>T'), (back, '<T')]

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
