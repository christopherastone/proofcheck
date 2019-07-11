import catparser
import category
import collections
import math
import random
import slash
import sys

DEBUG = False
MAX_CATEGORIES = 50


class CategoryEnumerator:
    def __init__(self, filename):
        lexicon_data = open(filename).read().splitlines()
        lexicon = catparser.do_parses(lexicon_data)[0]
        all_cats = set(cat for infos in lexicon.values() for cat, _ in infos)

        # XX XXX: For now, assume there are no singletons!
        # self.__singletons = set()
        # for cat in all_cats:
        #     self.add_singletons(cat)
        # for word in self.__singletons:
        #    self.__rules.append(Rule(category.SingletonCategory(word), [word]))

        worklist = list(all_cats)
        worklist.sort(key=lambda x: (len(str(x))))

        self.__graph = collections.defaultdict(list)
        self.__categories = set()
        self.__category_strings = set()
        while worklist:
            new = worklist.pop(0).refresh()
            if DEBUG:
                print(f'\n  considering {new}')
            new_str = category.alpha_normalized_string(new)
            if new_str in self.__category_strings:
                if DEBUG:
                    print(f"    it's a duplicate")
                continue
            for old in self.__categories:
                worklist_len = len(worklist)
                worklist += self.try_rules(old, new)
                worklist += self.try_rules(new, old)
                if len(worklist) != worklist_len:
                    if DEBUG:
                        print(f'    vs. {old}')
                        print("      adding: ", ", ".join([category.alpha_normalized_string(c)
                                                           for c in worklist[worklist_len:]]))
            worklist_len = len(worklist)
            worklist += self.typeraise(new)
            if DEBUG:
                print("  adding: ", ", ".join(
                    [category.alpha_normalized_string(c)
                     for c in worklist[worklist_len:]]))
            self.__categories.add(new)
            self.__category_strings.add(new_str)
            print(new_str)
            if len(self.__categories) > MAX_CATEGORIES:
                print("...etc...")
                break

    def try_apply(self, potential_functor, potential_argument):
        """Consider the given combination of categories to see if
           application might be possible(in the appropriate order,
           depending on the direction of the functor's slash)"""
        if isinstance(potential_functor, category.SlashCategory):
            sub = potential_argument.sub_unify(potential_functor.dom)
            if sub is not None:
                functor = potential_functor.subst(sub)
                # argument = potential_argument.subst(sub)
                # direction = functor.slash.dir,
                lhs = functor.cod.subst(sub)
                # if functor.slash.dir in [slash.LEFT, slash.UNDIRECTED]:
                #     self.__graph[functor].append(("functor <", argument, lhs))
                #     self.__graph[argument].append(("argument <", functor, lhs))
                # if functor.slash.dir in [slash.RIGHT, slash.UNDIRECTED]:
                #     self.__graph[functor].append(("functor >", argument, lhs))
                #     self.__graph[argument].append(("argument >", functor, lhs))

                if category.alpha_normalized_string(lhs) in \
                        self.__category_strings:
                    if DEBUG:
                        print("      built duplicate: ",
                              category.alpha_normalized_string(lhs))

                    return []
                else:
                    return [lhs]
            else:
                return []
        else:
            return []

    def try_rules(self, left, right):
        return self.try_apply(left, right)

    def typeraise(self, cat):
        t = category.CategoryMetavar("T")
        return [category.SlashCategory(t,
                                       slash.LSLASH,
                                       category.SlashCategory(t,
                                                              slash.RSLASH,
                                                              cat)),
                category.SlashCategory(t,
                                       slash.RSLASH,
                                       category.SlashCategory(t,
                                                              slash.LSLASH,
                                                              cat))]

    def print_graph(self):
        for start in self.__sorted_categories:
            for label, other, stop in self.__graph[start]:
                print(f'{start} -> {stop} by {label} with {other}')

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


if __name__ == '__main__':
    random.seed()
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
