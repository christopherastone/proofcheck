import catparser
import category
import collections
import math
import slash
import sys


class Rule:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        self.slhs = str(lhs)
        self.srhs = str(rhs)

    def __str__(self):
        return f'{self.lhs} -> {" ".join(str(s) for s in self.rhs)}'

    def __eq__(self, other):
        return self.slhs == other.slhs and self.srhs == other.srhs

    def __le__(self, other):
        return self.slhs <= other.slhs or \
            (self.slhs == other.slhs and self.srhs <= other.srhs)

    def __lt__(self, other):
        return self.slhs < other.slhs or \
            (self.slhs == other.slhs and self.srhs < other.srhs)

    def __hash__(self):
        return hash((self.slhs, self.srhs))


class CCGrammar:
    def __init__(self, filename):
        lexicon_data = open(filename).read().splitlines()
        lexicon = catparser.do_parses(lexicon_data)[0]
        self.__words = {word: cat for word, infos in lexicon.items()
                        for cat, sem in infos}
        worklist = set(self.__words.values())

        self.__rules = []
        for word, cat in self.__words.items():
            self.__rules.append(Rule(cat, [word]))

        self.__singletons = set()
        for cat in worklist:
            self.add_singletons(cat)
        for word in self.__singletons:
            self.__rules.append(Rule(category.SingletonCategory(word), [word]))

        self.__graph = collections.defaultdict(list)
        self.__categories = set()
        while worklist:
            new = worklist.pop()
            # print(f'considering {new}')
            for old in self.__categories:
                # print(f'new = {new} and old = {old}')
                worklist.update(self.try_apply(old, new))
                worklist.update(self.try_apply(new, old))
            self.__categories.add(new)

        self.__sorted_categories = list(self.__categories)
        self.__sorted_categories.sort(key=lambda x: (len(str(x))))

    def add_singletons(self, cat):
        if isinstance(cat, category.SingletonCategory):
            self.__singletons.add(cat.word)
        elif isinstance(cat, category.SlashCategory):
            self.add_singletons(cat.dom)
            self.add_singletons(cat.cod)

    def try_apply(self, potential_functor, potential_argument):
        """Consider the given combination of categories to see if
           application might be possible(in the appropriate order,
           depending on the direction of the functor's slash)"""
        if isinstance(potential_functor, category.SlashCategory):
            sub = potential_argument.sub_unify(potential_functor.dom)
            if sub is not None:
                functor = potential_functor.subst(sub)
                argument = potential_argument.subst(sub)
                direction = functor.slash.dir,
                lhs = functor.cod.subst(sub)
                if functor.slash.dir in [slash.LEFT, slash.UNDIRECTED]:
                    self.__rules.append(Rule(lhs, [argument, functor]))
                    self.__graph[functor].append(("functor <", argument, lhs))
                    self.__graph[argument].append(("argument <", functor, lhs))
                if functor.slash.dir in [slash.RIGHT, slash.UNDIRECTED]:
                    self.__rules.append(Rule(lhs, [functor, argument]))
                    self.__graph[functor].append(("functor >", argument, lhs))
                    self.__graph[argument].append(("argument >", functor, lhs))

                return [lhs] if lhs not in self.__categories else []
            else:
                return []
        else:
            return []

    def print_rules(self):
        self.__rules.sort(key=lambda x: (len(str(x.lhs)), x))
        for rule in self.__rules:
            print(rule)

    def print_graph(self):
        for start in self.__sorted_categories:
            for label, other, stop in self.__graph[start]:
                print(f'{start} -> {stop} by {label} with {other}')

    def sentence_counts(self, upto=5, show_counts=True):
        """returns a dictionary mapping (category, number of words)
           keys to the integer number of matching sentences allowed
           by the grammar. Valid numbers of words run from 1 up to
           and including the value of the upto parameter."""

        # We could turn this dynamic programming algorithm into a
        # memoized recursive function, and only compute the numbers
        # on demand...

        counts = collections.defaultdict(int)

        for rule in self.__rules:
            if len(rule.rhs) == 1 and isinstance(rule.rhs[0], str):
                counts[(rule.lhs, 1)] += 1

        for l in range(2, upto+1):
            for cat in self.__categories:
                for rule in self.__rules:
                    if len(rule.rhs) == 2 and cat == rule.lhs:
                        for k in range(1, l):
                            counts[(cat, l)] += \
                                counts[(rule.rhs[0], k)] * \
                                counts[(rule.rhs[1], l-k)]

        if show_counts:
            table = list(counts.items())
            table.sort(key=lambda x:  (
                len(str(x[0][0])), str(x[0][0]), x[0][1]))
            for ((cat, wds), count) in table:
                print(f'{cat} has {count} of length {wds}')

        return counts

    def find_shortest_paths(self):
        self.__shortest_path_dist = \
            collections.defaultdict(lambda: math.inf)
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
    ccgrammar = CCGrammar(filename)
    ccgrammar.print_rules()
    print("~~~~~")
    ccgrammar.sentence_counts(5)
    print("~~~~~")
    ccgrammar.print_graph()
    print("~~~~~")
    ccgrammar.find_shortest_paths()
    ccgrammar.print_shortest_paths()


if __name__ == '__main__':
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
