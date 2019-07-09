import catparser
import category
import collections
import math
import random
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


class BadPhraseLength(BaseException):

    def __init__(self, cat, length):
        self.cat = cat
        self.length = length

    def __repr__(self):
        return f'BadPhraseLength({self.cat},{self.length})'


class CCGrammar:
    def __init__(self, filename):
        lexicon_data = open(filename).read().splitlines()
        lexicon = catparser.do_parses(lexicon_data)[0]
        self.__words = {word: [cat for cat, sem in infos]
                        for word, infos in lexicon.items()}

        self.__catmap_unary = collections.defaultdict(list)
        for word, cats in self.__words.items():
            for cat in cats:
                self.__catmap_unary[cat].append(word)

        all_cats = self.__catmap_unary.keys()

        self.__rules = []
        for word, cats in self.__words.items():
            for cat in cats:
                self.__rules.append(Rule(cat, [word]))

        self.__singletons = set()
        for cat in all_cats:
            self.add_singletons(cat)
        for word in self.__singletons:
            self.__rules.append(Rule(category.SingletonCategory(word), [word]))

        worklist = set(all_cats)
        self.__graph = collections.defaultdict(list)
        self.__categories = set()
        self.__catmap_binary = collections.defaultdict(list)
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

        # memo pad for sentence_count function
        #  We initialize here the singleton words, leaving the
        #  sentence_count function to care only about binary rules
        self.__sentence_counts = {}
        for cat in self.__categories:
            self.__sentence_counts[(cat, 1)] = len(self.__catmap_unary[cat])

        # memo_pad for rule_count function
        self.__rule_counts = {}

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
                    self.__catmap_binary[lhs].append((argument, functor))
                    self.__graph[functor].append(("functor <", argument, lhs))
                    self.__graph[argument].append(("argument <", functor, lhs))
                if functor.slash.dir in [slash.RIGHT, slash.UNDIRECTED]:
                    self.__rules.append(Rule(lhs, [functor, argument]))
                    self.__catmap_binary[lhs].append((functor, argument))
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

    def sentence_count(self, cat, length):
        """returns the number of sentences of the given length
           that can be generated from the given starting category."""

        assert(length > 0)
        if (cat, length) not in self.__sentence_counts:
            count = 0
            for rule in self.__rules:
                if len(rule.rhs) == 2 and cat == rule.lhs:
                    count += self.rule_count(rule, length)
            print(f'sentence_count {cat} {length} := {count}')
            self.__sentence_counts[(cat, length)] = count
        else:
            print(
                f'  sentence_count {cat} {length} == '
                f'{self.__sentence_counts[(cat, length)]}')

        return self.__sentence_counts[(cat, length)]

    def show_sentence_counts(self, upto=5):
        for cat in self.__sorted_categories:
            for wds in range(1, upto+1):
                print(f'{cat} has {self.sentence_count(cat, wds)}'
                      f' of length {wds}')

    def rule_count(self, rule, length):
        if len(rule.rhs) == 1:
            if isinstance(rule.rhs[0], str):
                return 1 if length == 1 else 0
            else:
                return sentence_count(rule.rhs[0], length)
        else:
            assert(len(rule.rhs) == 2)
            lhs = rule.lhs
            rhs0 = rule.rhs[0]
            rhs1 = rule.rhs[1]
            key = (lhs, rhs0, rhs1, length)
            if key not in self.__rule_counts:
                count = 0
                for k in range(1, length):
                    count += \
                        self.sentence_count(rhs0, k) * \
                        self.sentence_count(rhs1, length-k)
                self.__rule_counts[key] = count
                print(f'rule_count {lhs} -> {rhs0} {rhs1} {length} := {count}')
            else:
                print(
                    f'  rule_count {lhs} -> {rhs0} {rhs1} {length} '
                    f'== {self.__rule_counts[key]}')
            return self.__rule_counts[key]

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

    def generate(self, cat, length, threshold=1.0):
        print(cat, length)
        if (self.sentence_count(cat, length) == 0):
            raise BadPhraseLength(cat, length)

        if length == 1:
            words = self.__catmap_unary[cat]
            num_words = len(words)
            # We already know from above that there is at least one sentence
            # of length 1, and all such sentences are single words.
            assert num_words > 0
            n = random.randrange(num_words)
            return [words[n]]

        choices = self.__catmap_binary[cat]
        num_choices = len(choices)
        assert(num_choices > 0)
        while True:
            n = random.randrange(num_choices)
            rhs0, rhs1 = choices[n]
            k = random.randrange(1, length)
            try:
                words0 = self.generate(rhs0, k, threshold)
                words1 = self.generate(rhs1, length-k, threshold)
                return words0 + words1
            except BadPhraseLength as e:
                print("backtracking")
                pass


def test_lexicon(filename):
    ccgrammar = CCGrammar(filename)
    ccgrammar.print_rules()
    print("~~~~~")
    ccgrammar.show_sentence_counts(2)
    print("~~~~~")
    # ccgrammar.print_graph()
    # print("~~~~~")
    # ccgrammar.find_shortest_paths()
    # ccgrammar.print_shortest_paths()
    print(ccgrammar.generate(category.S, 2))
    # print(ccgrammar.generate(category.S, 3))
    # print(ccgrammar.generate(category.S, 4))


if __name__ == '__main__':
    random.seed()
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            test_lexicon(filename)
    else:
        test_lexicon('lexicon.txt')
