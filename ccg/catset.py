import category
import collections
import slash


class CatSet:
    def __init__(self, cat_orig_rule_triples=[]):
        self.__data = list(cat_orig_rule_triples)   # copy just in case
        self.__slash_triples = [(cat, orig, rule)
                                for cat, orig, rule in cat_orig_rule_triples
                                if isinstance(cat, category.SlashCategory)]
        self.__with_shape = None
        self.__has_slash = None
        self.__left = None
        self.__right = None
        self.__all = None
        self.__wo_rules = {}

    def __str__(self):
        return "{{" + ', '.join([category.alpha_normalized_string(c) for c in self.all]) + "}}"

    @property
    def all(self):
        if self.__all is None:
            self.__all = list(orig for _, orig, _ in self.__data)
        return [cat.refresh() for cat in self.__all]

    @property
    def with_shape(self):
        if self.__with_shape is None:
            shape_partition = collections.defaultdict(list)
            for cat, orig, rule in self.__data:
                shape_partition[cat.shape].append((cat, orig, rule))
            self.__with_shape = collections.defaultdict(CatSet)
            for shape, triples in shape_partition.items():
                self.__with_shape[shape] = CatSet(triples)
        return self.__with_shape

    @property
    def has_slash(self):
        if self.__has_slash is None:
            partition = collections.defaultdict(list)
            for cat, orig, rules in self.__slash_triples:
                for sl in slash.ALL_SLASHES:
                    if cat.slash <= sl:
                        partition[sl].append((cat, orig, rules))
            assert(None not in partition.keys())

            self.__has_slash = collections.defaultdict(CatSet)
            for sl, triples in partition.items():
                self.__has_slash[sl] = CatSet(triples)

        return self.__has_slash

    def without_rules(self, drop_set):
        drop_list = list(drop_set)
        drop_list.sort()
        memo_key = ";".join(drop_list)
        if memo_key not in self.__wo_rules.keys():
            triples = []
            for cat, orig, rules in self.__data:
                rule_diff = rules - drop_set
                if rule_diff:
                    triples.append((cat, orig, rule_diff))
                # else:
                #    print(f"Dropped {orig} {rules}")
            self.__wo_rules[memo_key] = CatSet(triples)

        return self.__wo_rules[memo_key]

        if self.__by_rule is None:
            rule_partition = collections.defaultdict(list)
            for cat, orig, rules in self.__data:
                rule_partition[rule].append((cat, orig, rules))

            self.__by_rule = {}
            for rule, triples in rule_partition.items():
                self.__by_rule[rule] = CatSet(triples)

    @property
    def left(self):
        if self.__left is None:
            self.__left = CatSet([(cat.cod, orig, rule)
                                  for cat, orig, rule in self.__slash_triples])
        return self.__left

    @property
    def right(self):
        if self.__right is None:
            self.__right = CatSet([(cat.dom, orig, rule)
                                   for cat, orig, rule in self.__slash_triples])
        return self.__right
