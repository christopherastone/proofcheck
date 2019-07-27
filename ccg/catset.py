import category
import collections


class CatSet:
    def __init__(self, cat_orig_pairs):
        self.__data = cat_orig_pairs[:]   # copy just in case
        self.__slash_pairs = [(cat, orig) for cat, orig in cat_orig_pairs
                              if isinstance(cat, category.SlashCategory)]
        self.__with_shape = None
        self.__has_slash = None
        self.__left = None
        self.__right = None
        self.__all = None

    @property
    def all(self):
        if self.__all is None:
            self.__all = list(orig for _, orig in self.__data)
        return self.__all

    @property
    def with_shape(self):
        if self.__with_shape is None:
            self.__with_shape = collections.defaultdict(list)
            for cat, orig in self.__data:
                self.with_shape[cat.shape].append(orig)
        return self.__with_shape

    @property
    def has_slash(self):
        if self.__has_slash is None:
            partition = collections.defaultdict(list)
            for cat, orig in self.__slash_pairs:
                partition[cat.slash].append((cat, orig))
            assert(None not in partition.keys())

            self.__has_slash = {}
            for sl, pairs in partition.items():
                self.__has_slash[sl] = CatSet(pairs)
        return self.__has_slash

    @property
    def left(self):
        if self.__left is None:
            self.__left = CatSet([(cat.cod, orig)
                                  for cat, orig in self.__slash_pairs])
        return self.__left

    @property
    def right(self):
        if self.__right is None:
            self.__right = CatSet([(cat.dom, orig)
                                   for cat, orig in self.__slash_pairs])
        return self.__right
