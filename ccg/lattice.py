"""
Implementation of finite lattices, based on inputting the Hasse diagram
"""

from collections import defaultdict


def edge_list_to_adjacency_map(edges):
    """
    Given a list of (src,dst) edges, convert to
      a map that sends each node to its immediate successors.
    """
    adjacency = defaultdict(set)
    for (a, b) in edges:
        adjacency[a].add(b)
    return adjacency


def first(iterable):
    """
    Given any iterable, return its first element.
    """
    for value in iterable:
        return value


def transitive_closure(adjacency, bot):
    """
    Calculates the transitive closure of the given DAG
    in adjacency-set format, by doing a depth-first
    search from the unique root of the DAG (the bottom element)
    """
    closure = defaultdict(set)

    def dfs(current, belows):
        nonlocal closure
        for below_item in belows:
            closure[below_item].add(current)
        for successor in adjacency[current]:
            dfs(successor, belows + [current])

    dfs(bot, [])
    return closure


class FiniteLattice:

    def __init__(self, edges):
        """
        Represents a finite lattice, so that we can do efficient comparisons
        and efficient meets/joins.

        The input is the sequence of edges in the Hasse diagram.
        We assume, but do not verify, that they form a lattice.
        """
        self.edges = list(edges)  # copy the values, not the reference
        self.rev_edges = [[b, a] for [a, b] in edges]
        self.elements = frozenset(node for edge in self.edges for node in edge)
        self.adjacency = edge_list_to_adjacency_map(self.edges)
        self.rev_adjacency = edge_list_to_adjacency_map(self.rev_edges)
        self.top = self.maximal(self.elements)
        self.bot = self.minimal(self.elements)
        self.strictuppers = transitive_closure(self.adjacency, self.bot)
        self.strictlowers = transitive_closure(self.rev_adjacency, self.top)

        # memoize joins and meets
        self.__join = {}
        self.__meet = {}
        for a in self.elements:
            for b in self.elements:
                self.__join[(a, b)] = self.calc_join(a, b)
                self.__meet[(a, b)] = self.calc_meet(a, b)

    def join(self, a, b):
        return self.__join[(a, b)]

    def meet(self, a, b):
        return self.__meet[(a, b)]

    def __repr__(self):
        return f'FiniteLattice({self.edges!r})'

    def lt(self, a, b): return b in self.strictuppers[a]
    def leq(self, a, b): return a == b or self.lt(a, b)
    def gt(self, a, b): return b in self.strictlowers[a]
    def geq(self, a, b): return a == b or self.gt(a, b)

    def maximal(self, the_set):
        current = first(the_set)
        while True:
            successors = self.adjacency[current] & the_set
            if len(successors) == 0:
                return current
            else:
                current = first(successors)

    def minimal(self, the_set):
        """
        Return a minimal element of the given set.
        """
        current = first(the_set)
        while True:
            predecessors = self.rev_adjacency[current] & the_set
            if len(predecessors) == 0:
                return current
            else:
                current = first(predecessors)

    def uppers(self, x):
        return frozenset([x]) | self.strictuppers[x]

    def lowers(self, x):
        return frozenset([x]) | self.strictlowers[x]

    def calc_join(self, a, b):
        return self.minimal(self.uppers(a) & self.uppers(b))

    def calc_meet(self, a, b):
        return self.maximal(self.lowers(a) & self.lowers(b))


def test():
    """
          5
        /  \\
       3    |
       |    4
       2    |
        \\ /
          1
    """
    f = FiniteLattice([(1, 2), (2, 3), (1, 4), (3, 5), (4, 5)])
    assert(f.lt(1, 3) and f.gt(3, 1))
    assert(f.lt(1, 5) and f.gt(5, 1))
    assert(not f.lt(5, 1) and not f.gt(1, 5))
    assert(not f.lt(2, 4) and not f.gt(4, 2))
    assert(not f.lt(4, 2) and not f.gt(2, 4))
    assert(f.join(2, 4) == 5 and f.join(4, 2) == 5)
    assert(f.join(3, 4) == 5 and f.join(4, 3) == 5)
    assert(f.join(1, 3) == 3 and f.join(3, 1) == 3)
    assert(f.join(3, 5) == 5 and f.join(5, 3) == 5)
    assert(f.meet(2, 4) == 1 and f.meet(4, 2) == 1)
    assert(f.meet(3, 4) == 1 and f.meet(4, 3) == 1)
    assert(f.meet(1, 3) == 1 and f.meet(3, 1) == 1)
    assert(f.meet(3, 5) == 3 and f.meet(5, 3) == 3)
    print("OK.")
