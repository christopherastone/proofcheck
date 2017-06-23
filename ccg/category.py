"""
Created on Tue May 30 14:48:25 2017

@author: stone
"""


class BaseCategory:
    """An atomic grammatical category, such as NP"""
    def __init__(self, nm: str):
        self.__name = nm

    def __str__(self):
        return self.__name

    def __repr__(self):
        return f'BaseCategory({self.__name!r})'

    def __eq__(self, other):
        return (isinstance(other, BaseCategory) and
                self.__name == other.__name)

    @property
    def dom(self):
        return None

    @property
    def cod(self):
        return None

    @property
    def slash(self):
        return None


class SlashCategory:
    """A complex grammatical category, with a given codomain, domain,
       and slash type"""
    def __init__(self, slash, cod, dom, restr=None):
        self.__slash = slash
        self.__cod = cod
        self.__dom = dom
        self.__restr = {} if restr is None else restr

    def __eq__(self, other):
        return (isinstance(other, SlashCategory) and
                (self.__slash == other.__slash) and
                (self.__cod == other.__cod) and
                (self.__restr == other.__restr))

    def __repr__(self):
        return (f'SlashCategory({self.__slash!r},{self.__cod!r},' +
                f'{self.__dom!r}' +
                ("" if self.__restr == {} else f',{self.__restr}') +
                f')')

    def __str__(self):
        return f'({self.__cod}{self.__slash}{self.__dom})'

    @property
    def dom(self):
        return self.__dom

    @property
    def cod(self):
        return self.__cod

    @property
    def slash(self):
        return self.__slash


########################
# SLASH-TYPE CONSTANTS #
########################

LEFT = '\\'
RIGHT = '/'


def invert(dir):
    """return the opposite of the given direction"""
    if dir == LEFT:
        return RIGHT
    if dir == RIGHT:
        return LEFT
    raise ValueError(f'bad direction {dir}')


############################
# USEFUL COMMON CATEGORIES #
############################

NP = BaseCategory("NP")                   # noun phrase
S = BaseCategory("S")                     # sentence
PP = BaseCategory("PP")                   # prepositional phrase
VBI = SlashCategory(LEFT, S, NP)          # intransitive verb, S\NP
VBT = SlashCategory(RIGHT, VBI, NP)       # transitive verb, (S\NP)/NP
MODAL = SlashCategory(RIGHT, VBI, VBI)    # modal verb, (S\NP)/(S\NP)
