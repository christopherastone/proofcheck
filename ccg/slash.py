import lattice

##############
# DIRECTIONS #
##############

LEFT = '\\'
RIGHT = '/'
UNDIRECTED = "|"

ALL_DIRECTIONS = [LEFT, RIGHT, UNDIRECTED]

# def invert(dir):
#     """return the opposite of the given direction"""
#     if dir == LEFT:
#         return RIGHT
#     if dir == RIGHT:
#         return LEFT
#     raise ValueError(f'bad direction {dir}')

#########
# Modes #
#########


INACTIVE = "!"
APPLYONLY = "*"
ALLOWB = "o"
ALLOWBX = "x"
ANYRULE = "."
PHI = "Φ"

ALL_MODES = [INACTIVE, APPLYONLY, ALLOWB, ALLOWBX, ANYRULE, PHI]

modes = lattice.FiniteLattice([
    (ANYRULE, ALLOWB),
    (ANYRULE, ALLOWBX),
    (ALLOWB, PHI),
    (ALLOWBX, PHI),
    (PHI, APPLYONLY),
    (APPLYONLY, INACTIVE)
])


###########
# SLASHES #
###########

class Slash:

    __slots__ = ('__dir', '__mode')

    def __init__(self, dir, mode):
        self.__dir = dir
        self.__mode = mode

    @property
    def dir(self):
        return self.__dir

    @property
    def mode(self):
        return self.__mode

    def __repr__(self):
        if self.mode == ANYRULE:
            return self.__dir
        else:
            return self.__dir + self.__mode

    def __hash__(self):
        return hash((self.__dir, self.__mode))

    # def __repr__(self):
    #     return f'Slash({self.dir!r},{self.mode!r})'

    def __eq__(self, other):
        return (  # isinstance(other, Slash) and
            self.__dir == other.__dir and
            self.__mode == other.__mode)

    # XXX: Should undirected be < or > directed???
    def __le__(self, other):
        return (  # isinstance(other, Slash) and
            (self.__dir == other.__dir or self.__dir == UNDIRECTED) and
            (self.__mode == other.__mode or modes.lt(self.__mode, other.__mode)))


ALL_SLASHES = [Slash(dir, mode) for dir in ALL_DIRECTIONS
               for mode in ALL_MODES]


def mk_rslash(mode):
    return Slash(RIGHT, mode)


def mk_lslash(mode):
    return Slash(LEFT, mode)


RSLASH = Slash(RIGHT, ANYRULE)
LSLASH = Slash(LEFT, ANYRULE)

RCOMPOSE = Slash(RIGHT, ALLOWB)
LCOMPOSE = Slash(LEFT, ALLOWB)

RAPPLY = Slash(RIGHT, APPLYONLY)
LAPPLY = Slash(LEFT, APPLYONLY)

RCROSS = Slash(RIGHT, ALLOWBX)
LCROSS = Slash(LEFT, ALLOWBX)
