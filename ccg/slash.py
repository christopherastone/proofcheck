import lattice

##############
# DIRECTIONS #
##############

LEFT = '\\'
RIGHT = '/'
UNDIRECTED = "|"

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
        return self.dir + self.mode

    # def __repr__(self):
    #     return f'Slash({self.dir!r},{self.mode!r})'

    def __le__(self, other):
        return (isinstance(other, Slash) and
                (self.dir == other.dir or other.dir == UNDIRECTED) and
                modes.leq(self.mode, other.mode))


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
