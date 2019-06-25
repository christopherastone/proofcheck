class BaseType:
    def __init__(self, name):
        self.__name = name

    @property
    def name(self):
        return self.__name

    def __str__(self):
        return self.name

    def __repr__(self):
        return f"E('{self.name}')"

    def __eq__(self, other):
        return (isinstance(other, BaseType) and
                self.name == other.name)

    @property
    def arity(self):
        return 0


class ArrowType:
    def __init__(self, dom, cod):
        self.__dom = dom
        self.__cod = cod

    @property
    def dom(self):
        return self.__dom

    @property
    def cod(self):
        return self.__cod

    def __str__(self):
        if isinstance(self.__dom, ArrowType):
            return f'({self.dom})->{self.cod}'
        else:
            return f'{self.dom}->{self.cod}'

    def __repr__(self):
        return f'ArrowType({self.dom!r},{self.cod!r})'

    def __eq__(self, other):
        return (isinstance(other, ArrowType) and
                self.dom == other.dom and
                self.cod == other.cod)

    @property
    def arity(self):
        return 1 + self.cod.arity


e = BaseType('e')
t = BaseType('t')
et = ArrowType(e, t)
ett = ArrowType(ArrowType(e, t), t)
