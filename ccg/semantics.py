#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jun  2 15:50:07 2017

@author: stone
"""


class Const:
    def __init__(self, nm: str):
        self.__name = nm

    def toString(self, stack=[]):
        return self.__name

    def __str__(self):
        return self.toString()

    def __repr__(self):
        return f'Const({self.__name!r})'

    def __eq__(self, other):
        return (isinstance(other, Const) and
                self.__name == other.__name)

    def shift(self, delta, base=0):
        return self

    def subst(self, k, e):
        return self
    
    def reduce(self):
        return self


class BoundVar:
    def __init__(self, n):
        self.__num = n

    def toString(self, stack=[]):
        if (0 <= self.__num < len(stack)):
            return stack[self.__num]
        else:
            return str(self.__num)

    def __str__(self):
        return self.toString()

    def __repr__(self):
        return f'BoundVar({self.__num})'

    def __eq__(self, other):
        return (isinstance(other, BoundVar) and
                self.__num == other.__num)

    def shift(self, delta, base=0):
        if self.__num >= base:
            return BoundVar(self.__num + delta)
        else:
            return self

    def subst(self, k, e):
        if (k == self.__num):
            return e
        else:
            return self

    def reduce(self):
        return self


def beta(body, arg):
    return body.subst(0, arg.shift(1)).shift(-1)


class App:
    def __init__(self, left, right):
        self.__left = left.reduce()
        self.__right = right.reduce()

    def toString(self, stack=[]):
        left = self.__left.toString(stack)
        left = '(' + left + ')' if isinstance(self.__left, Lam) else left
        return (left + '(' +
                self.__right.toString(stack) + ')')

    def __str__(self):
        return self.toString()

    def __repr__(self):
        return f'App({self.__left!r},{self.__right!r})'

    def __eq__(self, other):
        return (isinstance(other, App) and
                self.__left == other.__left and
                self.__right == other.__right)

    def shift(self, delta, base=0):
        return App(self.__left.shift(delta, base),
                   self.__right.shift(delta, base))

    def subst(self, k, e):
        return App(self.__left.subst(k, e), self.__right.subst(k, e))

    def reduce(self):
        if isinstance(self.__left, Lam):
            return beta(self.__left.body, self.__right).reduce()
        else:
            return self

    @property
    def left(self):
        return self.__left

    @property
    def right(self):
        return self.__right


class Lam:
    def __init__(self, hint, body):
        self.__hint = hint
        self.__body = body.reduce()

    def toString(self, stack=[]):
        return ("λ" + self.__hint + "." +
                self.__body.toString([self.__hint]+stack))

    def __str__(self):
        return self.toString()

    def __repr__(self):
        return f'Lam({self.__hint!r},{self.__body!r})'

    def __eq__(self, other):
        return (isinstance(other, Lam) and
                self.__body == other.__body)

    def shift(self, delta, base=0):
        return Lam(self.__hint, self.__body.shift(delta, base+1))

    def subst(self, k, e):
        return Lam(self.__hint, self.__body.subst(k+1, e.shift(1)))

    def reduce(self):
        return self

    @property
    def body(self):
        return self.__body


def test_beta():
    assert (App(Lam("x", BoundVar(0)), Const("c")).reduce() == Const("c"))
    assert (App(Lam("x", Lam("y", BoundVar(0))), Const("c")).reduce() ==
            Lam("z", BoundVar(0)))
    assert (App(Lam("x", Lam("y", BoundVar(1))), Const("c")).reduce() ==
            Lam("z", Const("c")))
    assert (App(Lam("x", Lam("y", BoundVar(1))), BoundVar(0)).reduce() ==
            Lam("z", BoundVar(1)))
    assert Const("c") != Const("d")
    assert Lam("x", BoundVar(0)) != Lam("x", Const("x"))
    assert BoundVar(0) != BoundVar(1)


    