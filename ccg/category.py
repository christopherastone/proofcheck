#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue May 30 14:48:25 2017

@author: stone
"""


def mkBase(s: str):
    return s

NP = mkBase("NP")
S = mkBase("S")


def slash(lr, dom, cod):
    return [lr, dom, cod]

LSLASH = '\\'
RSLASH = '/'


def mkL(cod, dom):
    return slash(LSLASH, dom, cod)


def mkR(cod, dom):
    return slash(RSLASH, dom, cod)


def isL(category):
    return (isinstance(category, list) and category[0] == LSLASH)


def isR(category):
    return (isinstance(category, list) and category[0] == RSLASH)


def sl(category):
    if isinstance(category, list):
        return category[0]
    else:
        return None


def dom(category):
    if isinstance(category, list):
        return category[1]
    else:
        return None


def cod(category):
    if isinstance(category, list):
        return category[2]
    else:
        return None
