#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import check

from list import List
from list import Cons as LCons
from list import Nil  as LNil

# Type constructors
class HList:
  def __init__(self,Ts):
    check(Ts,List)
    self.Ts = Ts
    pass

  pass

# Data constructor
class Nil(HList):
  def __init__(self):
    HList.__init__(self,LNil(type))
  
  def __repr__(self):
    return f"Nil()"

# Data constructor
class Cons(HList):
  def __init__(self,x,xs):
    check(xs,HList)
    HList.__init__(self,LCons(type(x),xs.Ts))
    self.x  = x
    self.xs = xs

  def __repr__(self):
    return f"Cons({self.x},{self.xs})"

# Examples

print(Nil())
print(Cons('a',Nil()))
print(Cons(1, Cons('b',Nil())))

