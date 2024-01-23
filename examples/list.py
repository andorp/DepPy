#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import check

# Homogenous list

# Type definition

class List:
  T : type
  def __init__(self,t):
    check(t,type)
    self.T = t
  pass # Still represent an abstract type

class Nil (List) :

  def __init__(self,t):
    List.__init__(self,t)

  def __repr__(self) :
    return f"Nil()"

class Cons (List) :

  def __init__(self,x,xs):
    check(xs,List)
    check(x,xs.T)
    List.__init__(self,xs.T)
    self.x  = x
    self.xs = xs

  def __repr__(self) :
    return f"Cons({self.x},{self.xs})"

# Abstract type, one layer of inheritance, type parameters are part of the abstract type.
# Telescope?

empty = Nil(int)
singleton = Cons(3,empty)

print(empty)
print(singleton)
