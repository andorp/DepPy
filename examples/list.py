#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import check

# Homogenous list

# Abstract type, one layer of inheritance, type parameters are part of the abstract type.

# Type definition

# Type constructors
class List:
  def __init__(self,T):
    check(T,type)
    # Type constructors can have parameters, they must be initialized in the constructor.
    self.T = T
    pass
  
  pass # Represents a type

# Data constructor
class Nil (List) :

  def __init__(self,T):
    List.__init__(self,T)

  def __repr__(self) :
    return f"Nil()"


# Data constructor
class Cons (List) :

  def __init__(self,x,xs):
    check(xs,List)
    check(x,xs.T)
    List.__init__(self,xs.T)
    self.x  = x
    self.xs = xs

  def __repr__(self) :
    return f"Cons({self.x},{self.xs})"

# Examples

empty = Nil(int)
singleton = Cons(3,empty)

print(empty)
print(singleton)
