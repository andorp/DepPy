#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import check
from nat import *

# Type definition

# Type constructors
class Vector:
  
  def __init__(self,n,T):
    # Type constructors can have parameters, they must be initialized in the constructor.
    # The type of the parameters (indexes?) must be checked in the type constructor
    check(n,Nat)
    check(T,type)
    self.n = n
    self.T = T
    pass
  
  pass

# Data constructor
class Nil(Vector) :
  def __init__(self,T:type):
    Vector.__init__(self,Zero(),T)

  def __repr__(self):
    return f"Nil()"

# Data constructor
class Cons(Vector) :
  def __init__(self,x,xs):
    check(xs,Vector)
    check(x,xs.T)
    Vector.__init__(self,Succ(xs.n),xs.T)
    self.x  = x
    self.xs = xs
  
  def __repr__(self):
    return f"Succ({self.x},{self.xs})"

# Examples

empty = Nil(int)
cons = Cons(1,empty)

print(empty)
print(cons)
