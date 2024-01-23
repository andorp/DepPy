#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import check
from nat import *

# Type definition

class Vector:
  n : Nat
  T : type
  def __init__(self,n:Nat,t:type):
    self.n = n
    self.T = t
  pass

class Nil(Vector) :
  def __init__(self,t:type):
    Vector.__init__(self,Zero(),t)

  def __repr__(self):
    return f"Nil()"

class Cons(Vector) :
  def __init__(self,x,xs):
    check(xs,Vector)
    check(x,xs.T)
    Vector.__init__(self,Succ(xs.n),xs.T)
    self.x  = x
    self.xs = xs
  
  def __repr__(self):
    return f"Succ({self.x},{self.xs})"

empty = Nil(int)
cons = Cons(1,empty)

print(empty)
print(cons)
