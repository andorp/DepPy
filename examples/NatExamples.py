#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

from check import *

from nat    import *
from list   import List
from list   import Nil  as LNil
from list   import Cons as LCons
from vector import Vector
from vector import Nil  as VNil
from vector import Cons as VCons


class ListCreate (NatFold) :
  def __init__(self):
    NatFold.__init__(self,List)

  def zero(self):
    return LNil(int)
  
  def succ(self,xs):
    check(xs, List)
    unify(xs.T,int)
    return LCons(1,xs)

listExample1 = natFold(fromInt(3), ListCreate())
print(listExample1)

# class VectorCreate (NatFold) :
#   def zero(self):
#     return VNil(int)

#   def succ(self,vs):
#     check(vs,Vector) # ??? How to add the index?
#     return VCons(1,vs)
