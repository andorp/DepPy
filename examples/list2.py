#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""


# Homogenous list

# Abstract type, one layer of inheritance, type parameters are part of the abstract type.

# Type definition

from type import Type,NAT

class LIST(Type) :
    
    def __init__(self,T) :
        # T : Type 
        self.T = T


# Type constructors
class List:

    #  List (T = A) are the t : List with t.T == A


  def has_type(self) :
      return LIST(self.T)
    
  def __init__(self,T):
    # self.T : Type
    # Type constructors can have parameters, they must be initialized in the constructor.
    pass
  
  def append(self,ys) :
      # append : (ys : List (T = self.T)) : List (T = self.T)
      pass

  pass # Represents a type

# Data constructor
class Nil (List) :

  def __init__(self,T):
    # T : Type
    self.T = T
    pass
    
    
  def append(self,ys) :
      return ys

  def __repr__(self) :
    return f"Nil()"


# Data constructor
class Cons (List) :

  def __init__(self,x,xs):
    # self.x : self.T
    # self.xs : List (T = self.T)
    self.T = xs.T
    self.x  = x
    self.xs = xs

  def __repr__(self) :
    return f"Cons({self.x},{self.xs})"

  def append(self,ys) :
      return Cons(self.x,self.xs.append(ys))

# Examples

empty = Nil(NAT)
singleton = Cons(3,empty)

print(empty)
print(singleton)
print(singleton.append(singleton))
