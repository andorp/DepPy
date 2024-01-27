#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 16 10:49:44 2024

@author: psztxa
"""

from check import check

"""
data Nat : Set
"""

# Type constructors
class Nat : # abstract: no __init__!
    # add : (Nat) Nat
    # ASSERT Nat.__dict__["add"] : (n : Nat) -> Nat
    
    # Abstract type must have a constructor, even it its empty
    # The constructor must end in pass
    def __init__(self):
        pass

    def add(self,n) : # Nat) Nat
        pass
    
    def double(self) : # () : Nat
        return self.add(self)

    # Equivalence checking, defined by the user.    
    def __same__(self,b):
        pass

    # Type definitions must have a pass at the end.
    pass

# Data constructor
class Zero (Nat) : 
    # ASSERT __dict__ : {}
    # DERIVED <Zero->Nat>(x) : Nat

    def __init__(self) :
        pass

    def __repr__(self) : 
        return "Zero()"
    
    def add(self,m) :
        return m

    def __same__(self,b):
      check(b,Nat)
      return isinstance(b,Zero)

# Data constructor
class Succ (Nat) : 
    # n : Nat
    # ASSERT __dict__ :{ "n" : Nat }
    # DERIVED <Succ->Nat>(x) : Nat
    def __init__(self,n) : # n : Nat
        check(n,Nat)
        self.n = n
        
    def add(self,m) : # (m : Nat) : Nat 
        return Succ(self.n.add(m))
        
    def __repr__(self) :
        return f"Succ({self.n})"

    def __same__(self,b):
        check(b,Nat)
        if isinstance(b,Succ):
            return self.n.__same__(b.n)
        else:
            return False

# Eliminator(?) of the natural numbers
# Visitor pattern for Nats (Foldable+Traversable)
class NatElim [T] :
    # TODO: replace T
    def zero(self)     -> T : pass
    def succ(self,t:T) -> T : pass
    pass

def natElim(k:Nat,elim:NatElim):
    # TODO: Tail recursion?
    if isinstance(k,Zero):
        elim.zero()
    elif isinstance(k,Succ):
        elim.succ(natElim(k.n))
    else:
        raise TypeError("natElim: parameter not of type Nat")

"""
Nat = Zero () | Succ (n : Nat)
"""
        
# Examples
        
nat = Nat()               # Example of te type Nat
two = Succ(Succ(Zero()))  # Example of the value 2
three = Succ(two)         # Example of the value 3
print(two.add(three))
