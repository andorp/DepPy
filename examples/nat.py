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
        
two = Succ(Succ(Zero()))
three = Succ(two)
print(two.add(three))
