#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 16 10:49:44 2024

@author: psztxa
"""

"""
data Nat : Set

"""

class Nat : # abstract: no __init__!
    # add : (Nat) Nat
    # ASSERT Nat.__dict__["add"] : (n : Nat) -> Nat
    
    def add(self,n) : # Nat) Nat
        pass
    
    def double(self) : # () : Nat
        return self.add(self)
    
class Zero (Nat) : 
    # ASSERT __dict__ : {}
    # DERIVED <Zero->Nat>(x) : Nat

    def __init__(self) :
        pass

    def __repr__(self) : 
        return "Zero()"
    
    def add(self,m) :
        return m

class Succ (Nat) : 
    # n : Nat
    # ASSERT __dict__ :{ "n" : Nat }
    # DERIVED <Succ->Nat>(x) : Nat
    def __init__(self,n) : # n : Nat
        self.n = n
        
    def add(self,m) : # (m : Nat) : Nat 
        return Succ(self.n.add(m))
        
    def __repr__(self) :
        return f"Succ({self.n})"
"""        
def Pred(Nat) :
    def __init__(self,n) : # n : Nat
        self.n = n
        
    def add(self,m) : # m : Nat 
        return Pred(self.n.add(m))
        
    def __repr__(self) :
        return f"Pred({self.n})"
"""

"""
Nat = Zero () | Succ (n : Nat)

"""

        
#---
        
two = Succ(Succ(Zero()))
three = Succ(two)
print(two.add(three))