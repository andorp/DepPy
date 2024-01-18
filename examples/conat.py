#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 16 11:21:41 2024

@author: psztxa
"""

"""
record ℕ∞ : Set where
  constructor zero-suc
  coinductive
  field
    pred∞ : Maybe ℕ∞
    
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞

_+∞-maybe_ : Maybe ℕ∞ → ℕ∞ → Maybe ℕ∞

pred∞ (m +∞ n) = pred∞ m +∞-maybe n

nothing +∞-maybe n = pred∞ n
just m' +∞-maybe n = just (m' +∞ n)
"""
from copy import copy,deepcopy

class Maybe_Conat :
    pass

class Nothing(Maybe_Conat) :   

    def add(self,n) :
        return n.pred
    
    def __repr__(self) :
        return "Nothing()"
        
class Just(Maybe_Conat) :
    def __init__(self,x) : # x : Lazy CoNat
        self.x = x

    def __repr__(self) :
        input("More?")
        return f"Just({next(self.x)})"
#        return f"Just({next(copy(self.x))})"

    def add_aux(self,n) :
        yield next(self.x).add(n)
#        yield next(copy(self.x)).add(n)
        
    def add(self,n) :
        return Just(self.add_aux(n))


class Conat :
    
    def __init__(self,pred) :
        self.pred = pred

    def __repr__(self) :
        return f"Conat({self.pred})"

    def get_pred(self):
        yield self.pred
        
    def add(self,n) :
        return Conat(self.pred.add(n))        
        
    def Zero() :
        return Conat(Nothing())
                
    def Succ_aux(n) :
        yield n
    
    def Succ(n) :
        return Conat(Just(Conat.Succ_aux(n)))
    
    def Inf_aux() :
        yield Conat.Inf()
    
    def Inf() : 
        return Just(Conat.Inf_aux())
    
zero = Conat.Zero()   
one = Conat.Succ(Conat.Zero())
onez = Conat.Succ(Conat.Zero())
two = Conat.Succ(Conat.Succ(Conat.Zero()))
three = Conat.Succ(two)
five = two.add(three)
onex = one.add(Conat.Zero()) 
oney = zero.add(one)
zerox = zero.add(zero)
twox = one.add(one)
twoy = one.add(onez)
twoz = one.add(deepcopy(one))