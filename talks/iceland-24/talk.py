#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
			 Thorsten Altenkirch
		   University of Nottingham

		   Πthon - dependently typed Python

Created on Fri Sep  6 09:01:02 2024

@author: txa


Why dependent types?
avoid run time errors by static checks
DTP are usually functional
jointly with Andor Penzes 
marry DTP and OOP
verify programs (need termination checking)
"""

class Nat :
    "add (n : Nat) : Nat -> Nat"
    
    pass

class Zero (Nat) :
    
    def __init__(self) :
        pass
    
    def add(self, n) :
        return n
    
    def __repr__(self) :
        return "Zero()"
    
class Suc(Nat) :
    
    def __init__(self, m) :
        "m : Nat"
        self.m = m
        
    def add(self,n) :
        return Suc(self.m.add(n))
        
    def __repr__(self) :
        return f"Suc({self.m})"        
        
one = Suc(Zero())
two = Suc(one)     
four = two.add(two)   

class Fin :
    pass
    "n : Nat"
    "lookupNil (self: Fin[n = Zero()]) : (xs : Vec) : Vec.A"
    "lookupCons (self : Fin)(xs : VCons [n = self.n)): Vec.A"
    
class FZero (Fin) :
    
    def __init__(self, n) :
        self.n = Suc (n)
 
    def lookupNil(self , xs) :
        raise TypeError("Impossible")
        
    def lookupCons(self,xs) :
        return xs.hd
       
class FSuc(Fin) :
    "pred : Fin"

    def __init__(self, pred) :
        " pred : Fin"
        self.n = Suc (pred.n)
        self.pred = pred
       
    def lookupNil(self , xs) :
        raise TypeError("Impossible")
     
    def lookupCons(self,xs) :
        return xs.tl.lookup(self.pred)
     

class Vec :
    pass
    "A : type"
    "n : Nat"
    "append (self : Vec) : (xs : Vec [A = self.A]) "
    "    -> Vec[A = self.A][n = self.n.add(xs.n) ]"
    
    "lookup (self : Vec) : (i : Fin [n = self.n]) -> self.A"
    
class VNil (Vec) :
    
    def __init__(self , A) :
        self.A = A
        self.n = Zero()
        
    def append(self,xs) :
        return xs
    
    def lookup(self,i) :
        return i.lookupNil(self)
        
class VCons (Vec) :
    "hd : A"
    "tl : Vec [.A = A]"
    
    def __init__(self, hd , tl) :
        self.A = tl.A
        self.hd = hd
        self.tl = tl
        self.n = Suc(tl.n)
        
    def append(self,xs) :
        return VCons(self.hd,self.tl.append(xs))
        
    def lookup(self,i) :
        return i.lookupCons(self)
        
        
        
        
        
        
        
        
    
    
    
        
        
    
    
    
    
    
    
    
    
    
    
    
    
    
    

