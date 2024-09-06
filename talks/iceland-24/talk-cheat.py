#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
			 Thorsten Altenkirch
		       University of Nottingham

		   Πthon - dependently typed Python

Created on Fri Sep  6 09:01:02 2024

@author: txa
"""

class Nat : 
    "add (Nat) :  Nat -> Nat"
    
    pass

class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
    
    def __repr__(self) :
        return "Zero()"
    
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
    
    def __repr__(self) :
        return f"Suc({self.n})"    
 
one = Succ(Zero())
two = Succ (one)
three = one.add(two)

class Fin :
    # n : Nat
    # lookupNil (self : Fin[.n = Zero]) : (xs : Vec) : vs.A 
    # lookupCons (self : Fin)  : (xs : VCons ) : v.A
    pass

    
class FZero :
    def __init__(self,m) :
        "m : Nat"
        self.n = Succ(m)
        pass

    def lookupNil(self) :
        raise TypeError("Impossible")

    def lookupCons(self,v) :
        return v.x

    def __repr__(self) :
        return "FZero({self.n})"


class FSucc :
    def __init__(self,f) :
        self.n = Succ(f.n)
        self.f = f
        
    def lookupNil(self) :
        raise TypeError("Impossible TODO Explain")

    def lookupCons(self,v) :
        return v.xs.lookup(self.f)

    def __repr__(self) :
        return f"FSucc({self.f})"    

class Vector :
    # self.A : type
    # self.n : Nat
    pass

    # append(self : Vactor) : (ys : Vector) -> Vector [.n = self.n.add(ys.n)]
    # lookup((self : Vector) : (i : Fin [.n = self.n]) : self.A

class VNil (Vector) :
    def __init__(self , A):
        self.A = A
        self.n = Zero

    def append(self,ys):
        return ys
        # CHECK ys.n = self.n.add(ys.n) 
        #            = zero.add(ys.n) = ys.n

    def lookup(self,i) :
        return i.lookupNil(self)

    def __repr__(self) :
        return f"VNil({self.A})"


class VCons (Vector) :
    
    def __init__(self,x,xs):
        # xs : Vector
        self.n = Succ(xs.n)
        self.A = xs.A
        self.x  = x
        self.xs = xs

    # append(ys) : Vector
    # append(ys).n = self.xs.n.add(ys.n)
    def append(self,ys):
        # ys : Vector
        return VCons(self.x,self.xs.append(ys))
        # CHECK VCons(self.x,self.xs.append(ys)).n = self.n.add(ys.n)]
        # VCons(self.x,self.xs.append(ys)).n 
        # = Succ(self.xs.append(ys).n)
        # = Succ(xs.n.add(ys.n))
        # self.n.add(ys.n) = Succ(xs.n).add(ys.n)
        # = Succ(xs.n.add(ys.n))
    
    def lookup(self,i) :
        return i.lookupCons(self)
 
    def __repr__(self) :
        return f"VCons({self.x},{self.xs})"
    
 
xs = VCons(one,VNil(Nat))
zeroF = FZero(one)
xs.lookup(zeroF)
