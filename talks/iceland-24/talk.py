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
        
        
    
    
    
    
    
    
    
    
    
    
    
    
    
    

