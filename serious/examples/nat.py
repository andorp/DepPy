#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 16:14:15 2024

@author: psztxa
"""
from code.syntax import *

class Nat : 
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

oneCode = Apply(Var("Succ"),[Apply(Var("Zero"),[])])
twoCode = Apply(Var("Succ"),[oneCode])
threeCode = Apply(Dot(oneCode,"add"),[twoCode])

nat = Program({"Nat":Class(None,[],{}),
               "Zero":Class("Nat",[],{"add":Method(["self","m"],Var("m"))}),
               "Succ":Class("Nat",[],{"add":Method(["self","m"],Apply(Var("Succ"),[Apply(Dot(Dot(Var("self"),"n"),"add"),[Var("m")])]))})
               },threeCode)

print(nat)

print(nat.eval())