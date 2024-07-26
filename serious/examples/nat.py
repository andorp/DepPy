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

classdefs = {"Nat":Class("Object",[],{}),
             "Zero":Class("Nat",[],{"add":Method(["self","m"],Var("m"))}),
             "Succ":Class("Nat",["n"],{"add":Method(["self","m"],Apply(Var("Succ"),[Apply(Dot(Dot(Var("self"),"n"),"add"),[Var("m")])]))})
               }

nat = Program(classdefs,threeCode)

# print(nat)
# print(nat.eval())
"""
e1 = Var("x")
env = {"x":1}
print(e1.eval({},{},env))
"""

"""
tst1 = Program(classdefs,Var("Nat"))
print(tst1.eval())


tst2 = Program(classdefs,Var("Zero"))
print(tst2.eval())
"""

zero_code = Apply(Var("Zero"),[])
"""
tst3 = Program(classdefs,zero_code)
print(tst3.eval())
"""

one_code = Apply(Var("Succ"),[zero_code])
"""
tst4 = Program(classdefs,one_code)
#print(tst4.eval())
print(tst4.eval().env["state"])


tst5 = Program(classdefs,(Dot(one_code,"n")))
print(tst5.eval())


tst6 = Program(classdefs,Dot(zero_code,"add"))
print(tst6.eval())
"""

tst7 = Program(classdefs,Apply(Dot(zero_code,"add"),[zero_code]))
print(tst7.eval())
# we need to pass self!




