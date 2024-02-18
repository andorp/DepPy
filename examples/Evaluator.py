#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Feb 16 17:03:44 2024

@author: psztxa
"""

class Class :
    pass

class ConcreteClass (Class) :
    def __init__(self,super,init,methods):
        # super : Class
        # init : Init
        # methods : Dict(String,Method)
        self.super = super
        self.init = init
        self.methods = methods

class AbstractClass (Class) :
        def __init__(self,super,methods):
            # super : Class
            self.super = super
            self.methods = methods

class Object (Class) :
    pass

class Init :
    def __init__(self,params) :
        # instVars : List(String)
        self.params = params
    
class Method : 
    def __init__(self,params,ret) :
        # params : List String
        # body : Expr
        self.params = params
        self.ret = ret
 
       
class Expr :
    pass
    
class Id (Expr) :
    def __init__(self,name) :
        # name : String
        self.name = name
            
class Dot (Expr) :
    def __init__(self,e,f) :
        # e : Expr
        # f : String
        self.e = e
        self.f = f
            
class Apply(Expr) :
    def __init__(self,e,args) :
        # e : Expr
        # args : List Expr
        self.e = e
        self.args = args
                     

"""
class Nat : # abstract: no __init__!
 
    pass
"""

Nat = AbstractClass(Object,[])

"""
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
"""

Zero = ConcreteClass(Nat,Init([]),
                     {"add": Method(["self","m"],Id("m"))})

"""
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
"""

Succ = ConcreteClass(Nat,Init(["n"]),
                     {"add":Method(["self","m"],
                        Apply(Id("Succ"),
                              [Apply(Dot(Dot(Id("self"),"n"),"m"),[Id("m")])]))})
                                          
                                          
                                          