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
        # methods : Dicti(String,Method)
        self.super = super
        self.init = init
        self.methods = methods

class AbstractClass (Class) :
        def __init__(self,super,init,methods):
            # super : Class
            self.super = super

class Object(Class) :
    pass

class Init :
    def __init__(self,instVars) :
        # params : List(String)
        # lets = List (String,Expr)
        self.params = InstVars
    
class Method : 
    def __init__(self,params,ret) :
        # params : List String
        # body : Expr
        self.params = params
        self.ret =ret
 
       
class Ref :
    pass
                
    def __init__(self, root,names) :
        # root : String
        # names : List(String)
        self.root = root
        self.names = names
        
class Expr :
    
    def __init__(self,m,args) :
        # m : Ref
        # args : List(Expr)
        self.m = m
        self.args = args
    
"""
class Nat : # abstract: no __init__!
 
    pass
"""

Nat = AbstractClass(Object)

"""
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
"""

Zero = ConcreteClass(Nat,Init([]),
                     {"add": Method(["self","m"],Expr(Ref("m",[]),[]))}) 

"""
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
"""

Succ = ConcreteClass(Nat,Init(["n"],
                     {"add":Method(["self","m"],Expr(Ref("Succ")))})