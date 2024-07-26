#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 15:44:24 2024

@author: psztxa
"""
from code.semantics import *

class Program :
    def __init__(self,classes,main) :
        # classes : dict str Class
        # main : Expr
        self.classes = classes
        self.main = main
        
    def __repr__(self) :
        return f"Program({self.classes},{self.main})"

    # eval : Program -> Dict str object
    def eval(self) : 
        return self.main.eval(evalClasses(self.classes),{},{})

class Class :
    def __init__(self,parent,instvars,methods):
        # super : str
        # instvars : list str
        # methods : dict String method
        self.parent = parent
        self.instvars = instvars
        self.methods = methods

    def __repr__(self) :
        return f"Class({self.parent},{self.instvars},{self.methods})" 

    # eval : Class -> Dict str Object -> Object      
    def eval(self,classenv) :
        return mkClass(self,classenv)
    
class Method : 
    def __init__(self,args,body):
        # args : list str
        # body : expr
        self.args = args
        self.body = body
        
    def __repr__(self) :
        return f"Method({self.args},{self.body})"       
    
    # eval : Method -> Dict str Object -> Dict str Object  -> Object
    def eval(self,classenv,methenv) :
        return mkMethod(self,classenv,methenv)
        
class Expr : # abstract
    pass

    # eval : Expr -> Dict str Object -> Dict str Object -> Dict str Object -> Object
    def eval(self,classenv,methenv,locenv) :
        return Object("test",{"x":1})   
    

class Var (Expr) :
    def __init__(self,name) :
        # name : str
        self.name = name

    def __repr__(self) :
        return f"Var({self.name})"           
    
        
class Dot (Expr) :
    def __init__(self,expr,field) :
        # e : Expr
        # f : str
        self.expr = expr
        self.field = field

    def __repr__(self) :
        return f"Dot({self.expr},{self.field})"        
        
class Apply(Expr) :
    def __init__(self,expr,args) :
        # e : Expr
        # args : list Expr
        self.expr = expr
        self.args = args
 
    def __repr__(self) :
        return f"Apply({self.expr},{self.args})"        
       
        