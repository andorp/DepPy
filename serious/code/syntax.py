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
    def __init__(self,params,body):
        # args : list str
        # body : expr
        self.params = params
        self.body = body
        
    def __repr__(self) :
        return f"Method({self.params},{self.body})"       
    
    # eval : Method -> Dict str Object -> Dict str Object  -> Object
    def eval(self,classenv,methenv) :
        return mkMethod(self,classenv,methenv)
        
class Expr : # abstract
    pass

    # eval : Expr -> Dict str Object -> Dict str Object -> Dict str Object -> Object
    """
    def eval(self,classenv,methenv,locenv) :
        return Object("test",{"x":1})   
    """

class Var (Expr) :
    def __init__(self,name) :
        # name : str
        self.name = name

    def __repr__(self) :
        return f"Var({self.name})"           
    
    def eval(self,classenv,methenv,locenv) :
        try :
            return locenv[self.name]
        except KeyError :
          try :
            return methenv[self.name]
          except KeyError :
              return classenv[self.name]
        
class Dot (Expr) :
    def __init__(self,expr,field) :
        # e : Expr
        # f : str
        self.expr = expr
        self.field = field

    def __repr__(self) :
        return f"Dot({self.expr},{self.field})"        

    def eval(self,classenv,methenv,locenv) :
        v = self.expr.eval(classenv,methenv,locenv)
        if v.atype == "object" :
            try :
                return v.env["state"][self.field]
            except KeyError :
                return v.env["class"].env["methods"][self.field] # TODO: add self to local env
            
        
class Apply(Expr) :
    def __init__(self,expr,args) :
        # e : Expr
        # args : list Expr
        self.expr = expr
        self.args = args
 
    def eval(self,classenv,methenv,locenv) :
        m = self.expr.eval(classenv,methenv,locenv)
        if m.atype == "method" :           
            ps = m.env["params"]
            cl = m.env["body"]
            closLocEnv = cl.env["local"]
            for e in self.args :
                closLocEnv = update(closLocEnv,ps[0],e.eval(classenv,methenv,locenv))
                ps = ps[1:]  
            return cl.env["expr"].eval(cl.env["classes"],cl.env["methods"],closLocEnv)
        elif m.atype == "class" :
            ps = m.env["instvars"]
            state = {}
            for e in self.args :
              state = update(state,ps[0],e.eval(classenv,methenv,locenv))
              ps = ps[1:]
            return mkObject(m,state)
        else :
            raise TypeError(f"Method or class expected but found {m.atype}")
            
    
    def __repr__(self) :
        return f"Apply({self.expr},{self.args})"        
       
        