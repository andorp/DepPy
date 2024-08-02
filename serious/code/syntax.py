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

    # eval : Program -> Object
    def eval(self) : 
        env = {"Object":objectClass}
        for name in self.classes:
            env[name] = self.classes[name].eval(env)
        # use destructive update to enable mutual recursion
        return self.main.eval(env)

class Class :
    def __init__(self,parent,instvars,methods):
        # parent : str
        # instvars : list str
        # methods : dict String method
        self.parent = parent
        self.instvars = instvars
        self.methods = methods

    def __repr__(self) :
        return f"Class({self.parent},{self.instvars},{self.methods})" 

    # eval : Class -> Dict str Object -> Object      
    def eval(self,env) :
        return ClassObj(env[self.parent],self.instvars,
                     {p : self.methods[p].eval(env) for p in self.methods.keys()})
    
class Method : 
    def __init__(self,params,body):
        # args : list str
        # body : expr
        self.params = params
        self.body = body
        
    def __repr__(self) :
        return f"Method({self.params},{self.body})"       
    
    # eval : Method -> Dict str Object -> Dict str Object  -> Object
    def eval(self,env) :
        return MethodObj(self.params,self.body,env)
        
class Expr : # abstract
    pass

    # eval : Expr -> Dict str Object -> Dict str Object -> Dict str Object -> Object
    # def eval(self,classenv,methenv,locenv) :
    #     return Object("test",{"x":1})   

class Var (Expr) :
    def __init__(self,name) :
        # name : str
        self.name = name

    def __repr__(self) :
        return f"Var({self.name})"           
    
    def eval(self,env) :
        return env[self.name]
      
class Dot (Expr) :
    def __init__(self,expr,field) :
        # expr : Expr
        # field : str
        self.expr = expr
        self.field = field

    def __repr__(self) :
        return f"Dot({self.expr},{self.field})"        

    def eval(self,env) :
        v = self.expr.eval(env)
        try : 
            return v.state[self.field]
        except KeyError :
            aclass = v.aclass
            while True :
                try :
                  return aclass.methods[self.field].applySelf(v)
                except KeyError :
                    aclass = aclass.asuper
                    continue
                # catch none error, return own error

class Apply(Expr) :
    def __init__(self,expr,args) :
        # e : Expr
        # args : list Expr
        self.expr = expr
        self.args = args
 
    def eval(self,env) :
        return self.expr.eval(env).apply([arg.eval(env) for arg in self.args])
           