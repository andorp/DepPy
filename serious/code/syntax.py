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

    # eval : Program -> Dict str Value -> Value
    def eval(self,env = {}):
        env["Object"] = objectClass
        for name in self.classes:
            env[name] = self.classes[name].eval(env)
        # use destructive update to enable mutual recursion
        return self.main.eval(env)

class Class :
    def __init__(self,parent,instvars,methods,name=""):
        # parent : str
        # instvars : list str
        # methods : dict String method
        self.parent = parent
        self.instvars = instvars
        self.methods = methods
        self.name = name

    def __repr__(self) :
        return f"Class({self.parent},{self.instvars},{self.methods})" 

    # eval : Class -> Dict str Object -> Object      
    def eval(self,env) :
        return ClassObj(env[self.parent],self.instvars,
                     {p : self.methods[p].eval(env) for p in self.methods.keys()},
                     name=self.name)
    
class Method : 
    def __init__(self,params,body,name=""):
        # args : list str
        # body : value
        self.params = params
        self.body = body
        self.name = name
        
    def __repr__(self) :
        return f"Method({self.params},{self.body})"       
    
    # eval : Method -> Dict str Object -> Dict str Object  -> Object
    def eval(self,env) :
        return MethodObj(self.params,self.body,env,name=self.name)
        
class Expr (Value): # abstract
    pass

    # eval : Expr -> Dict str Value -> Value
    # def eval(self,classenv,methenv,locenv) :
    #     return Object("test",{"x":1})   

    def evalDot(self,field) :
        return Dot(self,field)

    def apply(self,values) :
        return Apply(self,values)

class Var (Expr) :
    def __init__(self,name) :
        # name : str
        self.name = name

    def __repr__(self) :
        return f"Var({self.name})"           
    
    def eval(self,env) :
        return env[self.name]
 
      
class Dot (Expr) :
    def __init__(self,value,field) :
        # value : Value
        # field : str
        self.value = value
        self.field = field

    def __repr__(self) :
        return f"Dot({self.value},{self.field})"        

    def eval(self,env) :
        return self.value.eval(env).evalDot(self.field)


class Apply(Expr) :
    def __init__(self,value,args) :
        # e : Expr
        # args : list Expr
        self.value = value
        self.args = args
        
    def __repr__(self) :
        return f"Apply({self.value},{self.args})"

    def eval(self,env) :
        return self.value.eval(env).apply([arg.eval(env) for arg in self.args])
           