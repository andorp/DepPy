#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 17:17:40 2024

@author: psztxa
"""

class Object :
    def __init__(self,atype,env):
        # type : str
        # env : dict String Object
        self.atype = atype
        self.env = env
        
    def __repr__(self) :
        return f"Object({self.atype},{self.env})"
    
# evalClasses : dict String Class -> dict String object
def evalClasses (classes) :
    env = {}
    for x in classes :
        env[x]= classes[x].eval(env)
    return env

# mkClass : Class -> dict String Object -> Object
def mkClass (aclass,classenv) :
    methenv = {}
    for x in aclass.methods :
        methenv[x] = aclass.methods[x].eval(classenv,methenv)    
    return Object("class",{"parent":aclass.parent,"instvars":aclass.instvars,"methods":methenv})

# mkClosure : Expr -> -> dict String Object -> dict String Object -> dict String Object -> Object
def mkClosure(expr,classes,methods,local) :
    return Object("Closure",{"expr":expr,"classes":classes,"methods":methods,"local":local})

# mkMethod : Method -> dict String Object -> dict String Object -> Object
def mkMethod(method,classes,methods) :
    return Object("Method",{"args":method.args,"body":mkClosure(method.body,classes,methods,{})})
