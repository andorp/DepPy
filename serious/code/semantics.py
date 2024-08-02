#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 17:17:40 2024

@author: psztxa
"""

class Object :
    
    def __init__(self,aclass,state) :
        self.aclass = aclass
        self.state = state
    
    def applySelf(self,aself) :
        return self
    
class ClassObj (Object) :
    
    def __init__(self,asuper,instvars,methods) :
        self.asuper = asuper
        self.instvars = instvars
        self.methods = methods
        
    def apply(self,args) :
           return Object(self , 
                    { p : x for (p,x) in zip(self.instvars,args) })
    
class MethodObj(Object) :
    
    def __init__(self,params,expr,env) :
        self.params = params
        self.expr = expr
        self.env = env

    def apply(self,args) :
        env = dict(self.env)
        env.update({ p : x for (p,x) in zip(self.params,args)})
        return self.expr.eval(env)
            
    def applySelf(self,aself) :
        env = dict(self.env)
        env[self.params[0]] = aself
        return MethodObj(self.params[1:],self.expr,env)
    
objectClass = ClassObj(None,[],{})
