#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 17:17:40 2024

@author: psztxa
"""

class Value :
    pass


class Object (Value) :
    
    def __init__(self,aclass,state) :
        self.aclass = aclass
        self.state = state
    
    def __repr__(self) :
        return f"Object({self.aclass},{self.state})"
    
    
    def applySelf(self,aself) :
        return self
    
    def evalDot(self,field) :
        try : 
            return self.state[field]
        except KeyError :
            aclass = self.aclass
            while True :
                try :
                  return aclass.methods[field].applySelf(self)
                except KeyError :
                    aclass = aclass.asuper
                    continue
                # catch none error, return own error
    
class ClassObj (Object) :
    
    def __init__(self,asuper,instvars,methods,name="") :
        self.asuper = asuper
        self.instvars = instvars
        self.methods = methods
        self.name = name
        
    def apply(self,args) :
           return Object(self , 
                    { p : x for (p,x) in zip(self.instvars,args) })
 
    def __repr__(self) :
        return f"ClassObj(name={self.name},..)"
#        return f"ClassObj({self.asuper},{self.instvars},{self.methods})"
     
    
class MethodObj(Object) :
    
    def __init__(self,params,expr,env,name="") :
        self.params = params
        self.expr = expr
        self.env = env
        self.name = name

    def __repr__(self) :
        return f"MethodObj(name={self.name},..,{self.env})"
#        return f"MethodObj({self.params},{self.expr},{self.env})"


    def apply(self,args) :
        env = dict(self.env)
        env.update({ p : x for (p,x) in zip(self.params,args)})
        return self.expr.eval(env)
            
    def applySelf(self,aself) :
        env = dict(self.env)
        env[self.params[0]] = aself
        return MethodObj(self.params[1:],self.expr,env)
    
objectClass = ClassObj(None,[],{})
