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

class ObjectClass (Class) :
    pass

class MetaClass (Class) :
    def __init__(self,theclass) :
        # theclass : Class
        self.theclass = theclass

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
        
    def apply(self,objs) :
        # objs : List Object
        self.ret.eval(dict(zip(self.params,objs)))
       
class Expr :
    pass
    # eval (self : Expr , env : Dict (String , Object))
class Id (Expr) :
    def __init__(self,name) :
        # name : String
        self.name = name

    def eval(self,env) :
        return env[self.name]
            
class Dot (Expr) :
    def __init__(self,e,f) :
        # e : Expr
        # f : String
        self.e = e
        self.f = f

    def eval(self, env) :
        # lookup in object
        try :
            return self.e.eval(env).state[self.f]
        # lookup through classes
        except KeyError :
            theclass = self.e.eval(env).myclass
            while True :
                try : 
                    return theclass.methods[self.f]
                except KeyError :
                 theclass = theclass.super
        
class Apply(Expr) :
    def __init__(self,e,args) :
        # e : Expr
        # args : List Expr
        self.e = e
        self.args = args

    def eval(self,env) :
       self.e.eval(env).apply(map(lambda x:x.eval(env),self.args))     
                     

class Object :
    pass
    
class Instance (Object) :
      
    def __init__(self,myclass,state) :
        # myclass : Class
        # state : Dict (String , Object)
        self.myclass = myclass
        self.state = state
        
    def apply(self,objs) :
        # self.class = MetaClass
        return Instance(self.theclass,dict(zip(self.theclass.init.params,objs)))
        
    
class Closure( Object) :
    
    def __init__(self,body) :
        # body : Method
        self.body = body

    def apply(self,objs) :
        # objs : List Object
        self.body.apply(objs)
        

    # myclass.methods

"""
class Nat : # abstract: no __init__!
 
    pass
"""

# need to write an evaluator for classes

env = {}

Nat = AbstractClass(ObjectClass,[])
env["Nat"] = Instance(MetaClass(Nat),{}) # refactor 


"""
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
"""

Zero = ConcreteClass(Nat,Init([]),
                     {"add": Method(["self","m"],Id("m"))})

env["Zero"] = Instance(MetaClass(Zero),{})
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
                                          
                                          
class C :
    x = 0
    
    def m(self) :
        return self.x
    
class D(C) :
    
    x = 1
    
    def m(self) :
        return self.x
    
    
    