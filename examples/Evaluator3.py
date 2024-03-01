#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Feb 16 17:03:44 2024

@author: psztxa
"""

class Class :
    pass

"""
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
"""

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
        
    def apply(self,objs,env) :
        # objs : List Object
        localenv = env.copy()
        localenv.update(dict(zip(self.params,objs)))
        return self.ret.eval(localenv)
       
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
        obj = self.e.eval(env)
        try :
          return obj.state[self.f]
        except KeyError :
          return obj.myclass.state["methods"][self.f]
        """
        try :
            return self.e.eval(env).state[self.f]
        # lookup through classes
        except KeyError :
            theclass = self.e.eval(env).myclass
            while True :
                try : 
                    return theclass.state["methods"][self.f]
                except KeyError :
                 theclass = theclass["super"] 
                 # refactor using class objects only, super is an instance variable
        """
class Apply(Expr) :
    def __init__(self,e,args) :
        # e : Expr
        # args : List Expr
        self.e = e
        self.args = args

    def eval(self,env) :
        return self.e.eval(env).apply(map(lambda x:x.eval(env),self.args),env)     
#       self.e.eval(env).apply(map(lambda x:x.eval(env),self.args))     
                     

class Object :
    # myClass : Object
    def mkClass(supper,inits,methods) :
        return Instance(MetaClass(),{"super" : supper,"inits" : inits,"methods" : methods})
      
    def objectClass() :
        return Instance(MetaClass(),{})
  

class MetaClass (Object) :
    
    def __init__(self) :
        self.myclass = self
        
    def __repr__(self) :
        return "MetaClass()"
       
class Instance (Object) :
      
    def __init__(self,myclass,state) :
        # myclass : Object
        # state : Dict (String , Object)
        self.myclass = myclass
        self.state = state
        
    def apply(self,objs,env) :
        # self.class = MetaClass (assertion)
        return Instance(self,dict(zip(self.state["inits"].params,objs)))
        #return Instance(self.theclass,dict(zip(self.theclass.init.params,objs)))
        
    def __repr__(self) :
        return f"Instance({self.myclass},{self.state})"
    
  
class Closure(Object) :
    
    def __init__(self,body) :
        # body : Method
        self.body = body

    def apply(self,objs,env) :
        # objs : List Object
        return self.body.apply(objs,env)
        

    # myclass.methods

"""
class Nat : # abstract: no __init__!
 
    pass
"""

# need to write an evaluator for classes

env = {}

env["Nat"] = Object.mkClass(Object.objectClass(),[],[]) #Instance(MetaClass(Nat),{}) # refactor 


"""
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
"""

env["Zero"] = Object.mkClass(env["Nat"],Init([]),
                     {"add": Method(["self","m"],Id("m"))})

"""
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
        
"""

env["Succ"] =  Object.mkClass(env["Nat"],
                   Init(["n"]),
                     {"add":Method(["self","m"],
                        Apply(Id("Succ"),
                              [Apply(Dot(Dot(Id("self"),"n"),"m"),[Id("m")])]))})

# zero = Zero()    
env["zero"] = Apply(Id("Zero"),[]).eval(env) 

tst = Apply(Dot(Id("zero"),"add"),[Id("zero")]).eval(env) 
"""              
# one = Succ(zero)                           
env["one"] = Apply(Id("Succ"),[Id("zero")]).eval(env) 

# one.add(one)
env["two"] = Apply(Dot(Id("one"),"add"),[Id("one")]).eval(env) 
"""
    
    