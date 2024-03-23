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
        
    def __repr__(self) :
        return f"Init({self.params})"
        
    
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
    
    def __repr__(self) :
        return f"Method({self.params},{self.ret})"

class Closure :
    def __init__(self,method,myself) :
        self.method = method
        self.myself = myself
        
    def apply(self,objs,env) :
        # objs : List Object
        localenv = env.copy()
        localenv.update(dict(zip(self.method.params,[self.myself]+list(objs))))
        return self.method.ret.eval(localenv)
    
       
class Expr :
    pass
    # eval (self : Expr , env : Dict (String , Object))
class Id (Expr) :
    def __init__(self,name) :
        # name : String
        self.name = name

    def eval(self,env) :
        return env[self.name]
    
    def __repr__(self) :
        return f"Id({self.name})"
            
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
            theclass = obj.myclass
            while True :
             try : 
                return Closure(theclass.state["methods"][self.f],obj)
             except KeyError :
                theclass = theclass.state["super"] 
            
#          return Closure(obj.myclass.state["methods"][self.f],obj)
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
        
    def __repr__(self) :
        return f"Dot({self.e},{self.f})"
 
" zero.add" 
           
class Apply(Expr) :
    def __init__(self,e,args) :
        # e : Expr
        # args : List Expr
        self.e = e
        self.args = args

    def eval(self,env) :
        return self.e.eval(env).apply(map(lambda x:x.eval(env),self.args),env)     
#       self.e.eval(env).apply(map(lambda x:x.eval(env),self.args))     

    def __repr__(self) :
        return f"Apply({self.e},{self.args})"

                     

class Object :
    
    # myClass : Object
    def mkClass(name,supper,inits,methods) :
        # Name is only for debugging
        return Instance(MetaClass(),{"name":name,"super":supper,"inits":inits,"methods":methods})
      
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
        # return f"Instance(myclass={self.myclass},state={self.state})"
        return f"Instance({self.myclass.state.get("name","???")},state={self.state})"
    
# example
class Nat : # abstract: no __init__!
 
    pass
# end example

# need to write an evaluator for classes

env = {}

#env["Nat"] = Object.mkClass(Object.objectClass(),[],[]) #Instance(MetaClass(Nat),{}) # refactor 
env["Nat"] = Object.mkClass(
    name="Nat",
    supper=Object.objectClass(),
    inits=Init([]),
    methods={}
) #Instance(MetaClass(Nat),{}) # refactor 


# example
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
# end example


env["Zero"] = Object.mkClass(
    name="Zero",
    supper=env["Nat"],
    inits=Init([]), # TODO: Add init code
    methods=
      { "add": Method(["self","m"],Id("m"))}
)

# example
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
        
# end example

env["Succ"] =  Object.mkClass(
    name="Succ",
    supper=env["Nat"],
    inits=Init(["n"]),
    methods={
        "add": Method(
            params=["self","m"],
            ret=Apply(
                Id("Succ"),
                [ Apply(Dot(Dot(Id("self"),"n"),"add"),[Id("m")])
                ]
            )
        )
    }
)

zero = Zero() # example    
env["zero"] = Apply(Id("Zero"),[]).eval(env) 

tst = zero.add(zero)
env["tst"] = Apply(Dot(Id("zero"),"add"),[Id("zero")]).eval(env) 


one = Succ(zero) # example                           
env["one"] = Apply(Id("Succ"),[Id("zero")]).eval(env) 

two = one.add(one) # example
env["two"] = Apply(Dot(Id("one"),"add"),[Id("one")]).eval(env) 


#example
class A :

    def mm (self) :
        return zero
    
class B (A) :
    
    pass

tst2 = B().mm()
# end example

env["A"] = Object.mkClass("A",Object.objectClass(),Init([]),
                     {"mm": Method(["self"],Id("zero"))})

env["a"] = Apply(Id("A"),[]).eval(env)

env["tst2"] = Apply(Dot(Id("a"),"mm"),[]).eval(env)


env["B"] = Object.mkClass("B",env["A"],Init([]),{})

env["b"] = Apply(Id("B"),[]).eval(env)
 
env["tst3"] = Apply(Dot(Id("b"),"mm"),[]).eval(env)


# example
# Heterogenous vector
class Vector :
    # n : Nat
    pass

class VNil (Vector) :
    def __init__(self):
        # self.n = Zero
        pass

    # append(ys) : Vector
    # append(ys).n = ys.n
    def append(self,ys):
        # ys : Vector
        return ys

class VCons (Vector) :
    
    def __init__(self,x,xs):
        # xs : Vector
        # self.n = Succ(xs.n)
        self.x  = x
        self.xs = xs

    # append(ys) : Vector
    # append(ys).n = self.xs.n.add(ys.n)
    def append(self,ys):
        # ys : Vector
        return VCons(self.x,self.xs.append(ys))
# end example

env["Vector"] = Object.mkClass(
    name="Vector",
    supper=Object.objectClass(),
    inits=Init([]),
    methods={}
)

env["VNil"] = Object.mkClass(
    name="VNil",
    supper=env["Vector"],
    inits=Init([]), # TODO: Add init code
    methods=
      { "append": Method(
            params=["self","ys"],
            ret=Id("ys")
          )
      }
)

env["VCons"] = Object.mkClass(
    name="VCons",
    supper=env["Vector"],
    inits=Init(["x","xs"]),
    methods=
      { "append": Method(
            params=["self","ys"],
            ret=Apply(
                Id("VCons"),
                [ Dot(Id("self"),"x")
                , Apply(
                    Dot(Dot(Id("self"),"xs"),"append"),
                    [Id("ys")])
                ])
          )
      }
)

env['v0'] = Apply(Id("VNil"),[]).eval(env)
env['v1'] = Apply(Id("VCons"),[Id("one"),Id("v0")]).eval(env)
env['v2'] = Apply(Dot(Id("v1"),"append"),[Id("v1")]).eval(env)
# print(env["two"])
