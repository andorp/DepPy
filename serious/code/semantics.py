#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 17:17:40 2024

@author: psztxa
"""

class Value :

    "equal : Value -> Value -> Bool"

    def equalExpr(self,other) :
        return False
    
    def equalObject(self,other) :
        return False
   

class Object (Value) :
    
    def equal(self,other):
        return other.equalObject(self)
        
    def equalPureObject(self,other) :
        return False

    def equalClassObject(self,other) :
        return False

    def equalObjectClassObject(self,other) :
        return False

    def equalMethodObject(self,other) :
        return False

class PureObject(Object):
    
    def __init__(self,aclass,state) :
        self.aclass = aclass
        self.state = state
    
    def __repr__(self) :
        return f"PureObject({self.aclass},{self.state})"
    
    
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
                
    def equalObject(self,other):
        return other.equalPureObject(self)
        
    def equalPureObject(self,other) :
        if self.aclass.equal(other.aclass) and self.state.keys() == other.state.keys() :
            for x in self.state :
                if not self.state[x].equal(other.state[x]) :
                    return False
            return True
        else :
            return False
    
class ClassObj (Object) :
    
    def __init__(self,asuper,instvars,methods,name="") :
        self.asuper = asuper
        self.instvars = instvars
        self.methods = methods
        self.name = name
        
    def apply(self,args) :
           return PureObject(self , 
                    { p : x for (p,x) in zip(self.instvars,args) })
 
    def __repr__(self) :
#        return f"ClassObj(name={self.name},..)"
        return f"ClassObj({self.asuper},{self.instvars},{self.methods})"
        
    def equalObject(self,other):
        return other.equalClassObject(self)
        
    def equalClassObject(self,other) :
        return self.name == other.name      
"""
        if self.asuper.equal(other.asuper) and \
           self.instvars == other.instvars and \
           self.methods.keys() == other.methods.keys() :
               for x in self.methods :
                  if not self.methods[x].equal(other.methods[x]) :
                    return False
               return True
        else :
            return False
"""        
class ObjectClassObj(Object) :
    
    def equalObject(self,other):
        return other.equalObjectClassObject(self)
 
    def equalObjectClassObject(self,other) :
        return True
    
class MethodObj(Object) :
    
    def __init__(self,params,expr,env,name="") :
        self.params = params
        self.expr = expr
        self.env = env
        self.name = name

    def __repr__(self) :
#        return f"MethodObj(name={self.name},..,{self.env})"
        return f"MethodObj({self.params},{self.expr},{self.env})"


    def apply(self,args) :
        env = dict(self.env)
        env.update({ p : x for (p,x) in zip(self.params,args)})
        return self.expr.eval(env)
            
    def applySelf(self,aself) :
        env = dict(self.env)
        env[self.params[0]] = aself
        return MethodObj(self.params[1:],self.expr,env)
    
    def equalObject(self,other):
        return False
#        return other.equalMethodObject(self)
    
    # def equalMethodObject(self,other) :
    #     from code.syntax import Var
    #     return self.params == other.params and \
    #            self.expr.equal(other.expr)
        
"""    
    def equalMethodObject(self,other) :
        
        from code.syntax import Var
        if self.params == other.params :
           selfEnv = dict(self.env)
           otherEnv = dict(other.env)
           for x in self.params :
               selfEnv[x] = Var(x)
               otherEnv[x] = Var(x)
           return self.expr.eval(selfEnv).equal(other.expr.eval(otherEnv))
        else :
           return False
"""        
 # Todo : alpha conversion by zipping"      
        
    
objectClass = ObjectClassObj()
