#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Nov 15 15:39:23 2024

@author: psztxa
"""
from code.syntax import *

class TError(Exception):
    "Type error"
    pass

class EType : # expression types

    def check(self,con) :
        pass

class IsClass(EType) :
    
    def __init__(self , classname ) :
        # classname : String
        self.classname = classname
        
class Constraint (EType) :
    
    def __init__(self, ety , ivar , expr):
        # ety : Etype
        # ivar : String
        # expr : Expr
        self.ety = ety
        self.ivar = ivar
        self.expr = expr
        
class MethodType (EType):
    
    def __init__(self , self_var, tel , ety ) :
        # self_var : String
        # tel : List ( String , ety )
        # ety : EType
        self.self_var = self_var
        self.tel = tel
        self.ety = ety
        
class El(EType) : # expr : Class => "El expr" is the type of instances
    # El = element of a class
    def __init__(self,expr) :
        self.expr = expr

class SelfType(EType) :
    def __init__(self) :
        pass
    

# Nat
Nat = IsClass("Nat")
#add_ty = MethodType([("self",Nat),("n",Nat)],Nat)
# add : (self:Nat,n :Nat) Nat
#add_ty = MethodType([("self",Nat),("n",Nat)],Nat)
# lookupNil (self : Fin[.n = Zero]) : (xs : Vec) : xs.A 
#zero_code = Apply(Var("Zero"),[])
#lookupNil_ty = MethodType([("self",Constraint(IsClass("Fin"),"n",zero_code)),
#                           ("xs",IsClass("Vec"))],
#                          El(Dot(Var("xs"),"A")))  

class ClassComp : #class component
    "check : (self,Con,String,CClass)CClass"
        
    pass
    
class IVarDecl (ClassComp) :
    def __init__(self,ety):
        # ety : EType
        self.ety = ety

    def check(self,con,var,cclass) :
        self.ety.check(con)
        return cclass.addTy(var,self.ety)
        
class MethodDecl (ClassComp) :
    def __init__(self,mtype)       :
         # mtype : MType
         self.mtype = mtype

    def check(self,con,var,cclass) :
        self.mtype.check(con)
        return cclass.addTy(var,self.mtype)

class MethodDef (ClassComp) :
    def __init__(self,mdef)       :
         # mdef : Method
        self.mdef = mdef

    def check(self,con,var,cclass) :
        mtype = con.con[var] # lookup method type
        con = con.add(mtype.self_var,SelfType())
        # loop through the params and check each type
        # add the assumption that the parametre has the given type
        def loop (tvars , params , con) :
            if tvars == [] :
                if params != [] :
                    raise TError("mdef : diff params(1)")
                return
            else :
                if params== [] :
                    raise TError("mdef : diff params(2)")
                if tvars[0][0] != params[0] :
                    raise TError("mdef : diff params(3)")
                tvars[0][1].check(con)
                loop(tvars[1:],params[1:],con.add(tvars[0]))
        loop(mtype.tel,self.mdef.params,con)
        self.mdef.body.check(con,ety)
        return cclass.addMethod(self,var,mdef)

                
class TProgram :
    "tclasses : List (String , TClass) "
    "main : Expr"
    
    def __init__(self,tclasses,mtype,main) :
        self.tclasses = classes
        self.main = main
        
    "infer : self -> Type"
    def check(self) :
        def loop(tclasses,con) :
            if tclasses == [] :
                return self.main.infer(con)  
            else :
                return loop(tclasses[1:],con.add(tclasses[0][0],
                            tclasses[0][0].check(con)))
        return loop(tclasses,Con({}))
        
class CClass : # checked class
    "types : Con"
    "methods : Con"
    def __init__(self,types,methods) :
        self.types = types
        self.methods = methods
        
    def addTy(self,var,ety):
        return CClass(self.types.add(var,ety),self.methods)
 
    def addMethod(self,var,method):
        return CClass(self.types,self.methods.add(var,method))
                      

class TClass :
    
    def __init__(self,parent,comps,name="") :
        # parent : String
        # comps : List (String,ClassComp)
        # name : String
        self.parent = parent
        self.comps = comps
        self.name = name

    "check : self -> Con -> CClass"

    def check(self,con) :
        def loop(comps,con,cclass) :
            if comps==[] :
                return cclass
            else :
                return loop(comps[1:],con.add(comps[0][0],comps[0][1]),
                            comps[0][1].check(con,comps[0][0],cclass))
        return loop(self.comps,con,CClass(Con({}),Con({})))
        
class Con :
    
    "con : Dict(Objects)"
    "just a functional wrapper for dictionaries"
    
    def __init__(self, con) :
        self.con= con

    "add : SELF ->  String -> Object  -> Con"      
    def add(self,var,obj) :
        newcon = self.con.copy()
        newcon[var]=obj
        return Con(newcon)



add_ty = MethodType("self",[("n",Nat)],Nat)
     
tnat = TClass("Object",[("add",MethodDecl(add_ty))])
tzero = TClass("Nat",[("add",MethodDef(Method(["self","m"],Var("m"))))])
tsucc = TClass("Nat",[("n",IVarDecl(Nat)),
            ("add",MethodDef(
                    Method(["self","m"],
                        Apply(Var("Succ"),[Apply(Dot(Dot(Var("self"),"n"),"add"),[Var("m")])]))))])

    



