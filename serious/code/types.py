#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Nov 15 15:39:23 2024

@author: psztxa
"""
from code.syntax import *

class EType : # expression types
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
    "check : (self,Con,String) Void"
        
    pass
    
class IVarDecl (ClassComp) :
    def __init__(self,ety):
        # ety : EType
        self.ety = ety

    def check(self,con,var) :
        self.ety.check(con)
        
class MethodDecl (ClassComp) :
    def __init__(self,mtype)       :
         # mtype : MType
         self.mtype = mtype

    def check(self,con,var) :
        self.mtype.check(tclasses,con)
        
class MethodDef (ClassComp) :
    def __init__(self,mdef)       :
         # mdef : Method
        self.mdef = mdef

    def check(self,con,var) :
        mtype = con.lookupMtype(var)  
        con = con.addTvar(mtype.self_var,SelfType())
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
                loop(tvars[1:],params[1:],con.addVar(tvars[0]))
        loop(mtype.tel,self.mdef.params,con)
        # lookup method type
        # loop thorough the params and check each type
        # add the assumption that the parametr has the given type
        
class TProgram :
    "tclasses : List (String , TClass) "
    "mtype : EType"
    "main : Expr"
    
    def __init__(self,tclasses,mtype,main) :
        self.tclasses = classes
        self.mtype = mtype
        self.main = main
        
    "check : self -> Void"
    def check(self) :
        def loop(tclasses,con) :
            if tclasses == [] :
                return
            else :
                tclasses[0][0].check(con)
                loop(tclasses[1:],con.addClass(tclasses[0]))
        loop(tclasses,emptyCon)

class TClass :
    
    def __init__(self,parent,comps,name="") :
        # parent : String
        # comps : List (String,ClassComp)
        # name : String
        self.parent = parent
        self.comps = comps
        self.name = name

    "check : self -> Con -> Void"

    def check(self,con) :
        def loop(comps,con) :
            if comps==[] :
                return
            else :
                comps[0][1].check(con,comps[0][0])
                loop(comps[1:],ch_comps.addComp(comps[0]))
        loop(self.comps,con)

class Context :
    
    "classes : Dict TClass"
    "comps : Dict ClassComp"
    "tvars : Dict EType"
    
    def __init__(self, classes, comps, tvars) :
        self.classes= classes
        self.comps = comps
        self.tvars = tvars        

    "addClass : (self , (String,TClass)) -> Con"        
    def addClass(self,pair) :
        return Context(self.classes.copy()[pair[0]]=pair[1],self.comps,self.tvars)

    "addComp : (self , (String,ClassComp)) -> Con"        
    def addComp(self,pair) :
        return Context(self.classes,self.comps.copy()[pair[0]]=pair[1],self.tvars)

    "addVar : (self , (String,Ety)) -> Con"     
    def addVar(self,pair) :
        return Context(self.classes,self.comps,self.tvars.copy()[pair[0]]=pair[1])


def emptyCon() :
    return Context({},{},{})


add_ty = MethodType("self",[("n",Nat)],Nat)
     
tnat = TClass("Object",[("add",MethodDecl(add_ty))])
tzero = TClass("Nat",[("add",MethodDef(Method(["self","m"],Var("m"))))])
tsucc = TClass("Nat",[("n",IVarDecl(Nat)),
            ("add",MethodDef(
                    Method(["self","m"],
                        Apply(Var("Succ"),[Apply(Dot(Dot(Var("self"),"n"),"add"),[Var("m")])]))))])

    



