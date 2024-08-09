#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 16:14:15 2024

@author: psztxa
"""
import unittest
from code.syntax import *

class Nat : 
    pass

class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m
    
    def __repr__(self) :
        return "Zero()"
    
class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
    
    def __repr__(self) :
        return f"Suc({self.n})"    
    
one = Succ(Zero())
two = Succ (one)
three = one.add(two)

oneCode = Apply(Var("Succ"),[Apply(Var("Zero"),[])])
twoCode = Apply(Var("Succ"),[oneCode])
threeCode = Apply(Dot(oneCode,"add"),[twoCode])

classdefs = {
    "Nat":Class("Object",[],{},name="Nat"),
    
    "Zero":Class("Nat",[],
        {"add":Method(["self","m"],Var("m"),name="Zero.add")},
        name="Zero"),
    
    "Succ":Class("Nat",["n"],
        {"add":Method(["self","m"],Apply(Var("Succ"),[Apply(Dot(Dot(Var("self"),"n"),"add"),[Var("m")])]),
             name="Succ.add")},
        name="Succ")
}

zero_code = Apply(Var("Zero"),[])
one_code = Apply(Var("Succ"),[zero_code])
env = {"x" : Var("x"),"f" : Var("f")}


class Test(unittest.TestCase) :
    
    def test1(self):
        """
        Checks is looking up the Nat leads to a Class object, which doesn't have any instance variables nor methods.
        """
        result = Program(classdefs,Var("Nat")).eval()
        # self.assertEqual(result.atype,"class")
        self.assertEqual(result.instvars,[])
        self.assertEqual(result.methods,{})

    def test2(self):
        """
        Checks if looking up Zero leads to a its class representation
        """
        result = Program(classdefs,Var("Zero")).eval()
        # self.assertEqual(result.atype,"class")
        self.assertEqual(result.instvars,[])
        self.assertNotEqual(result.asuper, None)
        add = result.methods["add"]
        self.assertEqual(add.params,['self','m'])

    def test3(self):
        """
        Checks if evaluation of Zero constructor leads to the zero object.
        """
        result = Program(classdefs,zero_code).eval()
        #self.assertEqual(result.atype,"object")
        self.assertEqual(result.state,{})

    def test4(self):
        """
        Checks if one has a non-empty n field.
        """
        result = Program(classdefs,one_code).eval()
        # self.assertEqual(result.atype,"object")
        self.assertIn("n",result.state)

    def test5(self):
        """
        Checks if looking up n from one leads to zero.
        """
        result = Program(classdefs,(Dot(one_code,"n"))).eval()
        # self.assertEqual(result.atype,"object")
        self.assertEqual(result.state,{})

    def test6(self):
        """
        Checks if referencing a function from the zero object leads to a method of two parameters.
        """
        result = Program(classdefs,Dot(zero_code,"add")).eval()
        # self.assertEqual(result.atype,"method")
        # Dot applies the first argument and removes it from the active parameter list.
        self.assertEqual(result.params,['m'])
        # And adds the first argument to the local environment.
        self.assertIn("self",result.env)

    def test7(self):
        """
        Checks if calling the add method on the zero object leads to the zero result.
        """
        result = Program(classdefs,Apply(Dot(zero_code,"add"),[zero_code])).eval()
        #self.assertEqual(result.atype,"object")
        self.assertEqual(result.state,{})

    def test8(self) :
        """
        Evaluating a variable
        """
        result = Program(classdefs,Var("x")).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})     
        
    def test9(self) :
        """
        Evaluating a stuck dot
        """
        result = Program(classdefs,Dot(Var("x"),"n")).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})     

    def test10(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Var("f"),[zero_code])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})    

    def test11(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Var("Succ"),[Var("x")])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})   
        
    def test12(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Dot(zero_code,"add"),[Var("x")])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})           

    def test13(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Dot(Var("x"),"add"),[zero_code])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
#        self.assertEqual(result.state,{})           
        
    def test14(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,zero_code).eval()
        #self.assertEqual(result.atype,"object")
        print(result)
        print(result.equal(result))
#        self.assertEqual(result.state,{})   
        
        
    def test15(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Var("x")).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
        print(result.equal(result))
#        self.assertEqual(result.state,{})   
        
    def test16(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Var("Succ"),[Var("x")])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
        print(result.equal(result))
#        self.assertEqual(result.state,{})  
        
    def test17(self) :
        """
        Evaluating a stuck apply
        """
        result = Program(classdefs,Apply(Var("Succ"),[Var("x")])).eval(env)
        #self.assertEqual(result.atype,"object")
        print(result)
        print(result.equal(result))
#        self.assertEqual(result.state,{})  

if __name__ == '__main__':
    unittest.main()
