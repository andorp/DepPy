from Expr   import *
from Object import *

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
    inits=Init(constraints=[],params=[]),
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
    inits=Init(constraints=[],params=[]),
    methods={
        "add": Method(["self","m"],Id("m"))
    }
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
    inits=Init(constraints=[],params=["n"]),
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

env["A"] = Object.mkClass(
    name="A",
    supper=Object.objectClass(),
    inits=Init(constraints=[],params=[]),
    methods={"mm": Method(["self"],Id("zero"))}
)

env["a"] = Apply(Id("A"),[]).eval(env)
env["tst2"] = Apply(Dot(Id("a"),"mm"),[]).eval(env)

env["B"] = Object.mkClass(
    name="B",
    supper=env["A"],
    inits=Init(constraints=[],params=[]),
    methods={}
)

env["b"] = Apply(Id("B"),[]).eval(env)
env["tst3"] = Apply(Dot(Id("b"),"mm"),[]).eval(env)

# example
class Fin :
    # n : Nat
    # lookupNil [.self.n = Zero] : Any 
    # lookupCons (v : VCons [n = self.n]) : Any 
    pass

    

class FZero :
    def __init__(self) :
        # m : Nat
        # Field = expression
        # self.n = Succ(m)
        pass

    def lookupNil(self) :
        raise TypeError("Impossible TODO Explain")

    def lookupCons(self,v) :
        return v.x

    def elim(self,e):
        return e.FZero(self)

class FSucc :
    def __init__(self,f) :
        # f : Fin
        # self.n = Succ(f.n)
        self.f = f
        
    def lookupNil(self) :
        raise TypeError("Impossible TODO Explain")

    def lookupCons(self,v) :
        return v.xs.lookup(self.f)

    def elim(self,e):
        return e.FSucc(self)

class FinElim :
    def FZero(self,e:FZero):
        pass
    def FSucc(self,e:FSucc):
        pass

# end example

env['Fin'] = Object.mkClass(
    name="Fin",
    supper=Object.objectClass(),
    inits=Init(constraints=[],params=[]),
    methods={}
)

env['FZero'] = Object.mkClass(
    name="FZero",
    supper=env['Fin'],
    inits=Init(constraints=[],params=[]),
    methods={}
)

env['FSucc'] = Object.mkClass(
    name="FSucc",
    supper=env['Fin'],
    inits=Init(constraints=[],params=["f"]),
    methods={}
)

env['f0'] = Apply(Id("FZero"),[]).eval(env)
env['f1'] = Apply(Id("FSucc"),[Id("f0")]).eval(env)
env['f2'] = Apply(Id("FSucc"),[Id("f1")]).eval(env)

# example
# Heterogenous vector
class Vector :
    # self.n : Nat
    pass

    # append(ys : Vector) : Vector [.n = self.n.add(ys.n)]

    # lookup(i : Fin [.n = self.n]) : Any

class VNil (Vector) :
    def __init__(self):
        # self.n = Zero
        pass

    # append(ys) : Vector
    # append(ys).n = ys.n
    def append(self,ys):
        # ys : Vector
        return ys
        # CHECK ys.n = self.n.add(ys.n) 
        #            = zero.add(ys.n) = ys.n

    def lookup(self,i) :
        return i.lookupNil()

    def elim(self,e):
        return e.VNil(self)

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
        # CHECK VCons(self.x,self.xs.append(ys)).n = self.n.add(ys.n)]
        # VCons(self.x,self.xs.append(ys)).n 
        # = Succ(self.xs.append(ys).n)
        # = Succ(xs.n.add(ys.n))
        # self.n.add(ys.n) = Succ(xs.n).add(ys.n)
        # = Succ(xs.n.add(ys.n))
    
    def lookup(self,i) :
        return i.lookupCons(self)
    
    def elim(self,e):
        return e.VCons(self)
    
class VElim :
    def VNil(self,e:VNil):
        pass
    def VCons(self,e:VCons):
        pass
# end example

env["Vector"] = Object.mkClass(
    name="Vector",
    supper=Object.objectClass(),
    inits=Init(constraints=[],params=[]),
    methods={}
)

env["VNil"] = Object.mkClass(
    name="VNil",
    supper=env["Vector"],
    inits=Init(constraints=[],params=[]), 
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
    inits=Init(constraints=[],params=["x","xs"]),
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
# print(env["v2"])


# TODO: show constraints
"""
Lookup an element from a vector vect indexed by idx.
"""
"""
def lookup1(idx:Fin,vect:Vector) :
    # idx.n  : Nat
    # vect.n : Nat
    # idx.n = vect.n
    match (idx,vect) :
        case (FZero(),VNil()) :
            # idx.n  = Succ(m)
            # vect.n = Zero
            raise TypeError("Impossible TODO Explain")
        case (FZero(),VCons(x=y,xs=ys)) :
            # idx.n  = Succ(m)
            # vect.n = Succ(k)
            return y
        case (FSucc(f=a),VNil()) :
            # idx.n  = Succ(m)
            # vect.n = Zero
            raise TypeError("Impossible TODO Explain")
        case (FSucc(f=a),VCons(x=y,xs=ys)) :
            # idx.n  = Succ(m)
            # vect.n = Succ(k)
            return lookup1(a,ys)
"""

class Sgl :
    def __init__(self,val) :
        self.val = val
    
# a=b becomes Sgl(a)[.val = b] 
# Sgl(a) : Sgl(a)[a = a]
        
class Nat : # abstract: no __init__!
 
    # add(Nat) : Nat    
    
    # lneutr(self) : Sgl(Zero().add(self),self)
    def lneutr(self) :
        return Sgl(self) # Zero().add(self) = self
    
    # rneutr(self) : Sgl(self.add(Zero()),self)
        
    pass        
        
class Zero (Nat) : 

    def __init__(self) :
        pass

    def add(self,m) :
        return m

    def rneutr(self) : # Zero().add(Zero) = Zero() 
        return Sgl(self)

class Succ (Nat) : 

    def __init__(self,n) : 
        self.n = n
        
    def add(self,m) : 
        return Succ(self.n.add(m))
            
    def rneutr(self) : # Succ(self.n).add(Zero) = Succ(n.add(Zero))
        return Sgl(Succ(self.n.rneutr().val)) 
    # self.n.rneutr() : Sgl(self.n.add(Zero))[val=self.n]
    
"""
self.add(Zero)
"""
# env1={}
env["self"] = Var("self")
"""
print(Id("self").eval(env))
print(Dot(Id("self"),"add").eval(env))
print(Apply(Dot(Id("self"),"add"),[Apply(Id("Zero"),[])]).eval(env))
print(Apply(Dot(Apply(Id("Zero"),[]),"add"),[Id("self")]).eval(env))
print(Apply(Dot(Apply(Id("Zero"),[]),"add"),[Id("self")]).equal(Id("self"),env))
print(Apply(Id("Zero"),[]).equal(Id("self"),env))
"""
# Zero().add(Zero) = Zero() 
print(Apply(Dot(Apply(Id("Zero"),[]),"add"),[Apply(Id("Zero"),[])]).eval(env))
print("xxx")
print(Apply(Id("Zero"),[]).eval(env))

print(Apply(Dot(Apply(Id("Zero"),[]),"add"),[Apply(Id("Zero"),[])]).equal(Apply(Id("Zero"),[]),env))
print("zzz")
# Succ(self.n).add(Zero) = Succ(n.add(Zero))
env["n"] = Var("n")
lhs = Apply(Dot(Apply(Id("Succ"),[Dot(Id("self"),"n")]),"add"),[Apply(Id("Zero"),[])])
print(lhs.eval(env))
#rhs = Apply(Id("Succ"),[Apply(Dot(Id("n"),"add"),[Apply(Id("Zero"),[])])])
#print(rhs.eval(env))
#print(lhs.equal(rhs,env))
"""
print(Apply(Id("Zero"),[]).equal(Apply(Id("Zero"),[]),env))
print(Id("n").eval(env))
print(Id("n").equal(Id("n"),env))
"""