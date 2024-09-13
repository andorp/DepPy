open import Data.Nat
open import Data.Fin 
open import Data.Vec hiding (lookup ; _>>=_)
open import Data.List hiding (lookup)
open import Data.Maybe
-- open import Control.Monad

lookup : ∀ {A : Set} → ℕ → List A → Maybe A
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n xs
lookup _       []       = nothing


variable n : ℕ

data ClassVar : Set where
  object : ClassVar 
  aclass : ℕ → ClassVar 

data Field : Set where
  methodRef : ℕ → Field
  fieldRef : ℕ → Field

data Expr (vars : ℕ) : Set where
  class : ClassVar → Expr vars
  var : Fin vars → Expr vars
  _·_ : Expr vars → (fld : Field) → Expr vars
  _$_ : Expr vars → List (Expr vars) → Expr vars 

record Method : Set where
  field
    params : ℕ
    body : Expr (suc params) -- zero is self


record Class : Set where
  field
    parent : ClassVar 
    instvars : ℕ
    methods : List Method
    -- suc classes because we can refer to the current class
--    code : Fin methods → (Method (suc classes))

open Class

{-
data Classes : Set where
  [] : Classes 
  _▷_ : Classes → Class → Classes 
-}

Classes : Set
Classes = List Class


record Program : Set where
  field
    theclasses : Classes
    main : Expr zero

open Program
{-
class Nat :
    "add (n : Nat) : Nat -> Nat"
    
    pass

class Zero (Nat) :
    
    def __init__(self) :
        pass
    
    def add(self, n) :
        return n

class Suc(Nat) :
    
    def __init__(self, m) :
        "m : Nat"
        self.m = m
        
    def add(self,n) :
        return Suc(self.m.add(n))
        
one = Zero()
-}

p : Program
p = record {
  theclasses = record { parent = object ; instvars = zero ; methods = [] }
             ∷ record { parent = aclass zero ; instvars = zero ;
                        methods = (record { params = 1 ; body = var (suc zero)}) ∷ [] }
             ∷ record { parent = aclass zero ; instvars = 1 ;
                        methods = (record { params = 1 ; 
                                  body = class (aclass (suc (suc zero))) $
                                    ((((var zero · fieldRef zero) · methodRef zero) $ (var (suc zero) ∷ [])) ∷ []) }) ∷ [] }
             ∷ [] ;
  main = class (aclass (suc zero)) $ [] }

-- semantics

data Object : Set

record SimpleObject : Set where
  inductive
  field
    oclass : ClassVar
    state : List Object

open SimpleObject

data Object where
  class : Class → Object -- zero = Object
  meth : Method → SimpleObject → Object 
  simple : SimpleObject → Object

dot : Classes → Object → Field → Maybe Object
dot _ (class x) n = nothing
dot _ (meth x _) n = nothing
dot _ (simple x) (fieldRef n) = lookup n (state x)
dot cls (simple x) (methodRef m) with oclass x
... | object = nothing
... | aclass n =
  do c ← lookup n cls
     g ← lookup m (methods c)
     just (meth g x)
-- need to loop here

objectClass : Object 
objectClass = class (record { parent = object ; instvars = zero ; methods = [] })

apply : Classes → Object → List Object → Maybe Object
apply cls (class x) xs = {!!}
apply cls (meth x x₁) xs = {!!}
apply cls (simple x) xs = nothing

evalArgs : {vars : ℕ}(es : List (Expr vars)) → Classes → Vec Object vars → Maybe (List Object) 

evalExpr : {vars : ℕ}(e : Expr vars) → Classes → Vec Object vars → Maybe Object 
evalExpr (class object) cls env = just objectClass
evalExpr (class (aclass x)) cls env = Data.Maybe.map class (lookup x cls) -- class (lookup {!!} {!!})
evalExpr (var x) cls env = just (Data.Vec.lookup env x)
evalExpr (e · fld) cls env = 
  do
    v ← evalExpr e cls env
    dot cls v fld
evalExpr (e $ es) cls env = 
  do
    f ← evalExpr e cls env
    ys ← evalArgs es cls env
    apply cls f ys

evalArgs  = {!!}

{-
do
  x ← just 3
  y ← just 4
  return (x + y)
-}
evalProg : Program → Object
evalProg = {!!}

