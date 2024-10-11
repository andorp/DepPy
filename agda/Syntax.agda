open import Data.Nat
open import Data.Fin 
open import Data.Vec hiding (lookup ; _>>=_)
open import Data.List hiding (lookup)
open import Data.Maybe

variable A  B C : Set
variable m n : ℕ

lookup : List A →  ℕ → Maybe A
lookup [] n = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc n) = lookup xs n

vlookup : Vec A n → Fin n → A
vlookup (x ∷ xs) zero = x
vlookup (x ∷ xs) (suc i) = vlookup xs i

list2vec : List A → Maybe (Vec A n)
list2vec {n = zero} [] = just []
list2vec {n = zero} (x ∷ as) = nothing
list2vec {n = suc n} [] = nothing
list2vec {n = suc n} (x ∷ as) = 
  do
    ys ← list2vec {n = n} as
    just (x ∷ ys)

module _(n-classes : ℕ) where

  data ClassVar : Set where
    object : ClassVar
    aclass : Fin n-classes → ClassVar

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

  open Method

  record Class : Set where
    field
      parent : ClassVar 
      instvars : ℕ
      methods : List Method

  open Class 

  {-
  data Classes : Set where
    [] : Classes 
    _▷_ : Classes → Class → Classes 
  -}

  Classes : Set
  Classes = Vec Class n-classes


  -- semantics

  data Object : Set

  record SimpleObject : Set where
    inductive
    field
      oclass : ClassVar
      state : List Object

  open SimpleObject

  data Object where
    class : ClassVar → Object 
    meth : Method → SimpleObject → Object 
    simple : SimpleObject → Object

  module _(cls : Classes) where

    dot : Object → Field → Maybe Object
    dot (class x) n = nothing
    dot (meth x _) n = nothing
    dot (simple x) (fieldRef n) = lookup (state x) n
    dot (simple x) (methodRef m) with oclass x
    ... | object = nothing
    ... | aclass n =
      do c ← just (vlookup cls n)
         g ← lookup (methods c) m
         just (meth g x)
    -- need to loop here

    {-# TERMINATING #-}
    evalExpr : {vars : ℕ}(e : Expr vars) → Vec Object vars → Maybe Object 

    apply : Object → List Object → Maybe Object
    apply (class x) xs = just (simple (record { oclass = x ; state = xs })) -- constructor
    apply (meth x self) xs =
      do
        ys ← list2vec xs
        evalExpr (body x) ((simple self) ∷ ys)
    apply (simple x) xs = nothing

    evalArgs : {vars : ℕ}(es : List (Expr vars)) → Vec Object vars → Maybe (List Object) 

    evalExpr (class x) env = just (class x)
    evalExpr (var x) env = just (Data.Vec.lookup env x)
    evalExpr (e · fld) env = 
      do
        v ← evalExpr e env
        dot v fld
    evalExpr (e $ es) env = 
      do
        f ← evalExpr e env
        ys ← evalArgs es env
        apply f ys

    evalArgs [] env = just []
    evalArgs (x ∷ es) env = 
      do
        y ← evalExpr x env
        ys ← evalArgs es env
        just (y ∷ ys)


record Program : Set where
  field
    n-classes : ℕ
    theclasses : Classes n-classes
    main : Expr n-classes zero

open Program

evalProg : (p : Program) → Maybe (Object (n-classes p))
evalProg record { n-classes = n-classes ; theclasses = theclasses ; main = main } =
         evalExpr n-classes theclasses main []

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

  test1 = Zero()
  test2 = Suc (Zero ())
  test3 = Zero().add(Zero())
  test3 = test2.add(test2)
  -}


test : Expr 3 zero → Maybe (Object 3)
test e = evalProg p
  where p = record {
              n-classes = 3 ;
              theclasses = record { parent = object ; instvars = zero ; methods = [] }
                         ∷ record { parent = aclass zero ; instvars = zero ;
                                    methods = (record { params = 1 ; body = var (suc zero)}) ∷ [] }
                         ∷ record { parent = aclass zero ; instvars = 1 ;
                                    methods = (record { params = 1 ; 
                                              body = class (aclass (suc (suc zero))) $
                                                ((((var zero · fieldRef zero) · methodRef zero) $ (var (suc zero) ∷ [])) ∷ []) }) ∷ [] }
                         ∷ [] ;
              main = e }

c-Zero : Expr 3 zero
c-Zero = class (aclass (suc zero))

e-zero : Expr 3 zero
e-zero = c-Zero $ []
c-Suc : Expr 3 zero
c-Suc = class (aclass (suc (suc zero)))
e-suc : Expr 3 zero → Expr 3 zero
e-suc e = (c-Suc $ (e ∷ []))
e-1 : Expr 3 zero
e-1 = e-suc e-zero


test1 = test e-zero
test2 = test (e-suc e-zero)
test3 = test ((e-zero · (methodRef 0)) $ (e-zero ∷ []))
test4 = test ((e-1 · (methodRef 0)) $ (e-1 ∷ []))
