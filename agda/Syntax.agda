open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (lookup ; _>>=_ ; [_])
open import Data.List hiding (lookup )
open import Data.Maybe
open import Data.Bool

variable A  B C : Set
variable m n : ℕ

lookup : List A →  ℕ → Maybe A
lookup [] n = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc n) = lookup xs n

vlookup : Vec A n → Fin n → A
vlookup (x ∷ xs) zero = x
vlookup (x ∷ xs) (suc i) = vlookup xs i

finEqBool : ∀ {n} → Fin n → Fin n → Bool
finEqBool {n = zero} ()
finEqBool {n = suc n} zero     zero     = true
finEqBool {n = suc n} zero     (suc _)  = false
finEqBool {n = suc n} (suc _)  zero     = false
finEqBool {n = suc n} (suc i)  (suc j)  = finEqBool {n = n} i j

natEqBool : ℕ → ℕ → Bool
natEqBool zero     zero     = true
natEqBool zero     (suc n)  = false
natEqBool (suc m)  zero     = false
natEqBool (suc m)  (suc n)  = natEqBool m n

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

  Classes : Set
  Classes = Vec Class n-classes

  -- types
{-
for every class there is a class type and a class defn

class-type =
  ref parent-class
  a sequence of
    a type of an instance variable
    a type for a class variable (ie methods)
    method definitions


NEXT STEP :
  define untyped (and unscoped) syntax of the typed system
  implement scope and type checker
  should we use named syntax instead of deBruijn?
-}

  MRef : Set
  MRef = ℕ -- should be Fin

  IRef : Set
  IRef = ℕ  -- should be Fin

  data Type : Set where
    class : ClassVar → Type
    constr : Type → IRef → Expr zero → Type -- zero is stopgap
    
  record MType : Set where
    field
      param : List Type
      retType : Type

  data Context : Set where
    • : Context
    _▷i_ : Context → Type → Context
    _▷m_ : Context → MType → Context
    _▷d_:=_ : Context → MRef → Method → Context


  record TypedClass : Set where
    field
        parent : ClassVar
        con : Context



{-

  data Context : Set
  data Decl : Context → Set where
    ivarDecl : Ty Γ → Decl Γ
    methDecl : MTy Γ → Decl Γ 

  data Defn : Context → Set where
    methodDef :  → Decl Γ    

  data Context where
    • : Context
    _▷_ : (Γ : Context) → Decl Γ → Context
    _▷_=_ : (Γ : Context) → MVar Γ → Method → Context    

  data IVar : (parent : ClassVar) → Context → Set
    inh : IVar ? (getContext parent) → IVar parent •
    zero : IVar parent (Γ ▷ ivarDecl _)
    suc : IVar parent Γ → IVar parent (Γ ▷ d)
    ignore : IVar parent Γ → IVar parent (Γ ▷ _ = _)

  data MVar : (parent : ClassVar) → Context → Set
    inh : MVar ? (getContext parent) → MVar parent •
    zero : MVar parent (Γ ▷ methodDecl _)
    suc : MVar parent Γ → MVar parent (Γ ▷ d)
    ignore : MVar parent Γ → MVar parent (Γ ▷ _ = _)
    


-}
  

--  data MethodTy : Set where
    


  -- semantics

  module _(cls : Classes) where

    data Value (free : ℕ) : Set

    data Ne (vars : ℕ) : Set where
      var : Fin vars → Ne vars
      _·_ : Ne vars → (fld : Field) → Ne vars
      _$_ : Ne vars → List (Value vars) → Ne vars

    data Object (free : ℕ) : Set

    record SimpleObject (free : ℕ) : Set where
      inductive
      field
        oclass : ClassVar
        state : List (Value free)

    open SimpleObject

    data Object free where
      class : ClassVar → Object free
      meth : Method → (SimpleObject free) → Object free
      simple : (SimpleObject free) → Object free

    data Entry (vars : ℕ) : Set where
      val : Value vars → Entry vars
      var : Fin vars → Entry vars

    Env : (dom cod : ℕ) → Set
    Env dom cod = Vec (Entry dom) cod

    -- [ 0 , 1 , 2 ] : Vec (Fin 3) 3

    upto : Vec (Fin n) n
    upto {n = zero} = []
    upto {n = suc n} = zero ∷ (Data.Vec.map suc upto ) 

    idEnv : Env n n
    idEnv = Data.Vec.map var upto

    -- record Closure (free : ℕ) : Set where
    --   inductive
    --   field
    --     vars : ℕ
    --     e : Ne vars     -- stuck expr  
    --     env : Env free vars
    -- x [ x = y ]
    -- x [ x = Zero ]
    -- e : Expr {x}
    -- env : Env {y} {x}

    data Value free where
      obj : Object free → Value free
      ne : Ne free → Value free      
--      ne : Closure free → Value free

    {-# TERMINATING #-}
    dot : {free : ℕ} → Value free → Field → Maybe (Value free)
    dot (obj (class x)) n = nothing
    dot (obj (meth x _)) n = nothing
    dot (obj (simple x)) (fieldRef n) =
      lookup (state x) n
    dot {free} (obj (simple x)) (methodRef m) = loop (oclass x)
      where doit : Class → Maybe (Value free)
            doit c = do g ← lookup (methods c) m
                        just (obj (meth g x))
            loop : ClassVar → Maybe (Value free)
            loop object = nothing
            loop (aclass n) with doit (vlookup cls n)
            loop (aclass n) | just x = just x
            loop (aclass n) | nothing = loop (parent (vlookup cls n)) -- refactor!
    dot (ne n) f = just (ne (n · f))

    {-# TERMINATING #-}
    evalExpr : {free vars : ℕ}(e : Expr vars) → Env free vars → Maybe (Value free)

    apply : {free : ℕ} → Value free → List (Value free) → Maybe (Value free)
    apply (obj (class x)) xs = just (obj (simple (record { oclass = x ; state = xs }))) -- constructor
    apply (obj (meth x self)) xs =
       do
         ys ← list2vec (Data.List.map val xs)
         evalExpr (body x) ((val (obj (simple self))) ∷ ys)
    apply (obj (simple x)) xs = nothing
    apply (ne n) xs =
      just (ne (n $ xs)) 
--      just (ne (record { vars = vars ; e = e $ {!!} ; env = env }))
-- lift : Ne vars → Env free vars → Value vars
-- lift v env = Closure {vars = vars, 


    evalArgs : {free vars : ℕ}(es : List (Expr vars)) → Env free vars → Maybe (List (Value free))

    evalExpr (class x) env = just (obj (class x))
    evalExpr (var x) env with Data.Vec.lookup env x
    ... | val x = just x
    ... | var z = just (ne (var z))    
--    ... | var z = just (ne (record { vars = _ ; e = var z ; env = {!!} }))
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

    evalExpr₀ : Expr n → Maybe (Value n)
    evalExpr₀ e = evalExpr e idEnv

    equalsClassVar : ClassVar -> ClassVar -> Bool
    equalsClassVar object object = true
    equalsClassVar (aclass f₀) (aclass f₁) = finEqBool f₀ f₁
    equalsClassVar x y = false

    equalValues : List (Value n) → List (Value n) → Maybe Bool

    equalObject : Object n → Object n → Maybe Bool
    equalObject (class c₀) (class c₁) = just (equalsClassVar c₀ c₁)
    equalObject (class x) (meth x₁ x₂) = just false
    equalObject (class x) (simple x₁) = just false
    equalObject (meth x x₂) x₁ = just false
    equalObject (simple x) (class x₁) = just false
    equalObject (simple x) (meth x₁ x₂) = just false
    equalObject (simple record { oclass = oclass₀ ; state = state₀ }) (simple record { oclass = oclass₁ ; state = state₁ }) =
      if (equalsClassVar oclass₀ oclass₁) then equalValues state₀ state₁ else just false

    -- equalEntry : Entry n → Entry n → Maybe Bool
    -- equalEntry = {!!}

    equalField : Field → Field → Bool
    equalField (methodRef x₀) (methodRef x₁) = natEqBool x₀ x₁
    equalField (methodRef x) (fieldRef x₁) = false
    equalField (fieldRef x) (methodRef x₁) = false
    equalField (fieldRef x₀) (fieldRef x₁) = natEqBool x₀ x₁

    equalValue : Value n → Value n → Maybe Bool

    equalValues [] [] = just true
    equalValues [] (x ∷ vs₁) = just false
    equalValues (x ∷ vs₀) [] = just false
    equalValues (v₀ ∷ vs₀) (v₁ ∷ vs₁) = do
      b ← equalValue v₀ v₁
      c ← equalValues vs₀ vs₁
      just (b ∧ c)

    equalNe :  Ne n → Ne n → Maybe Bool
    equalNe (var x₀) (var x₁) = just (finEqBool x₀ x₁)
    equalNe (var x) (n₁ · fld) = just false
    equalNe (var x) (n₁ $ x₁) = just false
    equalNe (n₀ · fld) (var x) = just false
    equalNe (n₀ · fld₀) (n₁ · fld₁) =
      if equalField fld₀ fld₁ then equalNe n₀ n₁ else just false 
    equalNe (n₀ · fld) (n₁ $ x) = just false
    equalNe (n₀ $ x) (var x₁) = just false
    equalNe (n₀ $ x) (n₁ · fld) = just false
    equalNe (n₀ $ vs₀) (n₁ $ vs₁) = do
      b ← equalNe n₀ n₁
      c ← equalValues vs₀ vs₁
      just (b ∧ c)

    -- equalClosure :  Closure n → Closure n → Maybe Bool
    -- equalClosure record { vars = vars₀ ; e = (var x₀) ; env = env₀ } record { vars = vars₁ ; e = (var x₁) ; env = env₁ } =
    --   {!vlookup env₀ x₀!}
    -- equalClosure record { vars = vars₀ ; e = (var x) ; env = env₀ } record { vars = vars₁ ; e = (e₁ · fld) ; env = env₁ } =
    --   just false
    -- equalClosure record { vars = vars₀ ; e = (var x) ; env = env₀ } record { vars = vars₁ ; e = (e₁ $ x₁) ; env = env₁ } = 
    --   just false
    -- equalClosure record { vars = vars₀ ; e = (e₀ · fld) ; env = env₀ } record { vars = vars₁ ; e = e₁ ; env = env₁ } = {!!}
    -- equalClosure record { vars = vars₀ ; e = (e₀ $ x) ; env = env₀ } record { vars = vars₁ ; e = e₁ ; env = env₁ } = {!!}


    equalValue (obj x₀) (obj x₁) = equalObject x₀ x₁
    equalValue (obj x) (ne x₁) = just false
    equalValue (ne x) (obj x₁) = just false
    equalValue (ne n₀) (ne n₁) = equalNe n₀ n₁

    equalExpr : Expr n → Expr n → Maybe Bool
    equalExpr e₀ e₁ = do
      v₀ ← evalExpr₀ e₀
      v₁ ← evalExpr₀ e₁
      equalValue v₀ v₁


record Program : Set where
  field
    free : ℕ
    n-classes : ℕ
    theclasses : Classes n-classes
    main : Expr n-classes free

open Program

evalProg : (p : Program) → Maybe (Value (n-classes p) (theclasses p) (free p))
evalProg record { free = free ; n-classes = n-classes ; theclasses = theclasses ; main = main } =
         evalExpr n-classes theclasses main (idEnv n-classes theclasses)
         

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

  (n : Nat)
  n.add(Zero()) ==> stuck
  Zero().add(n)   ==> n
  n.add(Suc(Zero())) ==> stuck
  Suc(Zero()).add(n) ==> Suc(n)
  


  -}


m-classes : ℕ
m-classes = 3

myclasses : Classes m-classes
myclasses = record { parent = object ; instvars = zero ; methods = [] }
            ∷ record { parent = aclass zero ; instvars = zero ;
                       methods = (record { params = 1 ; body = var (suc zero)}) ∷ [] }
            ∷ record { parent = aclass zero ; instvars = 1 ;
                       methods = (record { params = 1 ;
                                 body = class (aclass (suc (suc zero))) $
                                   ((((var zero · fieldRef zero) · methodRef zero) $ (var (suc zero) ∷ [])) ∷ []) }) ∷ [] }
            ∷ []


test : Expr m-classes n → Maybe (Value m-classes myclasses n)
test e = evalProg p
  where p = record {
              n-classes = m-classes ;
              theclasses = myclasses;
              main = e }


c-Zero : Expr 3 n
c-Zero = class (aclass (suc zero))
e-zero : Expr 3 n
e-zero = c-Zero $ []
c-Suc : Expr 3 n
c-Suc = class (aclass (suc (suc zero)))
e-suc : Expr 3 n → Expr 3 n
e-suc e = (c-Suc $ (e ∷ []))
e-1 : Expr 3 zero
e-1 = e-suc e-zero

stuk : Expr 3 1
stuk = e-suc (var zero)

test1 = test {n = zero} e-zero
test2 = test {n = zero} (e-suc e-zero)
test3 = test {n = zero} ((e-zero · (methodRef 0)) $ (e-zero ∷ []))
test4 = test {n = zero} ((e-1 · (methodRef 0)) $ (e-1 ∷ []))

test5 = test {n = 1} (e-suc stuk)
test6 = test {n = 1} (((var zero) · (methodRef 0)) $ (e-zero {n = 1} ∷ []))
test7 = test {n = 1} (((e-zero {n = 1}) · (methodRef 0)) $ ((var zero) ∷ []))
test8 = test {n = 1} (((var zero) · (methodRef 0)) $ (e-suc (e-zero {n = 1}) ∷ []))
test9 = test {n = 1} (((e-suc (e-zero {n = 1})) · (methodRef 0)) $ ((var zero) ∷ []))

-- Number of variables

{-
vars : ℕ
vars = 1
 
-- Variable n
varN : Expr 3 vars
varN = var zero  -- Represents n
 
-- Zero and Suc expressions
e-zero : Expr 3 vars
e-zero = c-Zero $ []
 
e-suc : Expr 3 vars → Expr 3 vars
e-suc e = c-Suc $ [ e ]

evalProgWithEnv : ∀ {vars} → Expr m-classes vars → Env zero vars → Maybe (Value m-classes myclasses vars)
evalProgWithEnv e env = evalExpr m-classes myclasses e env

-- Test function for expressions with variables
testWithVar : Expr m-classes vars → Maybe (Value m-classes myclasses vars)
testWithVar e = evalProgWithEnv e [ var zero ]
 
-- Test 5: n.add(Zero())
test5 : Maybe (Value m-classes myclasses vars)
test5 = testWithVar ((varN · methodRef 0) $ [ e-zero ])
 
-- Test 6: Zero().add(n)
test6 : Maybe (Value m-classes myclasses vars)
test6 = testWithVar ((e-zero · methodRef 0) $ [ varN ])
 
-- Test 7: n.add(Suc(Zero()))
test7 : Maybe (Value m-classes myclasses vars)
test7 = testWithVar ((varN · methodRef 0) $ [ e-suc e-zero ])
 
-- Test 8: Suc(Zero()).add(n)
test8 : Maybe (Value m-classes myclasses vars)
test8 = testWithVar ((e-suc e-zero · methodRef 0) $ [ varN ])
-}
