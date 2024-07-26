open import Data.Bool

data ClassCxt : Set
record Class (Γ : ClassCxt) : Set

data ClassCxt where
  • : ClassCxt
  _▷_ : (Γ : ClassCxt) → Class Γ → ClassCxt

variable Γ : ClassCxt
variable A B : Class Γ

data ClassRef : (Γ : ClassCxt)(A :  → Set where

data Cxt (Γ : ClassCxt) : Set 

variable Δ Θ : Cxt Γ

data MethodCxt (Γ : ClassCxt) : Set

data Methods : Set where

data Init : Set where

record Class Γ  where
  inductive
  field
    super : ClassRef Γ
    instvars : Cxt Γ
    methodDecl : MethodCxt Γ

{- separate class declarations
   and definitions
-}

{-
isConcrete : Bool
    methodDef : T isConcrete → Methods 
    initMethod : T isConcrete → Init
-}

data Type (Γ : ClassCxt) : Set

variable σ : Type Γ

data CxtRef {Γ}(Δ : Cxt Γ)(σ : Type Γ) : Set where  

data Var {Γ}(Δ : Cxt Γ)(Θ : Cxt Γ)(σ : Type Γ) : Set where
  ivar : CxtRef Δ σ → Var Δ Θ σ 
  par : CxtRef Θ σ → Var Δ Θ σ 

data Expr {Γ : ClassCxt}(Δ : Cxt Γ)(Θ : Cxt Γ)(Ξ : MethodCxt Γ)(σ : Type Γ) : Set where
  var : Var Δ Θ σ → Expr Δ Θ Ξ σ
  dot : 

data Cxt Γ where
  • : Cxt Γ
  _▷_ : (Δ : Cxt Γ) → Type Γ → Cxt Γ

record MethodDecl (Γ : ClassCxt) : Set

data MethodCxt Γ where
  • : MethodCxt Γ
  _▷_ : (Ms : MethodCxt Γ) → MethodDecl Γ → MethodCxt Γ

record MethodDecl Γ where
  inductive
  field
    dom : Cxt Γ
    cod : Type Γ

data Type Γ where
  class : ClassRef Γ → Type Γ


  


{-
data ClassRef : (Γ : ClassCxt) → Set where
  zero : ClassRef (Γ ▷ A)
  suc : ClassRef Γ → ClassRef (Γ ▷ B)

data MethodCxt (Γ : ClassCxt) : Set

variable Ms : MethodCxt Γ

data Cxt (Γ : ClassCxt)(Ms : MethodCxt Γ) : Set

variable Δ : Cxt Γ Ms

data Type (Γ : ClassCxt)(Ms : MethodCxt Γ)(Δ : Cxt Γ Ms) : Set

variable σ τ : Type Γ Ms Δ

data Expr {Γ}{Ms}(dom : Cxt Γ Ms)(cod : Type Γ Ms dom) : Set where

record MethodDecl (Γ : ClassCxt)(Ms : MethodCxt Γ) : Set where
  inductive
  field
    dom : Cxt Γ Ms
    cod : Type Γ Ms dom

-- body : Expr dom cod

data MethodCxt Γ Δ where
  • : MethodCxt Γ
  _▷_ : (Ms : MethodCxt Γ) → MethodDecl Γ Ms → MethodCxt Γ

data MethodRef (Γ : ClassCxt)(Ms : MethodCxt Γ) : Set where

data Cxt Γ Ms where

record AbstractClass (Γ : ClassCxt) : Set where
  inductive
  field
    super : ClassRef Γ
    instvars : Cxt Γ • 
    methods : MethodCxt Γ instvars

data Class where
  ref : ClassRef Γ → Class Γ
  abstractClass : AbstractClass Γ → Class Γ

data Type Γ Ms Δ where
  class : ClassRef Γ → Type Γ Ms Δ
  self : Type Γ Ms Δ
--  constr : Type Γ Ms Δ → MethodRef Γ Ms 
-}
