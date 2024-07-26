open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- ℕ = μ X . 1 + X

module _(A : Set) where

{-
  Fam : Cat
  | Fam | = ℕ → Set
  Fam X Y = (n : ℕ) → X n → Y n 

  Fin : Fam

  T_Fin : Fam → Fam
  T_Fin X n = (m : ℕ) × (n ≡ suc m) × (⊤ + X m)

  Fun = μ T_Fin

-}

  data Fin (n : ℕ) : Set where
    VZero : (m : ℕ) → n ≡ suc m → Fin n  
    VSucc : (m : ℕ) → n ≡ suc m → Fin m → Fin n

  data Vec (n : ℕ) : Set where
    VNil : (n ≡ 0) → Vec n
    VCons : (m : ℕ) → n ≡ suc m → A → Vec m → Vec n

  lookupVec : (n : ℕ) → Vec n → Fin n → A

  lookupNil : (n : ℕ) → Fin n → n ≡ 0 → A
  lookupNil .(suc m) (VZero m refl) ()
  lookupNil .(suc m) (VSucc m refl i) ()

  lookupCons : (n : ℕ)(m : ℕ) → n ≡ suc m → Fin n → A → Vec m → A
  lookupCons n m x (VZero m₁ x₁) a as = a
  lookupCons .(suc m) m refl (VSucc .m refl i) a as =
             lookupVec m as i
  
  lookupVec n (VNil x) i = lookupNil n i x
  lookupVec n (VCons m x b bs) i = lookupCons n m x i b bs

  module _(M : ℕ → Set)
          (mVzero : (n : ℕ)(m : ℕ) → n ≡ suc m → M n)
          (mVsucc : (n : ℕ)(m : ℕ) → n ≡ suc m → M m → M n) where

    RFin : (n : ℕ) → Fin n → M n
    RFin n (VZero m x) = mVzero n m x
    RFin n (VSucc m x i) = mVsucc n m x (RFin m i)


