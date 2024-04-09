module Some where

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

natFold :
  {A : Set}    ->
  (z : A)      ->
  (s : A -> A) ->
  (n : Nat)    ->
  ---------------
  A
natFold z s Zero     = z
natFold z s (Succ n) = s (natFold z s n)

natElim :
  (P : Nat -> Set)                     ->
  (z : P Zero)                         ->
  (s : {k : Nat} -> P k -> P (Succ k)) ->
  (n : Nat)                            ->
  ---------------------------------------
  P n
natElim P z s Zero     = z
natElim P z s (Succ n) = s (natElim P z s n)

data List (A : Set) : Set where
  Nil  : List A
  Cons : A -> List A -> List A

data Fin : Nat -> Set where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)

finFold :
  {A : Set}    ->
  {n : Nat}    ->
  (z : A)      ->
  (s : A -> A) ->
  (f : Fin n)  ->
  ---------------
  A
finFold         z s FZero          = z
finFold {A} {n} z s (FSucc {n1} f) = s (finFold z s f)

finElim :
  {n : Nat}                            ->
  (P : Nat -> Set)                     ->
  (z : {k : Nat} -> P (Succ k))        ->
  (s : {k : Nat} -> P k -> P (Succ k)) ->
  (f : Fin n)                          ->
  ---------------------------------------
  P n
finElim P z s FZero     = z
finElim P z s (FSucc f) = s (finElim P z s f)

finElim2 :
  {n : Nat}                                            ->
  (P : {k : Nat} -> Fin k -> Set)                      ->
  (z : {k : Nat} -> P (FZero {k}))                     ->
  (s : {k : Nat} -> {f : Fin k} -> P f -> P (FSucc f)) ->
  (f : Fin n)                                          ->
  -------------------------------------------------------
  P f
finElim2 P z s FZero     = z
finElim2 P z s (FSucc f) = s (finElim2 P z s f)

data Vect (A : Set) : Nat -> Set where
  VNil  : Vect A Zero
  VCons : {n : Nat} -> A -> Vect A n -> Vect A (Succ n) 

vectFold :
  {A B : Set}         ->
  {n   : Nat}         ->
  (z   : B)           ->
  (s   : A -> B -> B) ->
  (xs  : Vect A n)    ->
  ------------------------
  B
vectFold z s VNil = z
vectFold z s (VCons x xs) = s x (vectFold z s xs)

vectElim :
  {A B : Set} ->
  {n   : Nat} ->
  (P   : Set -> Nat -> Set) ->
  (z   : P A Zero) ->
  (s   : {k : Nat} -> P A k -> P A (Succ k)) ->
  (xs  : Vect A n) ->
  P A n
vectElim P z s VNil         = z
vectElim P z s (VCons x xs) = s (vectElim P z s xs)

vectElim2 :
  {A : Set}                                         ->
  {n : Nat}                                         ->
  (P : {A0 : Set} -> {k : Nat} -> Vect A0 k -> Set) ->
  (z : {A0 : Set} -> P {A0} VNil)                   ->
  (s : {A0 : Set} -> 
       {k : Nat}  ->
       {x : A0}   ->
       {xs : Vect A0 k} -> P xs -> P (VCons x xs))  ->
  (xs : Vect A n)                                   ->
  ------------------
  P xs
vectElim2 P z s VNil         = z
vectElim2 P z s (VCons x xs) = s (vectElim2 P z s xs)

lookup0 :
  {A   : Set}      ->
  {n   : Nat}      ->
  (idx : Fin n)    ->
  (xs  : Vect A n) ->
  -------------------
  A
lookup0 FZero       (VCons x xs) = x 
lookup0 (FSucc idx) (VCons x xs) = lookup0 idx xs

lookup1 :
  {A   : Set}      ->
  {n   : Nat}      ->
  (idx : Fin n)    ->
  (xs  : Vect A n) ->
  A  
lookup1 idx xs = {!   !}