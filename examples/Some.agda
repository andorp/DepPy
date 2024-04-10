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

natInd :
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

listFold :
  {A B : Set}         ->
  (n   : B)           ->
  (c   : A -> B -> B) ->
  (xs  : List A)      ->
  ----------------------
  B
listFold n c Nil         = n
listFold n c (Cons x xs) = c x (listFold n c xs)

lookuple :
  {A  : Set}    ->
  (n  : Nat)    ->
  (xs : List A) ->
  ----------------
  A
lookuple = {!   !}

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

finInd :
  {n : Nat}                                          ->
  (P : forall {k} -> Fin k -> Set)                   ->
  (z : forall {k} -> P (FZero {k}))                  ->
  (s : forall {k} {f : Fin k} -> P f -> P (FSucc f)) ->
  (f : Fin n)                                        ->
  -----------------------------------------------------
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

vectInd :
  {A : Set}                                   ->
  {n : Nat}                                   ->
  (P : forall {B} {k} (ys : Vect B k) -> Set) ->
  (z : forall {B} -> P {B} VNil)              ->
  (s : forall {B} {k} {x} {xs : Vect B k}
       -> P xs
       -> P (VCons x xs))                     ->
  (xs : Vect A n)                             ->
  ----------------------------------------------
  P xs
vectInd P z s VNil         = z
vectInd P z s (VCons x xs) = s (vectInd P z s xs)

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