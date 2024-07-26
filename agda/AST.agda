module AST where

open import Agda.Builtin.String
open import Data.List
open import Agda.Builtin.Sigma

module Untyped where

  data Expr : Set where
    Var : String -> Expr
    Id  : String -> Expr
    Dot : Expr -> String -> Expr
    App : Expr -> List Expr -> Expr

  record Init : Set where
    field
      params : List String

  record Method : Set where
    field
      params : List String
      body   : Expr

  record Class : Set where
    field
      vars   : String
      init   : Init
      method : List Method

module Typed where

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  data Type : Set where
    ClassName : String -> Type
    Method : List (String × Type) -> Type -> Type

  -- Expression context
  data Gamma : Set where
    EΓ : Gamma
    BΓ : String -> Type -> Gamma -> Gamma

  -- Class context
  data Sigma : Set where
    EΣ : Sigma

  -- Well defined name
  data InGamma : String -> Type -> Gamma -> Set where
    Here :
      {n : String}        ->
      {t : Type}          ->
      {g : Gamma}         ->
      ----------------------
      InGamma n t (BΓ n t g)
    There :
      {n , m : String}     ->
      {t , t2 : Type}      ->
      {g : Gamma}          ->
      InGamma n t g        ->
      -----------------------
      InGamma n t (BΓ m t2 g)

  data Expr : Sigma -> Gamma -> Set where
    Var :
      {s : Sigma}   ->
      {g : Gamma}   ->
      {t : Type}    ->
      (n : String)  ->
      InGamma n t g ->
      ----------------
      Expr s g