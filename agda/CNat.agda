module CNat where

record Nat : Set where
  constructor N
  field

record Zero : Set where
  constructor Z
  field
    base : Nat

record Succ : Set where
  constructor S
  field
    base : Nat
    n    : Either Zero Succ
