# Imagine a dependently typed Python

Andor Penzes

 * Disclameir: This is just an idea.

## Slide 1

Dependent types:

 * Types and values live in the same space.
 * Values are part of types: Vect 3 Int.
 * Types can be inspected like values.
 * Computation is done at type checking:
   `add (xs : Vect n a, ys : Vect m a) -> Vect (n + m) a`

## Slide 2

Foundations

 * We write programs to solve problems.
 * We organize information as data.
 * We transformation data via functions.
 * Sometimes our abstractions are loosy and needs tying.

## Slide 3

Data representation

 * Sum of products; aka generics, aka levitation.
 * OOP, (Python)
    * Subclasses are sums;
    * Objects are products; fields of object.
 * FP, (Haskell/Idris/Agda)
    * Data constructor are sums
    * Fields are products;

Compile time, Run time

 * Compile time types ensures consistency
 * Runtime types define representation, behaviour
 * Tests ensure consistency
 * Assertions ensure consistency

## Slide 4

Example:

```
class Fin:
  # n : Nat

class FZ(Fin)
  # n = S k
  def __init__(self) :
    pass

class FS(Fin)
  # n = S k
  def __init__(self,x) :
    # x : Fin[n = k]
    self.x = x
```

```
class Vect:
  # n : Nat

  def add(self,ys):
    # m   : Nat
    # ys  : Vect m
    # add : Vect k [k = m + n]
    pass

class Nil(Vect):
  # n = 0
  def __init__(self):
    pass

  def add(self,ys):
    # m   : Nat
    # ys  : Vect m
    # add : Vect k [k = m + n]
    #     : Vect k [k = m + 0]
    #     : Vect k [k = m]  
    return ys

class Cons(Vect):
  # n = S k

  def __init__(self,x,xs):
    # xs : Vect [n=k]
    self.x  = x
    self.xs = xs

  def add(self,ys):
    # m  : Nat
    # ys : Vect m
    zs = self.xs.add(ys)
    # zs : Vect z [z = m + xs.n]
    ws = Cons(x,ws)
    # ws : Vect w [w = S z]
    #    : Vect w [w = S (m + xs.n)]
    #    : Vect w [w = m + (S xs.n)]
    #    : Vect w [w = m + (S k)]
    return ws
```

## Slide 5

## Slide 6

## Slide 7

