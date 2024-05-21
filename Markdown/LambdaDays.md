# Imagine a dependently typed Python

Andor Penzes

 * Disclameir: This is just an idea.

## Slide 0

 * Design phase
 * Prototyping
 * Discussions
 * Call for contributions

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

class FZ(Fin):
  # n = S k
  def __init__(self) :
    pass

class FS(Fin):
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
    # add : Vect k [k = m + self.n]
    pass

class Nil(Vect):
  # n = 0
  def __init__(self):
    pass

  def add(self,ys):
    # m   : Nat
    # ys  : Vect m
    # add : Vect k [k = m + self.n]
    #     : Vect k [k = m + 0]
    #     : Vect k [k = 0 + m]
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
    # ws : Vect k [k = S z]
    #    : Vect k [k = S (m + xs.n)]
    #    : Vect k [k = m + (S xs.n)]
    #    : Vect k [k = m + (S k)]
    #    : Vect k [k = m + self.n]
    return ws
```

## Slide 5

Evaluation, type checking by normalization

 * Classes, objects and expressions
 * Evaluation of closed expressions lead to a value
 * Evaluation of open expressions lead to the normal form
 * Surprising result, good for debugging 

## Slide 6

How to handle effects? Not yet decided, we have several options:

 * Not to mention them at all; unchecked function calls break abstraction
 * Monads/Monad transformers
 * Effect Handlers

Effect handlers provide an abstraction for modular effectful programming:
a handler acts as an interpreter for a collection of commands whose interface
are statically tracked by the type system.

```
class State:
  # Command
class Get(State):
  def __init__(self):
    pass
class Put(State):
  def __init__(self,s):
    self.s = s
```

```
class Something:
  def next!(self):
    # function : <State Int> Int
    x = Get!
    Put(Get! + 1)
    return x
```

```
class Program:
  def runState(self,s,x) :
    # s        : S
    # x        : <State S> X
    # runState : X
    match (x) :
      effect (Get => k):
        return self.runState(s,k(s))
      effect (Put z => k):
        return self.runState(z,k())
      object (x) :
        return x
```

## Slide 7

Sketches of the type system:

Image from Thorsten.

