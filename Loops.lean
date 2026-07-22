import Batteries.Lean.Float

/-!
# Loops
-/

/-!
Let's get something out of the way: Lean does support the kind of loops that
you find in imperative languages such as Python. In Python you can define

```python
def sum(xs : list[float]) -> float:
  s = 0.0
  for x in xs:
    s = s + x
  return s
```

and get

```pycon
>>> sum([0.1, 0.2, 0.3])
0.6000000000000001
```
In Lean there is a very similar construct:
-/

namespace Imperative

def sum (xs : List Float) : Float := Id.run do
  let mut acc := 0.0
  for x in xs do
    acc := acc + x
  return acc

#eval sum [0.1, 0.2, 0.3]
-- 0.600000

#eval sum [0.1, 0.2, 0.3] == 0.1 + 0.2 + 0.3
-- true

end Imperative

/-!
However, this is not a fundamental construct, merely a syntactic layer that
gets reinterpreted as a pure functional construction without a for loop
and mutable variables. We will drop that kind of constructs until we have
a better grasp of what functional programming can do and how monads can
restore a semblance of imperative code in a functional world.
-/

/-!
In Lean, given that we expect our `sum` function to have the type
`List Float → Float`, it's very natural to try and pattern
match on the list to compute the sum. The rest of the code almost writes
itself! We end up with:
-/


namespace V0

def sum (xs : List Float) : Float :=
  match xs with
  | [] => 0.0
  | x :: xs => x + sum xs

#check sum

#eval sum [0.1, 0.2, 0.3]
-- 0.600000

end V0

/-!
Success! Well, not quite, since the result of our functional sum may not
agree with the output of the imperative one. Despite the same display of
digits,
-/

#eval 0.1 + 0.2 + 0.3
-- 0.600000

#eval V0.sum [0.1, 0.2, 0.3]
-- 0.600000

/-!
we actually have
-/

#eval V0.sum [0.1, 0.2, 0.3] == 0.1 + 0.2 + 0.3
-- false

/-!
How come? To begin with, Lean calls the `Float.toString` method to display a
string representation of a float and this method does not provide enough digits
to characterize a float uniquely.

To overcome this issue, we can import `Batteries.Lean.Float`, which gives
use a new `Float.toStringFull` method that will provide all the digits of
a float.
-/

#eval IO.println (0.1 + 0.2 + 0.3).toStringFull
-- 0.600000000000000088817841970012523233890533447265625

/-!
This results matches what Python produces:

```python
>>> x = 0.0 + 0.1 + 0.2 + 0.3
>>> print(f"{x:.100g}")
0.600000000000000088817841970012523233890533447265625
```

On the other hand
-/

#eval IO.println  (V0.sum [0.1, 0.2, 0.3]).toStringFull
-- 0.59999999999999997779553950749686919152736663818359375

/-!
OK, now we understand that our computations have different results, but we
still need to understand why!
-/

/-!
TODO:
  - default `+` is left-assoc (hint : over the +)
  - repeated use of referential transparency to see what `V0.sum` computes.

-/


/-!
```lean
V0.sum [0.1, 0.2, 0.3]
-> V0.sum (0.1 :: [0.2, 0.3])
-> 0.1 + V0.sum [0.2, 0.3]
-> 0.1 + V0.sum (0.2 :: [0.3])
-> 0.1 + (0.2 + V0.sum [0.3])
-> 0.1 + (0.2 + V0.sum (0.3 :: []))
-> 0.1 + (0.2 + (0.3 + V0.sum []))
-> 0.1 + (0.2 + (0.3 + 0.0))
```

We can actually prove this in Lean!
-/

/-!
```mermaid
flowchart TD
    A["V0.sum [0.1, 0.2, 0.3]"]
    B["V0.sum (0.1 :: [0.2, 0.3])"]
    C["0.1 + V0.sum [0.2, 0.3]"]
    D["0.1 + V0.sum (0.2 :: [0.3])"]
    E["0.1 + (0.2 + V0.sum [0.3])"]
    F["0.1 + (0.2 + V0.sum (0.3 :: []))"]
    G["0.1 + (0.2 + (0.3 + V0.sum []))"]
    H["0.1 + (0.2 + (0.3 + 0.0))"]

    A --> B
    B --> C
    C --> D
    D --> E
    E --> F
    F --> G
    G --> H
```
-/



namespace V0

example : sum [0.1, 0.2, 0.3] = 0.1 + (0.2 + (0.3 + 0.0)) :=
  calc sum [0.1, 0.2, 0.3]
    _ = sum (0.1 :: [0.2, 0.3])         := rfl
    _ = 0.1 + sum [0.2, 0.3]            := rfl
    _ = 0.1 + sum (0.2 :: [0.3])        := rfl
    _ = 0.1 + (0.2 + sum [0.3])         := rfl
    _ = 0.1 + (0.2 + sum (0.3 :: []))   := rfl
    _ = 0.1 + (0.2 + (0.3 + sum []))    := rfl
    _ = 0.1 + (0.2 + (0.3 + 0.0))       := rfl

end V0

/-!
```mermaid
graph TD
    A["+"] --> B["0.1"]
    A --> C["+"]
    C --> D["0.2"]
    C --> E["+"]
    E --> F["0.3"]
    E --> G["0.0"]
```
-/



/-!
OTOH, it's pretty clear that our pseudo-imperative version computes

```lean
((0.0 + 0.1) + 0.2) + 0.3
```
-/

/-!
```mermaid
graph TD
    A["+"] --> B["+"]
    A --> C["0.3"]
    B --> D["+"]
    B --> E["0.2"]
    D --> F["0.0"]
    D --> G["0.1"]
```
-/


/-!
What are loops used actually for? If you exclude loops that produce some
side-effect, for loops at there core typically:
- read some initial state,
- iterate over a collection, and at each step use the new element from the
collection and the current state to update the state until the collection is
fully traversed.

The product of the loop is the final value of the state.

-/

/-!
Note: for loops over a collection *terminate*. While/repeat loops, that's unclear...
-/

/-!
TODO: easier to delay tail-recursive concept to the left-associative version
of the sum since
-/


/-!
## Tail recursion, stack overflow, etc.
-/

/-!
Note that when we do that kind of recursion, the multiple calls to `sum`
that occurs are still "alive" on the call stack until we reach the empty
list, since we have to keep the function variable `x` to make a sum with
the partial sum to be able to remove the function from the call stack.
This will ultimately lead us to a stack overflow for large lists of floats.
-/

#check List.range
-- List.range (n : Nat) : List Nat

#eval List.range 3
-- [0, 1, 2]

#eval 3 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> V0.sum
-- 0.600000

#eval 100 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> V0.sum
-- 505.000000

#eval 100_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> V0.sum
-- 500005000.000000

#eval 1_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> V0.sum
-- 50000050000.000000

/-!
```lean
#eval 10_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> V0.sum
-- Server process crashed, likely due to a stack overflow or a bug.
```
-/

/-!
This accumulation of functions environment on the call stack has to happen
because there tasks are not finished after the recursive call. If instead
we manage to make the recursive call the last call of the function,
that is if our function is not only recursive but **tail-recursive**,
since Lean implements **tail-call optimization**, we can grow our list
only limited by the memory allocated to our process, not by the size of
the stack.
-/

/-!
The trick to do that is to "push" the state each function is still holding,
here the float which is meant to be added to the sum,
to the next function. So we need an auxiliary function
-/

def sumAux (xs : List Float) (x0 : Float) : Float :=
  match xs with
  | [] => x0
  | x :: xs => sumAux xs (x + x0)

def sum' (xs : List Float) : Float :=
  sumAux xs 0.0

#eval 1_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum'
-- 50000050000.000000

/-!
Expensive but works!
```lean
#eval 10_000_000 |> List.range |>.map (fun i => Float.ofNat (i + 1) / 10.0) |> sum'
-- 5000000500000.000000

Note that Python doesn't implement tail-call optimization so the translation
of this pattern to Python will still create a stack overflow.
```
-/

/-!
Now if we think for a minute we have not exactly performed the same computation
in Python and in Lean. In Python our initial loop has computed

```python
>>> ((0.0 + 0.1) + 0.2) + 0.3
0.6000000000000001
```

which is the same as

```python
>>> 0.0 + 0.1 + 0.2 + 0.3
0.6000000000000001
```

since `+` is left-associative in Python.

The full precision can be displayed with

```python
>>> x = 0.0 + 0.1 + 0.2 + 0.3
>>> print(f"{x:.100g}")
0.600000000000000088817841970012523233890533447265625
```

Lean has the same convention: `+` is left-associative, so if we ask for the
full-precision display (we need to import `Batterries.Lean.Float` for that),
we get:
-/

#eval 0.0 + 0.1 + 0.2 + 0.3 |>.toStringFull |> IO.println
-- 0.600000000000000088817841970012523233890533447265625

#eval ((0.0 + 0.1) + 0.2) + 0.3 |>.toStringFull |> IO.println
-- 0.600000000000000088817841970012523233890533447265625

#eval (0.0 + 0.1 + 0.2 + 0.3) == (((0.0 + 0.1) + 0.2) + 0.3)
-- true

/-!
But our computation of the sum says something different:
-/

#eval V0.sum [0.1, 0.2, 0.3] |>.toStringFull |> IO.println
-- 0.59999999999999997779553950749686919152736663818359375

#eval sum' [0.1, 0.2, 0.3] |>.toStringFull |> IO.println
-- 0.59999999999999997779553950749686919152736663818359375

/-!
TODO: monadic fold
--------------------------------------------------------------------------------
-/

/-!
TODO: classic fold as a special case.
-/

/-!
Pseudo-imperative for loops
--------------------------------------------------------------------------------
-/

/-!
Very similar to monadic folds
-/

#print ForIn
-- class ForIn.{u, v, u₁, u₂} (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) :
--   Type (max (max (max u (u₁ + 1)) u₂) v)
-- number of parameters: 3
-- fields:
--   ForIn.forIn : {β : Type u₁} → ρ → β → (α → β → m (ForInStep β)) → m β
-- constructor:
--   ForIn.mk.{u, v, u₁, u₂} {m : Type u₁ → Type u₂} {ρ : Type u} {α : outParam (Type v)}
--     (forIn : {β : Type u₁} → ρ → β → (α → β → m (ForInStep β)) → m β) : ForIn m ρ α

#print ForInStep
-- inductive ForInStep.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- ForInStep.done : {α : Type u} → α → ForInStep α
-- ForInStep.yield : {α : Type u} → α → ForInStep α

structure ToInfinityAndBeyond where
  n : Nat

namespace ToInfinityAndBeyond

partial def forIn
    {α} {m} [Monad m]
    (t : ToInfinityAndBeyond) (init : α) (f : Nat → α → m (ForInStep α)) :
    m α := do
  let a <- f t.n init
  match a with
  | ForInStep.done a => return a
  | ForInStep.yield a => forIn (ToInfinityAndBeyond.mk (t.n + 1)) a f

instance {m} [Monad m]: ForIn m ToInfinityAndBeyond Nat where
  forIn := forIn

def test : IO String := do
  for n in (ToInfinityAndBeyond.mk 1) do
    IO.println s!"{n}"
    if n == 3 then
      break
  return "Done!"

#eval test
-- 1
-- 2
-- 3
-- "Done!"

end ToInfinityAndBeyond

/-!
TODO:
  - ForIn from Stream (for free)
  - How the interface of Stream is similar to Python's iterator.

Q: **START** with Stream, discussion ForIn as an ulterior step (nah,
we are already deep in fold and monadic fold afaict)

-/

inductive TrafficLight where
| green : TrafficLight
| yellow : TrafficLight
| red : TrafficLight

instance : ToString TrafficLight where
  toString (tl : TrafficLight) := match tl with
  | .green => "green"
  | .yellow => "yellow"
  | .red => "red"


namespace V0

structure TrafficLightSequence where
  current : Option TrafficLight

namespace TrafficLightSequence

instance : Inhabited TrafficLightSequence where
  default := {current := some TrafficLight.green}

def next? (tls : TrafficLightSequence) : Option (TrafficLight × TrafficLightSequence) :=
  match tls.current with
  | some .green => some (.green, {current := some .yellow})
  | some .yellow => some (.yellow, {current := some .red})
  | some .red => some (.red, {current := none})
  | none => none

instance : Std.Stream TrafficLightSequence TrafficLight where
  next? := next?

def test : IO Unit := do
  let tls : TrafficLightSequence := default
  for tl in tls do
    IO.println tl

#eval test
-- green
-- yellow
-- red

end TrafficLightSequence

end V0


namespace V1

abbrev TrafficLightSequence := Fin 4 -- 0, 1, 2, 3
-- or define a new type definitionally equal, or wrap a Fin 4 in a struct, etc.
-- all these solutions have their quirks.

namespace TrafficLightSequence

instance : Inhabited TrafficLightSequence where
  default := 0

def next? (tls : TrafficLightSequence) : Option (TrafficLight × TrafficLightSequence) :=
  match tls with
  | 0 => some (.green, 1)
  | 1 => some (.yellow, 2)
  | 2 => some (.red, 3)
  | 3 => none

instance : Std.Stream TrafficLightSequence TrafficLight where
  next? := next?

def test : IO Unit := do
  let tls : TrafficLightSequence := default
  for tl in tls do
    IO.println tl

#eval test
-- green
-- yellow
-- red

end TrafficLightSequence

end V1

structure ZigZag where
  x : Nat
  y : Nat

namespace ZigZag

#print Std.Stream
-- class Std.Stream.{u, v} (stream : Type u) (value : outParam (Type v)) : Type (max u v)
-- number of parameters: 2
-- fields:
--   Std.Stream.next? : stream → Option (value × stream)
-- constructor:
--   Std.Stream.mk.{u, v} {stream : Type u} {value : outParam (Type v)} (next? : stream → Option (value × stream)) :
--     Std.Stream stream value

def next? (zz : ZigZag) : Option ((Nat × Nat) × ZigZag) :=
  let zz_next := match zz.x, zz.y with
  | 0, y => {x := y + 1, y := 0}
  | x, y => {x := x - 1, y := y + 1}
  some ((zz.x, zz.y), zz_next)

instance : Std.Stream ZigZag (Nat × Nat) where
  next? := next?

def test : IO Unit := do
  let zigzag : ZigZag := {x := 0, y := 0}
  for (x, y) in zigzag do
    IO.println s!"{(x, y)}"
    if x == 4 then
      break
  return ()

#eval test
-- (0, 0)
-- (1, 0)
-- (0, 1)
-- (2, 0)
-- (1, 1)
-- (0, 2)
-- (3, 0)
-- (2, 1)
-- (1, 2)
-- (0, 3)
-- (4, 0)

end ZigZag
