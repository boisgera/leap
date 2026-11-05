import Mathlib

/-!
Already done at this stage in `IO`:

  - `do` blocks and sequencing
  - `return`
  - `<-`

-/

/-!
More constructs in IO / do blocks
--------------------------------------------------------------------------------

Mutable variables and for loops.

-/

def main (args : List String) : IO UInt32 := do
  let mut sum : Nat := 0
  for arg in args do
    let number? := arg.toNat?
    match number? with
    | none => continue -- filter out;
    -- we could also break or fail immediately with `return 1`
    | some number => sum := sum + number
  IO.println s!"sum: {sum}"
  return 0

#eval main ["1", "2", "3", "😊", "4", "5"]
-- sum: 15


/-!
Common use cases
--------------------------------------------------------------------------------

TODO: start with `Id`. Then `StateM`, then `Option`/`Except`?

### `Option` and `Except ε`.

**TODO** Ex with safeFloat, first without sugar, then with ; Specific API : `<|>`,
`throw`, `catch`?

### `State`.

**TODO** Function counter? Random seed "state"? (try with a random die roll)

`get`, `modify`, etc.


xkcd: https://xkcd.com/221/

-/

def XKCD.getRandomNumber : Nat :=
  4 -- chosen by fair dice roll.
    -- guaranteed to be random.


/-!
[LCG](https://en.wikipedia.org/wiki/Linear_congruential_generator)
-/

def getRandomNumber (seed : UInt64) : Nat × UInt64 :=
  let s := seed * 6364136223846793005 + 1442695040888963407
  (((s >>> 32) % 6).toNat + 1, s)

#eval getRandomNumber (seed := 42) -- returns a dice roll and a new seed.
-- (4, 10481999410520546993)

def sumOfThreeDiceBad (seed : UInt64 := 42) : Nat :=
  let (die1, seed1) := getRandomNumber seed
  let (die2, seed2) := getRandomNumber seed1
  let (die3, _seed3) := getRandomNumber seed2
  die1 + die2 + die3

#eval sumOfThreeDiceBad
-- 13

#eval sumOfThreeDiceBad
-- 13

/-!
After having used the random stream, we also have to return
the current seed for the random process coming after to use:
-/

def sumOfThreeDice (seed : UInt64 := 42) : Nat × UInt64 :=
  let (die1, seed1) := getRandomNumber seed
  let (die2, seed2) := getRandomNumber seed1
  let (die3, seed3) := getRandomNumber seed2
  (die1 + die2 + die3, seed3)

#eval sumOfThreeDice (seed := 42)
-- (14, 7615522811268512075)

/-!
Now we can invoke the
-/

#eval do
  let (sum1, seed1) := sumOfThreeDice (seed := 42)
  IO.println sum1
  let (sum2, _seed2) := sumOfThreeDice (seed := seed1)
  IO.println sum2
-- 13
-- 12

/-!
For any type `σ`, `StateM σ` is a monad (the state monad).
For any type `alpha`, `StateM σ α` is definitionally equal to
the type of functions `σ -> α × σ`:
-/

theorem state_monad_def : ∀ (σ α : Type), StateM σ α = (σ -> α × σ) := by
  intro σ α
  rfl

/-!

Let's redefine a random die value generator using this state monad.
In this context, the state type is `σ := UInt64`. Let's call this
monad `LCG.Random`.
-/

abbrev LCG.Random := StateM UInt64

def getRandomNumberM : LCG.Random Nat := fun (seed : UInt64) =>
  let s := seed * 6364136223846793005 + 1442695040888963407
  (((s >>> 32) % 6).toNat + 1, s)

/-!
We can use `getRandomNumberM` exactly as `getRandomNumber` before
(well, except for the use of named arguments ; but we can still fake it
if we want)
-/

#eval getRandomNumberM 42
-- (4, 10481999410520546993)

#eval getRandomNumberM (let seed := 42; seed)
-- (4, 10481999410520546993)

/-!
We can also use the monadic API of `State64` for a slightly different
definition of the random generator:
-/

def getRandomNumberMAlt : LCG.Random Nat := do
  -- In the rhs: the action that outputs the state and leave it unchanged.
  let seed : UInt64 <- fun (s) => (s, s)
  let newSeed := seed * 6364136223846793005 + 1442695040888963407
  -- In the rhs: the action that replaces the state (and output the unit value)
  let _ : Unit <- fun (_) => ((), newSeed)
  let dieRoll : Nat := ((newSeed >>> 32) % 6).toNat + 1
  -- Now output the die roll value, keep the value of the state
  fun (s) => (dieRoll, s)

#check getRandomNumberMAlt 42
-- getRandomNumberMAlt 42 : Id (ℕ × UInt64)

#check getRandomNumberMAlt 42 |>.run
-- (getRandomNumberMAlt 42).run : ℕ × UInt64

#eval getRandomNumberMAlt 42
-- (4, 10481999410520546993)


/-!
This is a bit klunky right? Fortunately the last action can be coded using
the general monadic `return` and the previous one are `get` and `set`. So
we can do instead:
-/

def getRandomNumberMAlt2 : LCG.Random Nat := do
  -- In the rhs: the action that outputs the state and leave it unchanged.
  let seed <- get
  let newSeed := seed * 6364136223846793005 + 1442695040888963407
  set newSeed
  let dieRoll : Nat := ((newSeed >>> 32) % 6).toNat + 1
  return dieRoll

#eval getRandomNumberMAlt2 42
-- (4, 10481999410520546993)

#eval getRandomNumberMAlt2.run 42
-- (4, 10481999410520546993)

#eval getRandomNumberMAlt2.run' 42
-- 4

/-!
Now we can use the same style to reimplement `sumOfTheeDices`
-/

def sumOfThreeDiceAlt : LCG.Random Nat := do
  let die1 <- getRandomNumberMAlt2
  let die2 <- getRandomNumberMAlt2
  let die3 <- getRandomNumberMAlt2
  return die1 + die2 + die3

#eval sumOfThreeDiceAlt.run 42
-- (14, 7615522811268512075)

#eval sumOfThreeDiceAlt.run' 42
-- 14

/-!

### `Id`

**TODO.** Explain that the identity monad is useful when one want to
implement pure functions (no side-effect) in an imperative style.

-/

namespace Fibonacci

def fibNaiveRec (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fibNaiveRec n + fibNaiveRec (n + 1)

#eval fibNaiveRec 8 -- 21

def fibTailRec (n : Nat) (f0 : Nat := 0) (f1 : Nat := 1) : Nat :=
  match n with
  | 0 => f0
  | 1 => f1
  | n + 2 => fibTailRec (n + 1) f1 (f0 + f1)

#eval fibTailRec 8 -- 21

#check Id
-- Id.{u} (type : Type u) : Type u

#print Id
-- @[implicit_reducible] def Id.{u} : Type u → Type u :=
-- fun type => type

theorem Id_def : ∀ (α : Type), Id α = α := by
  intro α
  rfl

#eval 0...3
-- { lower := 0, upper := 3 }

#check 0...3 -- Range, closed/open
-- 0...3 : Std.Rco ℕ

#eval (0...3).toList
-- [0, 1, 2]


def fibMonadic (n : Nat) : Id Nat := do
  let mut f0 := 0
  let mut f1 := 1
  if n = 0 then
    return f0
  else
    for _ in 0...n do
      (f0, f1) := (f1, f0 + f1)
  return f1

#check fibMonadic 8
-- fibMonadic 8 : Id Nat

#eval (fibMonadic 8 : Nat)
-- 13

#check Id.run
-- Id.run.{u_1} {α : Type u_1} (x : Id α) : α

#print Id.run
-- @[implicit_reducible] protected def Id.run.{u_1} : {α : Type u_1} → Id α → α :=
-- fun {α} x => x

def fibIdRun (n : Nat) : Nat := Id.run do
  let mut f0 := 0
  let mut f1 := 1
  if n = 0 then
    return f0
  else
    for _ in 0...n do
      (f0, f1) := (f1, f0 + f1)
  return f1

#check fibIdRun 8
-- fibIdRun 8 : Nat

#eval fibIdRun 8
-- 13

end Fibonacci

/-!

### `List` ?

(only via Mathlib)

-/

namespace ListMonad

def square (n : Nat) : Nat := n * n

def squareList (ns : List Nat) : List Nat := do
  let n <- ns        -- extract a generic Nat `n` from the list
  let m := square n  -- compute its square
  return m           -- make a List Nat out of it

#eval squareList [1, 2, 3]
-- [1, 4, 9]

def squareList' (ns : List Nat) : List Nat := do
  return square (<- ns)

#eval squareList' [1, 2, 3]
-- [1, 4, 9]

/-!
This is only available in Mathlib and a bit frown upon in Mathlib, that would
rather keep Monads for control flow. And there is no new feature here, since
the same "vectorized computation" can be performed by:
-/


#eval [1, 2, 3].map square


end ListMonad

/-!

### Task ?

### Monad transformers

Ex : Option + State for parsing.




-/

/-!
Desugaring
--------------------------------------------------------------------------------
TODO :
  - `*>`, `>>=`, `pure`, `>==>`,
  - laws.
  - desugar some simple examples, and more complex ones.
    Ex: 2 println, print the current timestamp, etc.

Desugaring of `ForIn`

-/
