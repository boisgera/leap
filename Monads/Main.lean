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


### `Id`

The identity monad is useful when one want to implement pure functions
(with no side-effect) but an imperative style is more convenient.

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

#print Id -- the identity function!
-- @[implicit_reducible] def Id.{u} : Type u → Type u :=
-- fun type => type

theorem Id_def : ∀ (α : Type), Id α = α := by
  intro α
  rfl

#eval 0...3
-- { lower := 0, upper := 3 }

#check 0...3 -- Range, closed/open ; other variants exist!
-- 0...3 : Std.Rco ℕ

#eval (0...3).toList
-- [0, 1, 2]


def fibId (n : Nat) : Id Nat := do
  let mut (f0, f1) := (0, 1)
  if n = 0 then
    return f0
  else
    for _ in 0...(n - 1) do
      (f0, f1) := (f1, f0 + f1)
  return f1

#check fibId 8
-- fibId 8 : Id Nat

/-!
There is a small issue here: the return type is not `Nat` but `Id Nat`. Most
of the time, that won't be an issue (these type are definitionally equal!),
for example, we can directly `#eval` the result or assign it to a identifier
of type `Nat`:
-/

#eval fibId 8
-- 21

def fib8 : Nat := fibId 8

#check fib8 -- Fibonacci.fib8 : ℕ

#eval fib8
-- 21

/-!
But if we want to be certain that there is no issue: we can explicitly coerce
the term of type `Id Nat` to `Nat` with `Id.run`:
-/

#check Id.run
-- Id.run.{u_1} {α : Type u_1} (x : Id α) : α

#print Id.run
-- @[implicit_reducible] protected def Id.run.{u_1} : {α : Type u_1} → Id α → α :=
-- fun {α} x => x

def fibIdRun (n : Nat) : Nat := Id.run do
  let mut (f0, f1) := (0, 1)
  if n = 0 then
    return f0
  else
    for _ in 0...(n - 1) do
      (f0, f1) := (f1, f0 + f1)
  return f1

#check fibIdRun 8
-- fibIdRun 8 : Nat

#guard fibIdRun 8 = fibId 8

end Fibonacci

/-!


### `State`.

The `StateM` monad will be useful to design with more convenience functions
that have a side-effect, but limited to a given variable which we call
the state.

-/

/--
Source: <https://xkcd.com/221/>
-/
def XKCD.roll : Nat :=
  4 -- chosen by fair dice roll.
    -- guaranteed to be random.

#eval XKCD.roll
-- 4

#eval XKCD.roll
-- 4

/-!
To get *different* results each time we call this function,
we can use a small [LCG] random number generator.

[LCG](https://en.wikipedia.org/wiki/Linear_congruential_generator)
-/

namespace Die

def roll (seed : UInt64) : Nat × UInt64 :=
  let s := seed * 6364136223846793005 + 1442695040888963407
  (((s >>> 32) % 6).toNat + 1, s)

/-!
To use it, you have to provide a `UInt64` *seed* to initialize the random
number generation, then each call will provide you with a "random" die roll
value and a new seed that you need to compute further random values.
-/

#eval roll 42 -- returns a dice roll and a new seed.
-- (4, 10481999410520546993)

#eval roll 42 -- this is pure and thus deterministic!
-- (4, 10481999410520546993)

def sumOfThreeDiceBad (seed : UInt64) : Nat :=
  let (die1, seed1) := roll seed
  let (die2, seed2) := roll seed1
  let (die3, _seed3) := roll seed2
  die1 + die2 + die3

#eval sumOfThreeDiceBad 42
-- 13

#eval sumOfThreeDiceBad 42 -- again, probably not what you want!
-- 13

/-!
After having used the random stream, we also have to return
the current seed for the random process coming after to use:
-/

def sumOfThreeDice (seed : UInt64 := 42) : Nat × UInt64 :=
  let (die1, seed1) := roll seed
  let (die2, seed2) := roll seed1
  let (die3, seed3) := roll seed2
  (die1 + die2 + die3, seed3)

#eval sumOfThreeDice 42
-- (14, 7615522811268512075)

/-!
Now we can invoke the random function twice in a row:
-/

#eval do
  let seed0 := 42
  let (sum1, seed1) := sumOfThreeDice seed0
  IO.println sum1
  let (sum2, _seed2) := sumOfThreeDice seed1
  IO.println sum2
-- 13
-- 12

/-!
Let's see how monads can help use there.
For any type `σ`, `StateM σ` is the monad with state `σ`.
For any type `alpha`, `StateM σ α` represent the type of functions that
given a state `σ` compute a value of type `α` and a new state `σ`.
It is actually definitionally equal to the type of functions `σ -> α × σ`:
-/

theorem state_monad_def : ∀ (σ α : Type), StateM σ α = (σ -> α × σ) := by
  intro σ α
  rfl

/-!

Let's redefine a random die value generator using this state monad.
In this context, the state type is `σ := UInt64`. Let's call this
monad `Random`.
-/

abbrev Random := StateM UInt64

def rollM : Random Nat := fun (seed : UInt64) =>
  let s := seed * 6364136223846793005 + 1442695040888963407
  (((s >>> 32) % 6).toNat + 1, s)

/-!
We can use `rollM` as we used `roll` before.
-/

#eval rollM 42
-- (4, 10481999410520546993)

/-!
We can also use the monadic API of `State64` for a slightly different
definition of the random generator. Remember that `do` blocks can
sequence actions -- here function that given a state compute a value and
update the state -- and that in this context the left arrow `<-`
executes the action and outputs the value. Thus, we can write:
-/

def rollMAlt : Random Nat := do
  -- execute the action that outputs the state and leave it unchanged.
  let seed : UInt64 <- fun (s) => (s, s)
  let newSeed := seed * 6364136223846793005 + 1442695040888963407
  -- execute the action that replaces the state (and output the unit value)
  let _ : Unit <- fun (_) => ((), newSeed)
  let dieRoll : Nat := ((newSeed >>> 32) % 6).toNat + 1
  -- output the die roll value, keep the state unchanged
  fun (s) => (dieRoll, s)

#check rollMAlt 42
-- rollMAlt 42 : Id (ℕ × UInt64)

/-!
If needed, we can `run` our way around the (superficial) typing issue:
-/

#check (rollMAlt 42).run
-- (rollMAlt 42).run : ℕ × UInt64

#eval rollMAlt 42
-- (4, 10481999410520546993)


/-!
This is a bit klunky right? Fortunately the last action can be coded using
the general monadic `return` and the previous one are `get` and `set`. So
we can do instead:
-/

def rollMAlt2 : Random Nat := do
  let seed <- get
  let newSeed := seed * 6364136223846793005 + 1442695040888963407
  set newSeed
  let dieRoll : Nat := ((newSeed >>> 32) % 6).toNat + 1
  return dieRoll

#eval rollMAlt2 42
-- (4, 10481999410520546993)

#eval rollMAlt2.run 42
-- (4, 10481999410520546993)

/-!
In the state monad we can also use `run'` to get only the value.
-/

#eval rollMAlt2.run' 42
-- 4

/-!
Now we can use the same style to reimplement `sumOfTheeDices`
-/

def sumOfThreeDiceAlt : Random Nat := do
  let die1 <- rollMAlt2
  let die2 <- rollMAlt2
  let die3 <- rollMAlt2
  return die1 + die2 + die3

#eval sumOfThreeDiceAlt.run 42
-- (14, 7615522811268512075)

#eval sumOfThreeDiceAlt.run' 42
-- 14

#eval (do
  sumOfThreeDiceAlt -- throw way the first result (14)
  let sum <- sumOfThreeDiceAlt -- pick the 2nd one
  return sum
).run' 42
-- 11

end Die

/-!

### `Option` and `Except ε`.

**TODO** Ex with safeFloat, first without sugar, then with ; Specific API : `<|>`,
`throw`, `catch`?

-/

namespace SafeFloat

#eval 0.0 / 0.0 -- NaN

def div? (x? y? : Option Float) : Option Float :=
  match y? with
  | none => none
  | some y =>
    if y = 0 then
      none
    else
      match x? with
      | none => none
      | some x => some (x / y)

#eval Float.log (-1.0) -- Nan

def log? (x? : Option Float) : Option Float :=
  match x? with
  | none => none
  | some x => if x ≤ 0 then none else some x.log

#eval Float.sqrt (-1.0)
-- NaN

def sqrt? (x? : Option Float) : Option Float :=
  match x? with
  | none => none
  | some x => if x < 0 then none else some x.sqrt

def f (x : Float) : Float :=
  x.log.sqrt

#eval f 0.1
-- NaN

def f? (x? : Option Float) : Option Float :=
  match x? with
  | none => none
  | some x =>
    match (log? x) with
    | none => none
    | some y => sqrt? y

#eval f? (some 10.0)
-- some 1.517427

#eval f? (some 0.1)
-- none

/-!
But `Option` is also a monad ; let's use a `do` block to define `f`.
-/

def fAlt? (x? : Option Float) : Option Float := do
  let x <- x?
  let y <- log? x
  let z <- sqrt? y
  return z

#eval fAlt? (some 10.0)
-- some 1.517427

#eval fAlt? (some 0.1)
-- none

/-!
or even
-/

def fAlt2? (x? : Option Float) : Option Float := do
  sqrt? (<- log? (<- x?))

#eval fAlt2? (some 10.0)
-- some 1.517427

#eval fAlt2? (some 0.1)
-- none

/-!
There are two additional constructs for `Option` that can be useful in this
context: `failure` is a synonym for `none` that better represent what `none`
stands for.  The "or else" operator `<|>` applied to two options outputs the
left option if it is not `none` otherwise it output the right-hand side.
-/

#eval (failure : Option Float)
-- none

#eval (some 3.14 <|> some 1.0)
-- some 3.140000

#eval (none <|> some 1.0)
-- some 1.000000

#eval (none <|> none : Option Float)
-- none

def sqrtAlt? (x? : Option Float) : Option Float := do
  let x <- x?
  if x < 0 then
    failure
  else
    return x.sqrt

/-!
We can also use equivalent constructs that will feel more familiar to
imperative programmers: `throw` and `try/catch`.
-/

#eval (throw () : Option Float)
-- none

#eval
  try
    some 3.14
  catch _ =>
    some 1.0
-- some 3.140000

#eval
  try
    none
  catch _ =>
    some 1.0
-- some 1.000000

#eval
  try
    (none : Option Float)
  catch _ =>
    none
-- none


end SafeFloat


/-!
`throw` and `try-catch` are a bit underwhelming with options.
They really shine with `Except` values, which are very similar.
Like options, except values can either hold a value when a computation
succeed or signal an error; however, they can also hold data in the
error case, for example an error message, something an option cannot do.

Note: many language call the `Except` type `Result` instead which is probably
more appropriate (an `Except` value is *not* an exception).

-/

#print Except
-- inductive Except.{u, v} : Type u → Type v → Type (max u v)
-- number of parameters: 2
-- constructors:
-- Except.error : {ε : Type u} → {α : Type v} → ε → Except ε α
-- Except.ok : {ε : Type u} → {α : Type v} → α → Except ε α

/-!
Using this, we could reimplement our safe float computations with error
messages, using the fact that for any type `α`, `Except α` is a monad.
-/

namespace SafeFloat2

abbrev FloatResult := Except String Float

def log? (x? : FloatResult) : FloatResult :=
  match x? with
  | Except.error e => Except.error e -- return the first error
  | Except.ok x =>
    if x ≤ 0 then -- return the appropriate error
      Except.error s!"{x} is nonpositive"
    else
      Except.ok x.log

#eval log? (Except.ok 1.0)
-- Except.ok 0.000000

#eval log? (Except.ok (-1.0))
-- Except.error "-1.000000 is nonpositive"

#eval log? (Except.error "already doomed")
-- Except.error "already doomed"

/-!
We can have a more concise implementation using a `do` block as well
-/

def sqrtAlt? (x? : FloatResult) : FloatResult := do
  let x <- x? -- will re-throw x? if it's an error
  if x ≤ 0 then
    throw s!"{x} is nonpositive" -- error + short-circuit
  return x.log


end SafeFloat2

/-



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


-/

#print StateT
-- @[implicit_reducible]
-- def StateT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
-- fun σ m α => σ → m (α × σ)

/-
`StateM` that we have used before is actually also a special case of `StateT`
when the monad `m` is taken to be `Id`.
-/

example (σ α : Type u) : StateM σ α = StateT σ Id α := by
  rfl

/-!
A special useful case: describe operations with a state that can fail.
-/

example (σ α : Type u) : StateT σ Option α = (σ → Option (α × σ)) := by
  rfl

/-!
Now in do block you have all the good stuff from both monads:
`failure`, `<|>`, `get`, `set`, etc.
-/

/-!
TODO: something even simpler, without recursion to begin with.
Bash argument parsing for example? That's going to be a bit painful
with the nested quotes maybe... Brainfuck with the 8 symbols and
arbitrary spaces/newlines between them? Yes, maybe.

-/



/-!

TODO: a tree parser with parens would be simpler?

Example: tiny language parser:
-/

inductive Expr where
  | number (digit : Fin 10)
  | add (e1 e2 : Expr)
  deriving Repr

namespace Expr

/-!
The state here is what's left to parse (a list of chars).
-/
abbrev Parser := StateT (List Char) Option

def Parser.number : Parser Expr := do
  match (<- get) with
  | [] => failure
  | c :: cs =>
    let code := c.toNat
    let mut digit : Fin 10 := 0
    if '0'.toNat ≤ code ∧ code ≤ '9'.toNat then
      let n := code - '0'.toNat
      digit := Fin.ofNat 10 n
      set cs
      return Expr.number digit
    else
      failure

#eval Parser.number.run "9".toList
-- some (Expr.number 9, [])

#eval Parser.number.run "999".toList
-- some (Expr.number 9, ['9', '9'])

#eval Parser.number.run "".toList
-- none

#eval Parser.number.run "A".toList
-- none


def Parser.space : Parser Unit := do
  sorry

def Parser.oneOrMoreSpaces : Parser Unit := do
  sorry

mutual

def Parser.add : Parser (Expr × Expr) := do
  sorry

def Parser.expr : Parser Expr := do
  sorry

end


end Expr

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
