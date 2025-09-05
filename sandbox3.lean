
/-
Function with a `Unit` argument are often used in conjunction with the
`Thunk` type to implement [lazy computations](https://lean-lang.org/doc/reference/latest//Basic-Types/Lazy-Computations/#Thunk).

To begin with, we need to realize that Lean is *eager*: it will evaluate the
arguments of a function before it starts evaluating the function itself.
That includes situation where we could have avoided such computations.
Consider for example:
-/

def dbg_two :=
  dbg_trace "⌛"
  2

def f (n : Nat) (use : Bool) : Nat :=
  if use then
    n
  else
    0

#eval f dbg_two (use := true)
-- ⌛
-- 0

#eval f dbg_two (use := false)
-- ⌛
-- 2

/-
In the second case, we didn't need to evaluate `dbg_two` to produce the
result of `f` but Lean did it anyway. We have a way to deal around that
if we replace the `Nat` argument with a `Unit -> Nat` function argument
that we will evaluate only when we need it:
-/

def dbg_two' : Unit -> Nat :=
  fun () =>
    dbg_trace "⌛"
    2

#check dbg_two'
-- dbg_two' : Unit → Nat

#eval dbg_two' ()
-- ⌛
-- 2

def f' (n : Unit -> Nat) (use : Bool) : Nat :=
  if use then
    n ()
  else
    0

#eval f' dbg_two' (use := false)
-- 0

#eval f' dbg_two' (use := true)
-- ⌛
-- 2

/-
It works!
The downside of this is that we add to redesign the whole thing
and the the user of `f'` now needs to remember to
use the more complex `dbg_two'` instead of `dbg_two`.
-/

/-
Fortunately, their is a way to change that if we use the `Thunk` type.
It's a simple wrapper around functions with a `Unit` argument:
-/

#check Thunk.mk
-- Thunk.mk.{u} {α : Type u} (fn : Unit → α) : Thunk α

def thunk := Thunk.mk dbg_two'

#eval thunk.get
-- ⌛
-- 2

/-
But a term `e` of type `α` will automatically be
[converted to the thunk](https://lean-lang.org/doc/reference/latest///Basic-Types/Lazy-Computations/#Thunk-coercions)
`Thunk.mk fun () => e : Thunk α` when needed. And that delays the evaluation of
the original term `e`. In action, this fact allows use to get the benefit
of lazy computation with the ease of use of our original API:

-/


def f'' (n : Thunk Nat) (use : Bool) : Nat :=
  if use then
    n.get
  else
    0

#eval f'' dbg_two (use := false)
-- 0

#eval f'' dbg_two (use := true)
-- ⌛
-- 2
