
#check Functor

#print Functor
-- class Functor.{u, v} (f : Type u -> Type v) : Type (max (u + 1) v)
-- number of parameters: 1
-- fields:
--   Functor.map : {α β : Type u} -> (α -> β) -> f α -> f β
--   Functor.mapConst : {α β : Type u} -> α -> f β -> f α :=
--     fun {α β} => Functor.map ∘ Function.const β
-- constructor:
--   Functor.mk.{u, v} {f : Type u -> Type v} (map : {α β : Type u} -> (α -> β) -> f α -> f β)
--     (mapConst : {α β : Type u} -> α -> f β -> f α) : Functor f

/-
A functor `F` is a type class that:

  - consumes a type-level function `f` (e.g. `List`, `Option`, etc.),

  - returns an object that has a `map` method whose signature is
    `{α β : Type u} -> (α -> β) -> f α -> f β`

-/

/-
`List` is a functor; `List.map f` applies `f` to each element.
-/
#eval [1, 2, 3].map (· + 1)
-- [2, 3, 4]

/-
`Option` is a functor; `Option.map f` applies `f` to the wrapped value or
returns `none` if the option was `none` to begin with.
-/
#eval (some 0).map (· + 1)
-- some 1

#eval none.map (· + 1)
-- none

/-
`IO` is a functor. But it's a bit harder to show since the `map` method
is resolved as something that returns a `EStateM` by default...
-/

def esm43 := (pure 42 : IO Nat).map (· + 1)

#check esm43
-- EStateM IO.Error IO.RealWorld Nat

-- #eval (pure 42 : IO Nat).map (· + 1)
-- unable to synthesize `MonadEval` instance to adapt
--   EStateM IO.Error IO.RealWorld Nat
-- to `IO` or `Lean.Elab.Command.CommandElabM`.

/-
We need to
-/

def io43 : IO Nat := (pure 42 : IO Nat).map (· + 1)

#eval io43
-- 43

/-
Well, anyway at the end of the say, the behavior of `IO.map` is quite
similar to what we get for `Option.map` I guess? But since pure values don't
extinguish what `IO` is doing so I guess that it's more complex than
that. What's happening if I do:
-/

def action : IO Unit := IO.println "Hello world!"

def actionSuccess : IO UInt32 := action.map fun (_: Unit) => 0

#eval actionSuccess
-- Hello world!
-- 0

/-
OK, nice! So I am adding a "value transformer" at the end of the action
chain, without any impact on the side-effects.
-/

/-
Let's build our own instance of `Functor` now. We'll do that for a `Tree`
type (binary tree), which is quite similar to the `List` type.
-/

inductive Tree (α : Type u) : Type u where
| nil : Tree α
| node : α -> Tree α -> Tree α -> Tree α

def Tree.map {α β : Type u} (f : α -> β) : Tree α -> Tree β
| nil => nil
| node a tl tr => node (f a) (map f tl) (map f tr)

instance : Functor Tree where
  map := Tree.map

def t :=
  Tree.node
    0
    Tree.nil
    (
      Tree.node
        1
        Tree.nil
        (
          Tree.node
            2
            Tree.nil
            Tree.nil
        )
    )

#eval t
-- Tree.node 0 (Tree.nil) (Tree.node 1 (Tree.nil) (Tree.node 2 (Tree.nil) (Tree.nil)))

#eval t.map (· + 1)
-- Tree.node 1 (Tree.nil) (Tree.node 2 (Tree.nil) (Tree.node 3 (Tree.nil) (Tree.nil)))

/-
Technically in Lean 4, functions are not functors, probably for typeclass
resolution issues (wild guess?). But they "should", with map operating on
the return value (?).
-/
-- #eval (· * 2).map (· + 1)
-- Invalid field `map`: The environment does not contain `Function.map`
--   fun x => x * 2
-- has type
--   (x : ?m.9) -> ?m.11 x
