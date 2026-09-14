
/-!
TODO:
  - push Not
  - by_contra
  - excluded middle
-/

namespace Sandbox


/-!
`False`
--------------------------------------------------------------------------------
-/
/-!
`False` is a proposition with no term:
-/

#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:

/-!
As a consequence, a core, obviously impossible typing judgment is:
I found a term `false` or type `False`.
No you haven't, `False` is by construction uninhabited, it has no proof term!
(unless of course Lean's logic inconsistent... or you made it inconsistent by
adding some custom axioms!)
-/

/-!
`Not`
--------------------------------------------------------------------------------
-/

/-!
In Lean, to each proposition `P`, we may associate the negated proposition `¬P`
(or `Not P`). By definition, `¬P` is equal to `P → False`. Why this definition?
Because if you can find a proof `not_p` of `¬P`, you then have a function from
`P` to `False` and the only way this can work if it's `P` has no proof!
So having a proof of `¬P` means effectively: `P` has no proof.

For example, that works when `P` itself is `False`! We can build a proof
of `¬False`, i.e. `False → False`: the identity function from `False` to
`False` works perfectly for that!
-/

theorem not_false : ¬False := fun (false : False) => false

/-!
Now if a proposition `P` has a proof `p`, we can't build a function from
`P` to `False` (what would the image of `p` would be?), so `¬P` has no proof.
In other words
-/

theorem not_not (P : Prop) (p : P) : ¬¬P := fun (not_p : ¬P) => not_p p

/-!
Ex falso
--------------------------------------------------------------------------------

*Ex falso quodlibet*, or "priniciple of explosion" states that when you have
obtained a proof of `False`, you can derive any proposition (or object of any
type) you want! It is encapsulated into the elimination rule for `False`.

-/

#check False.elim
-- False.elim.{u} {C : Sort u} (h : False) : C

/-
For example:
-/

example (false : False) : 0 = 1 := false.elim

example (false : False) : { x : Nat // x < 0 } := false.elim

/-!
In tactic mode, when your your hypotheses yield a contradiction,
use the tactic `exfalso` to transform the goal into `False`
(of course by the principle of explosition, if you can prove `False`,
this is sufficient to prove your initial goal.)
-/

/-! Contradiction
--------------------------------------------------------------------------------

If you have proofs of `P` and `¬P` (i.e. `P → False`), you have a contradiction
... and an easy proof of `False`: just apply the proof of `¬P` to the proof of `P`!

-/

example {P : Prop} (p : P) (not_p : ¬P) : False := not_p p

/-!
Then by the principle of explosion, you can derive whatever you like from the
initial contradiction
-/

example {P : Prop} (p : P) (not_p : ¬P) : 1 + 1 = 3 := (not_p p).elim

/-
You can use the `term` absurd to combine both steps in one:
-/

#check absurd
-- absurd.{v} {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b

example {P : Prop} (p : P) (not_p : ¬P) : 1 + 1 = 3 := absurd p not_p

/-
In tactic mode, `contradiction` also works (and you don't need to name the
contradicting hypotheses, they will be search in the environnement).
-/

example {P : Prop} (p : P) (not_p : ¬P) : 1 + 1 = 3 := by contradiction



end Sandbox
