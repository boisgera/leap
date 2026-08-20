import Mathlib

/-!
By definition, `Set α` are propositions indexed by a term `a : α`.
-/

#check Set ℝ

example {α} : Set α = (α → Prop) := rfl

/-!
Then ... what is the characteristic functions of a set? What is the signature?
How do I define it?
-/

def charac_ {α} : Set α → α → ℝ :=
  sorry

/-!
This is *very, very* similar to trying to convert a Prop into a Bool... which is
an issue!

Indeed, if pick `α := Unit` to begin with, `Set α` is effectively the same
as `Prop` and getting à real equal to 0 or 1 out of it is the same thing as
getting a Bool. And this sub-problem we can "solve" with excluded middle:
-/

def c (p : Prop) : Bool :=
  match Classical.em p with
  | Or.inl p => true
  | Or.inr notP => false

/-!
... except of course that we cannot get anything but a Prop out of this...
Instead, let's try
-/

noncomputable def charac__ {α} : Set α → α → ℝ :=
  fun (s : Set α) (a : α) =>
    if a ∈ s then
      1
    else 0

/-!
Which fails since "being in s" is not decidable. But with
-/

open Classical

/-!
that works !!!
-/

noncomputable def charac {α} : Set α → α → ℝ :=
  fun (s : Set α) (a : α) =>
    if a ∈ s then
      1
    else 0

/-!
Claude tells me that:

> The moment you open Classical, Decidable (a ∈ s) resolves
> for any proposition, no actual decision procedure needed.
> It's not a real algorithm,
> it's Classical.choice wearing a Decidable costume

This is kinda nuts... Anyway, with `noncomputable` and this, we can make
it work.

-/

/-!
The "real deal" (from Mathlib) is `Set.indicator`
-/

#print Set.indicator
-- def Set.indicator.{u_1, u_3} : {α : Type u_1} → {M : Type u_3} → [Zero M] →
-- Set α → (α → M) → α → M :=
-- fun {α} {M} [Zero M] s f x => if x ∈ s then f x else 0

/-!
The source is interesting, we see a more targetted way to make it work,
without opening Classical, with a local declaration of a Decidable
instance for the Prop we are interested in and no more.
-/

noncomputable def charac' {α} : Set α → α → ℝ :=
  fun (s : Set α) (a : α) =>
    haveI := Classical.propDecidable (a ∈ s)
    if a ∈ s then
      1
    else 0
