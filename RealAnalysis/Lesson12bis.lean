import Mathlib

set_option pp.showLetValues true

/-!
Misc. stuff about finite or infinite subsequences.
-/

def SubSeq {α} (a b : ℕ → α) := ∃ (σ : ℕ → ℕ), StrictMono σ ∧ a = b ∘ σ

/-!
What if instead we select an (infinite) subset of ℕ and use that to
define a subsequence?
-/

#print Set.restrict
-- def Set.restrict.{u_1, u_6} : {α : Type u_1} → {π : α → Type u_6} →
--     (s : Set α) → ((a : α) → π a) → (a : ↑s) → π ↑a :=
--   fun {α} {π} s f x => f ↑x

def a (n : ℕ) : ℝ := (-2) ^ n

def S := {n : ℕ | n % 2 = 0}

#print Set.Finite
-- protected def Set.Finite.{u} : {α : Type u} → Set α → Prop :=
-- fun {α} s => Finite ↑s

#print Finite
-- inductive Finite.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Finite.intro : ∀ {α : Sort u} {n : ℕ} (a : α ≃ Fin n), Finite α

/-!
The `≃` notation stands for `Equiv`. `α ≃ β` is the type of functions from
`α → β` with a two-sided inverse.

```lean
structure Equiv (α : Sort*) (β : Sort _) where
  protected toFun : α → β -- Do NOT use directly; use the coercion instead.
  protected invFun : β → α -- Do NOT use directly; use the coercion of `e.symm` instead.
  protected left_inv : LeftInverse invFun toFun := by ...
  protected right_inv : RightInverse invFun toFun := by ...

@[inherit_doc]
infixl:25 " ≃ " => Equiv
```
-/


#print Function.LeftInverse
-- def Function.LeftInverse.{u_1, u_2} :
--     {α : Sort u_1} → {β : Sort u_2} →
--     (β → α) → (α → β) → Prop :=
--     fun {α} {β} g f => ∀ (x : α), g (f x) = x

def bijectionFin2Bool : Fin 2 ≃ Bool := {
  toFun (n : Fin 2) : Bool :=
    match n with
    | 0 => false
    | 1 => true
  invFun (bool : Bool) : Fin 2 :=
    match bool with
    | false => 0
    | true => 1
  left_inv := by
    rw [Function.LeftInverse]
    grind
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    grind
}

/-
Note: `Equiv` is a `Type`, not a `Prop`! If this is want you need,
instead of `α ≃ β`, consider `Cardinal.mk α = \Cardinal.mk β`.
Use `Cardinal.eq.mpr` to get this prop from the bijection.
-/

#print Cardinal
-- def Cardinal.{u} : Type (u + 1) :=
-- Quotient Cardinal.isEquivalent

#print Cardinal.isEquivalent
-- def Cardinal.isEquivalent.{u} : Setoid (Type u) :=
-- { r := fun α β => Nonempty (α ≃ β), iseqv := Cardinal.isEquivalent._proof_1 }

#check Cardinal.eq
-- Cardinal.eq.{u} {α β : Type u} : Cardinal.mk α = Cardinal.mk β ↔ Nonempty (α ≃ β)

#print Nonempty
-- inductive Nonempty.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α

example : Cardinal.mk (Fin 2) = Cardinal.mk Bool :=
  let nonempty := Nonempty.intro bijectionFin2Bool
  Cardinal.eq.mpr nonempty

def EvenNumber := {n : ℕ // n % 2 = 0}

example : ℕ ≃ EvenNumber := {
  toFun (n : ℕ) := ⟨2 * n, by grind⟩
  invFun (en : EvenNumber) :=
    let ⟨n, _⟩ := en
    n / 2
  left_inv := by
    rw [Function.LeftInverse]
    grind
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    grind
}

example : ¬ (Bool ≃ Fin 3) := by
  admit
