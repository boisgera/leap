import Mathlib

#print unitInterval
-- @[reducible] def unitInterval : Set ℝ :=
-- Set.Icc 0 1

-- Turn the (sub)set { x : ℝ | 0 ≤ x ∧ x ≤ 1 } into the subtype
-- { x : ℝ // 0 ≤ x ∧ x ≤ 1 }
abbrev I : Type := ↑unitInterval -- nota: def won't work here if we want to
-- inherit the Preorder structure (which we do)

-- Could we work on EReal instead? On a an abstract CompleteLinearOrder so
-- that both versions are available afterwards?

#print CompleteLinearOrder
-- class CompleteLinearOrder.{u_8} (α : Type u_8) : Type u_8
-- number of parameters: 1

#synth CompleteLinearOrder I
-- instCompleteLinearOrderElemIccOfFactLe

#synth CompleteLinearOrder EReal
-- instCompleteLinearOrderEReal

#print Monotone
-- def Monotone.{u, v} : {α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] → (α → β) → Prop :=
-- fun {α} {β} [Preorder α] [Preorder β] f => ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

#print Antitone
-- def Antitone.{u, v} : {α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] → (α → β) → Prop :=
-- fun {α} {β} [Preorder α] [Preorder β] f => ∀ ⦃a b : α⦄, a ≤ b → f b ≤ f a

/-!
OK, let's collapse everything to CompleteLinearOrder, don't dwell into Preorder
and stuff. Just check that every CompleteLinearOrder is a Preorder.
-/

example {α : Type*} [CompleteLinearOrder α] : Preorder α := inferInstance

/-!
The `InfSet` type class, that defines a `sInf` operation has no semantics
whatsoever.
-/
#check sInf
-- InfSet.sInf.{u_1} {α : Type u_1} [self : InfSet α] : Set α → α

#print InfSet
-- class InfSet.{u_1} (α : Type u_1) : Type u_1
-- number of parameters: 1
-- fields:
--   InfSet.sInf : Set α → α
-- constructor:
--   InfSet.mk.{u_1} {α : Type u_1} (sInf : Set α → α) : InfSet α

/-!
The lawful version is `CompleteSemilatticeInf`:
-/

#print CompleteSemilatticeInf
-- class CompleteSemilatticeInf.{u_8} (α : Type u_8) : Type u_8
-- ...
--   CompleteSemilatticeInf.isGLB_sInf : ∀ (s : Set α), IsGLB s (sInf s)
-- ...

#print IsGLB
-- def IsGLB.{u_1} : {α : Type u_1} → [LE α] → Set α → α → Prop :=
-- fun {α} [LE α] s => IsGreatest (lowerBounds s)

#print IsGreatest
-- def IsGreatest.{u_1} : {α : Type u_1} → [LE α] → Set α → α → Prop :=
-- fun {α} [LE α] s a => a ∈ s ∧ a ∈ upperBounds s

#print lowerBounds
-- def lowerBounds.{u_1} : {α : Type u_1} → [LE α] → Set α → Set α :=
-- fun {α} [LE α] s => {x | ∀ ⦃a : α⦄, a ∈ s → x ≤ a}

#print upperBounds
-- def upperBounds.{u_1} : {α : Type u_1} → [LE α] → Set α → Set α :=
-- fun {α} [LE α] s => {x | ∀ ⦃a : α⦄, a ∈ s → a ≤ x}

/-!
Let's quickly forget about these details and just check that everything
works perfectly in `CompleteLinearOrder`:
-/

example {α : Type*} [CompleteLinearOrder α] : InfSet α := inferInstance

example {α : Type*} [CompleteLinearOrder α] : CompleteSemilatticeInf α := inferInstance


/-!
--------------------------------------------------------------------------------
-/

#check sInf_le
-- sInf_le.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α}
-- (h : a ∈ s) : sInf s ≤ a

#check le_sInf
-- le_sInf.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α}
-- (h : ∀ b ∈ s, a ≤ b) : a ≤ sInf s

#print lowerBounds
-- def lowerBounds.{u_1} : {α : Type u_1} → [LE α] → Set α → Set α :=
-- fun {α} [LE α] s => {x | ∀ ⦃a : α⦄, a ∈ s → x ≤ a}

#check sInf_le_iff
-- sInf_le_iff.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α} :
--   sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a

#check le_sInf_iff
-- le_sInf_iff.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α} :
-- a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b

namespace Galois

-- Wrong as stated apparently ; we need (?) something like:
-- For a monotone f : A → B, there is a g : B → A
-- with b ≤ f a ↔ g b ≤ a iff,
-- for every b, the set {a | b ≤ f a} has a least element.
-- In that case g b is that least element, and g is unique.

#print IsLeast
-- def IsLeast.{u_1} : {α : Type u_1} → [LE α] → Set α → α → Prop :=
-- fun {α} [LE α] s a => a ∈ s ∧ a ∈ lowerBounds

/-!
Not used explicitly anywhere!
-/
lemma image_preimage_subset {α β} (f : α → β) (s : Set β) :
    f '' f ⁻¹' s ⊆ s := by
  intro x hx
  simp only [Set.mem_image, Set.mem_preimage] at hx
  have ⟨x1, hx1_in, hx1_eq⟩ := hx
  rw [hx1_eq] at hx1_in
  assumption

def sInfPreserving {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) := ∀ s, sInf (f '' s) = f (sInf s)

theorem monotonic_of_sInfPreserving {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (h : sInfPreserving f) : Monotone f := by
  rw [sInfPreserving] at h
  rw [Monotone]
  intro a b a_le_b
  set s : Set α := {a, b} with hs -- or directly use {a, b} below
  specialize h s
  simp [hs] at h
  have : min a b = a := by grind
  rw [this] at h
  simp [Set.image] at h
  have : { x | f a = x ∨ f b = x } = { f a, f b } := by grind
  simp [this] at h
  exact h

/-!
TODO: clean-up all the #print that are not used above?
-/

/-!
TODO:
  - define the function f -> g (leftAdjoint),
  - show that only the left adjoint can be a solution,
  - show that the left adjoint preserves sup?
-/

theorem galois {α β}
    [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fip : sInfPreserving f) :
    ∃ (g : β → α),
    (∀ (a : α) (b : β), b ≤ f a ↔ g b ≤ a) := by
  let g (b : β) := sInf { a | b ≤ f a }
  use g
  intro a b
  simp only [g]
  constructor
  · intro hab
    apply sInf_le
    simp only [Set.mem_ofPred_eq]
    exact hab
  · intro h
    have h1 : f (sInf {a | b ≤ f a}) ≤ f a := by
      have fm := monotonic_of_sInfPreserving f fip
      apply fm
      exact h
    have h2 : sInf (f '' {a | b ≤ f a}) ≤ f a := by
      rw [fip {a | b ≤ f a}]
      exact h1
    simp [Set.image] at h2
    have h3 : b ≤ sInf {x | ∃ a, b ≤ f a ∧ f a = x} := by
      apply le_sInf
      simp only [Set.mem_ofPred_eq]
      intro c ⟨a, ha1, ha2⟩
      rw [ha2] at ha1
      assumption
    exact le_trans h3 h2

end Galois
