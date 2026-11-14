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

theorem galois_1 {α β}
    [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : Monotone f) :
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
  · intro hab
    rw [sInf_le_iff, lowerBounds] at hab
    simp only [Set.mem_ofPred_eq] at hab
    -- apply hab
    sorry

theorem galois {α β}
    [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : Monotone f) :
    ∃ (g : β → α),
    (∀ (a : α) (b : β), b ≤ f a ↔ g b ≤ a) ∧
    Monotone g := by
  sorry

#check galois

end Galois
