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


#check sInf
-- InfSet.sInf.{u_1} {α : Type u_1} [self : InfSet α] : Set α → α

example {α : Type*} [CompleteLinearOrder α] : InfSet α := inferInstance

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


theorem galois {α β}
    [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : Monotone f) :
    ∃ (g : β → α),
    (∀ (a : α) (b : β), b ≤ f a ↔ g b ≤ a) ∧
    Monotone g := by
  sorry

#check galois
