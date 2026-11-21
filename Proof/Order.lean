import Mathlib


#print SemilatticeInf -- A PartialOrder already.

def f {α} [SemilatticeInf α] (a b : α) : α := a ⊓ b

example {α} [SemilatticeInf α] : Min α := inferInstance

/-!
`LinearOrder`:

  - gets `le_refl` and `le_trans` from `Preorder`,

  - gets `le_antisymm` from `PartialOrder`,

  - add `le_total` on its own.

-/
#print LinearOrder

namespace Sandbox

def sInfHom
    {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β) : Prop :=
  ∀ (s : Set α), f (sInf s) = sInf (f '' s)

theorem image_top_eq_top {α β} [CompleteLinearOrder α]  [CompleteLinearOrder β]
    (f : α → β) (fm : sInfHom f) : f ⊤  = ⊤ := by
  rw [sInfHom] at fm
  specialize fm ∅
  simp_rw [sInf_empty, Set.image_empty, sInf_empty] at fm
  exact fm

#print Monotone
-- def Monotone.{u, v} : {α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] → (α → β) → Prop :=
-- fun {α} {β} [Preorder α] [Preorder β] f => ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

#check sInf_pair

#check min_def

#print Preorder

theorem monotone_of_sInfHom {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : sInfHom f) : Monotone f := by
  rw [Monotone]
  intro a b a_le_b
  have h1 : f (sInf {a, b}) = sInf (f '' {a, b}) :=
    fm {a, b}
  have h2: sInf {a, b} = a := by
    simp only [sInf_insert, sInf_singleton, inf_eq_left]
    exact a_le_b
  have h3 : f '' {a, b} = {f a, f b} := by
    simp_rw [Set.image]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq, true_and]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  rw [h2] at h1
  rw [h3] at h1
  rw [sInf_pair] at h1
  rw [min_def] at h1
  simp at h1
  by_contra h
  push Not at h
  specialize h1 h
  rw [Preorder.lt_iff_le_not_ge] at h
  have h4 := h.2
  have h5 : f a ≤ f b := by
    rw [h1]
  exact h4 h5

end Sandbox
