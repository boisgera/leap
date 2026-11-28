
import Mathlib

namespace Galois

def sInfHom {α β} [CompleteLinearOrder α] [CompleteLinearOrder β] (f : α → β)
    : Prop :=
  ∀ (s : Set α), f (sInf s) = sInf (f '' s)

def leftAdjoint {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (y : β) : α := sInf {x | y ≤ f x}


#check sInf_le_iff
-- sInf_le_iff.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α} :
-- sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a

#print lowerBounds
-- def lowerBounds.{u_1} : {α : Type u_1} → [LE α] → Set α → Set α :=
-- fun {α} [LE α] s => {x | ∀ ⦃a : α⦄, a ∈ s → x ≤ a}

#check le_sInf_iff
-- le_sInf_iff.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α} :
-- a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b

lemma sInf_Ici {α} [CompleteLinearOrder α] (a : α) : sInf {x | a ≤ x} = a := by
  apply le_antisymm
  · rw [sInf_le_iff]
    rw [lowerBounds]
    simp only [Set.mem_ofPred_eq]
    intro b hb
    apply hb
    apply le_refl
  · rw [le_sInf_iff]
    intro a' ha'
    simp only [Set.mem_ofPred_eq] at ha'
    assumption

theorem monotone_of_sInfHom
    {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : sInfHom f) : Monotone f := by
  rw [Monotone]
  intro a b a_le_b
  rw [sInfHom] at *
  specialize fm {a, b}
  simp at fm
  have : min a b = a := by grind
  rw [this] at fm
  have : f '' {a, b} = {f a, f b} := by grind
  rw [this] at fm
  simp at fm
  assumption

theorem galois
    {α β} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (f : α → β) (fm : sInfHom f) (g : β → α) :
    (∀ (x : α), ∀ (y : β), y ≤ f x ↔ g y ≤ x)
    ↔
    g = leftAdjoint f := by
  apply Iff.intro
  · intro h
    ext y
    rw [leftAdjoint]
    have : sInf {x | g y ≤ x} = g y := sInf_Ici (g y)
    rw [<- this]
    have : {x | g y ≤ x} = {x | y ≤ f x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [<- h x y]
    have : sInf {x | g y ≤ x} = sInf {x | y ≤ f x} := by
      rw [this]
    exact this
  · intro g_eq
    rw [g_eq]
    intro x y
    rw [leftAdjoint]
    constructor
    · intro hxy
      rw [sInf_le_iff]
      rw [lowerBounds]
      simp only [Set.mem_ofPred_eq]
      intro a ha
      apply ha
      assumption
    · -- ⊢ sInf {x | y ≤ f x} ≤ x → y ≤ f x
      -- Nota: not used fm yet.
      intro hxy
      have : f (sInf {x | y ≤ f x}) ≤ f x := by
        apply monotone_of_sInfHom
        apply fm
        exact hxy
      rw [fm] at this
      rw [sInf_le_iff] at this
      simp [lowerBounds] at this
      specialize this y
      apply this
      intro a ha
      assumption


end Galois
