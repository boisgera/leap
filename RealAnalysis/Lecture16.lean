import Mathlib

-- TODO: explore the fact that in ℝ, Cauchy sequences converge.

-- TODO: show that for real-valued sequences, the standard `CauchySeq` and
--       our simple `IsCauchy` are equivalent. Do the same for limits and
--       deduce a simple, concrete version of "ℝ is complete".

/-!
⚠️ Many new definitions to consider!
-/

#print CauchySeq
-- def CauchySeq.{u, v} : {α : Type u} → {β : Type v} →
-- [uniformSpace : UniformSpace α] → [Preorder β] → (β → α) → Prop :=
-- fun {α} {β} [UniformSpace α] [Preorder β] u => Cauchy (Filter.map u Filter.atTop)

#check Preorder -- ≤ which is reflexive and transitive; for us: ℕ
-- Preorder.{u_2} (α : Type u_2) : Type u_2

#check UniformSpace -- Here for us: ℝ
-- Think of it as something a bit weaker than "metric space";
-- the mere "topological space" is not enough to define Cauchy filter.
-- This is actually a topological space with a "uniform structure" with four
-- additional axioms.
-- UniformSpace.{u} (α : Type u) : Type u

/-!
What `CauchySeq a` captures when `a : ℕ → ℝ` is that "some filter based on a
is Cauchy". Need to investigate:
  - what is a filter,
  - what is this filter,
  - what is a Cauchy filter.
-/

#print Filter
-- structure Filter.{u_1} (α : Type u_1) : Type u_1
-- number of parameters: 1
-- fields:
--   Filter.sets : Set (Set α)
--   Filter.univ_sets : Set.univ ∈ self.sets
--   Filter.sets_of_superset : ∀ {x y : Set α}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
--   Filter.inter_sets : ∀ {x y : Set α}, x ∈ self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
-- constructor:
--   Filter.mk.{u_1} {α : Type u_1} (sets : Set (Set α)) (univ_sets : Set.univ ∈ sets)
--     (sets_of_superset : ∀ {x y : Set α}, x ∈ sets → x ⊆ y → y ∈ sets)
--     (inter_sets : ∀ {x y : Set α}, x ∈ sets → y ∈ sets → x ∩ y ∈ sets) : Filter α

#print Filter.atTop -- "neighborhood" of "+∞" I guess?
-- def Filter.atTop.{u_3} : {α : Type u_3} → [Preorder α] → Filter α :=
-- fun {α} [Preorder α] => ⨅ a, Filter.principal (Set.Ici a)

-- Note that filters instantiate ⊓ (inf) via `Filter.instInfSet`

#check Filter.instInfSet
-- Filter.instInfSet.{u_1} {α : Type u_1} : InfSet (Filter α)

#print Set.Ici -- "Interval closed-infinity: Ici" (I guess)
-- def Set.Ici.{u_1} : {α : Type u_1} → [Preorder α] → α → Set α :=
-- fun {α} [Preorder α] a => {x | a ≤ x}

#print Filter.principal
-- def Filter.principal.{u_1} : {α : Type u_1} → Set α → Filter α :=
-- fun {α} s => {
--   sets := {t | s ⊆ t},
--   univ_sets := ⋯,
--   sets_of_superset := ⋯,
--   inter_sets := ⋯
-- }

/-!
OK, at this stage the definition of `CauchySeq` (partiallu) makes sense:
a sequence is Cauchy if the image of the "neighbourhood of +∞" by the sequence
is a Cauchy filter. But the definition of a Cauchy filter (in a uniform space)
is a bitch. Consider:
-/

#print Cauchy
-- def Cauchy.{u} : {α : Type u} → [uniformSpace : UniformSpace α] → Filter α → Prop :=
-- fun {α} [UniformSpace α] f => f.NeBot ∧ f ×ˢ f ≤ uniformity α
