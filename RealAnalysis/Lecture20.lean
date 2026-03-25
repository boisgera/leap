import Mathlib

-- Infinite Sums: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html
-- SummationFilter: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.html#SummationFilter.unconditional

#check Summable
-- Summable.{u_1, u_2} {α : Type u_1} {β : Type u_2} [AddCommMonoid α] [TopologicalSpace α]
-- (f : β → α)
-- (L : SummationFilter β := SummationFilter.unconditional β) : Prop

#check tsum
-- tsum.{u_4, u_5} {α : Type u_4} {β : Type u_5} [AddCommMonoid α] [TopologicalSpace α] (f : β → α)
-- (L : SummationFilter β := SummationFilter.unconditional β) : α

-- - `tsum` may have to choose among several sums.
-- - `tsum` returns 0 when the function is not summable
-- - the notation for `tsum` is `∑' i, f i` when `L` is the
--   default, unconditional filter, or `∑'[L] i, f i` generally.

-- HasSum combines "being summable" and "with sum a":

#check HasSum
-- HasSum.{u_1, u_2} {α : Type u_1} {β : Type u_2} [AddCommMonoid α] [TopologicalSpace α]
-- (f : β → α) (a : α)
-- (L : SummationFilter β := SummationFilter.unconditional β) : Prop

-- A summation filter on `β` is (wraps) a filter on `Finset β`
#print SummationFilter
-- structure SummationFilter.{u_4} (β : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   SummationFilter.filter : Filter (Finset β)
-- constructor:
--   SummationFilter.mk.{u_4} {β : Type u_4} (filter : Filter (Finset β)) : SummationFilter β

-- The unconditional filter is the largest filter (wrt ⊆) among such
-- filters: every finite subset is in the filter.
#print SummationFilter.unconditional
-- def SummationFilter.unconditional.{u_2} : (β : Type u_2) → SummationFilter β :=
-- fun β => { filter := Filter.atTop }

-- Is HasSum a mere wrapper around Tendsto? Yes! Ah, OK, so that clears up
-- things a bit :)
#print HasSum
-- def HasSum.{u_1, u_2} : {α : Type u_1} →
--   {β : Type u_2} →
--     [AddCommMonoid α] →
--       [TopologicalSpace α] → (β → α) → α → optParam (SummationFilter β) (SummationFilter.unconditional β) → Prop :=
-- fun {α} {β} [AddCommMonoid α] [TopologicalSpace α] f a L => Filter.Tendsto (fun s => ∑ b ∈ s, f b) L.filter (nhds a)

-- Now, I expect `Summable` to be a simple existential wrapper around that?
-- And indeed, that works!
#print Summable
-- def Summable.{u_1, u_2} : {α : Type u_1} →
--   {β : Type u_2} →
--     [AddCommMonoid α] →
--       [TopologicalSpace α] → (β → α) → optParam (SummationFilter β) (SummationFilter.unconditional β) → Prop :=
-- fun {α} {β} [AddCommMonoid α] [TopologicalSpace α] f L => ∃ a, HasSum f a L

-- And now I guess that `tsum` is basically using Su
#print tsum
-- Garbage ...

-- The source of tsum is actually a mechanical translation from the prod version
-- It reads basically:
-- - if the function is not summable, return 0
-- - otherwise,
--   - if the support is finite, do the finite sum,
--   - else if 0 is an acceptable value, return 0
--   - otherwise, choose among the available sums.

-- OK, so basically at this stage, there are a lot of convenience constructions
-- but not a lot of really new tools. I can get away with very little if I
-- use directly the notation for sums over finite sets, Tendsto and the "top"
-- filter on Finset ℕ directly. That's good to know!

-- -----------------------------------------------------------------------------

-- Reminder of what's useful about Filter.Tendsto:

-- First, the definition:
#print Filter.Tendsto
-- def Filter.Tendsto.{u_1, u_2} : {α : Type u_1} → {β : Type u_2} →
-- (α → β) → Filter α → Filter β → Prop :=
-- fun {α} {β} f l₁ l₂ => Filter.map f l₁ ≤ l₂

-- OK, so that's `Filter.map` which is "two-levels" above the image of an
-- element by a function (or one level above): the collection of sets
-- in Filter.map f l₁ is Set.preimage f ⁻¹' l₁.sets (ouch).

-- So the low-level, operational stuff about Filter.Tendsto would be:

def TT.{u_1, u_2} {α : Type u_1} {β : Type u_2}
    (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
        Filter.Tendsto f l₁ l₂ ↔ ∀ t ∈ l₂, ∃ s ∈ l₁, f '' s ⊆ t

-- Actually what already exists is a slightly higher-level version based on preimage:
#check Filter.tendsto_def
-- Filter.tendsto_def.{u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
-- Filter.Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁

theorem tendsto_def_alt.{u_1, u_2} {α : Type u_1} {β : Type u_2}
    (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    (Filter.Tendsto f l₁ l₂) ↔ ∀ t ∈ l₂, ∃ s ∈ l₁, f '' s ⊆ t := by
  rw [Filter.tendsto_def]
  constructor
  . intro h t t_in_l₂
    specialize h t t_in_l₂
    use f ⁻¹' t
    constructor
    . exact h
    . -- ⊢ f '' (f ⁻¹' t) ⊆ t
      apply Set.image_preimage_subset
  . intro h s s_in_l₂
    have ⟨s_1, s_1_in_l₁, k⟩ := h s s_in_l₂
    have k' := Set.preimage_mono (f := f) k
    have k'' := Set.subset_preimage_image f s_1
    have := subset_trans k'' k'
    exact l₁.sets_of_superset s_1_in_l₁ this


#print Filter.map

namespace Ex_00


theorem sum_zeros : Filter.Tendsto
    (fun (s : Finset ℕ) => (∑ _ ∈ s, 0 : ℝ))
    Filter.atTop
    (nhds 0) := by
  rw [Filter.tendsto_def]
  intro t t_in_nhds_zero
  have zero_in_t := mem_of_mem_nhds t_in_nhds_zero
  simp only [Finset.sum_const_zero]
  have : (fun s => 0) ⁻¹' t = Set.univ (α := Finset ℕ) := by
    ext x
    constructor
    . grind
    . intro _
      rw [Set.mem_preimage]
      exact zero_in_t
  rw [this]
  exact Filter.atTop.univ_sets



end Ex_00

-- -----------------------------------------------------------------------------

-- Q: what is the equivalent of Cauchyness for summability?

-- TODO: prove that :
-- - absolute convergence -> summability
-- - summability -> convergence
-- - summability -> convergence of any reordering
