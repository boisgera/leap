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

#check Finset.sum_nbij
-- Finset.sum_nbij.{u_1, u_2, u_3} {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [AddCommMonoid M] {s : Finset ι}
--   {t : Finset κ} {f : ι → M} {g : κ → M} (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : Set.InjOn i ↑s)
--   (i_surj : Set.SurjOn i ↑s ↑t) (h : ∀ a ∈ s, f a = g (i a)) : ∑ x ∈ s, f x = ∑ x ∈ t, g x

#check mem_nhds_iff
-- mem_nhds_iff.{u} {X : Type u} [TopologicalSpace X] {x : X} {s : Set X} : s ∈ nhds x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t

-- OK, now I'd like to tackle the proof of:
def TO_PROVE.reordering (f : ℕ → ℝ) (ℓ : ℝ) (i : ℕ → ℕ) {_ : Function.Bijective i} : Prop :=
  (HasSum f ℓ ↔ HasSum (f ∘ i) ℓ)

-- Out of nowhere, I'd think that it could be useful to characterize `HasSum f ℓ`
-- by the elementary statement below. After that, it's "just" a matter of
-- performing the suitable change of variables in finite sums
-- to prove the reordering theorem.

theorem hasSum_iff (f : ℕ → ℝ) (ℓ : ℝ) : -- 🚧 TODO!
    HasSum f ℓ ↔
    ∀ ε > 0, ∃ (s : Finset ℕ),
      |∑ k ∈ s, f k - ℓ| < ε ∧
      ∀ t : Finset ℕ, Disjoint t s → |∑ k ∈ t, f k| < ε  := by admit

#check Filter.mem_atTop
-- Filter.mem_atTop.{u_3} {α : Type u_3} [Preorder α] (a : α) :
--     {b | a ≤ b} ∈ Filter.atTop

#print Filter.atTop
-- def Filter.atTop.{u_3} : {α : Type u_3} → [Preorder α] → Filter α :=
-- fun {α} [Preorder α] => ⨅ a, Filter.principal (Set.Ici a)

#check Filter.mem_iInf
-- Filter.mem_iInf.{u, u_2} {α : Type u} {ι : Type u_2} {s : ι → Filter α} {U : Set α} :
--  U ∈ ⨅ i, s i ↔ ∃ I, I.Finite ∧ ∃ V, (∀ (i : ↑I), V i ∈ s ↑i) ∧ U = ⋂ i, V i

#check Filter.mem_atTop_sets
-- Filter.mem_atTop_sets.{u_3} {α : Type u_3} [Preorder α] [IsDirectedOrder α] [Nonempty α] {s : Set α} :
--  s ∈ Filter.atTop ↔ ∃ a, ∀ b ≥ a, b ∈ s

#check Finset.sum_nbij
-- Finset.sum_nbij.{u_1, u_2, u_3} {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [AddCommMonoid M]
--   {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}
--   (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : Set.InjOn i ↑s)
--   (i_surj : Set.SurjOn i ↑s ↑t)
--   (h : ∀ a ∈ s, f a = g (i a)) : ∑ x ∈ s, f x = ∑ x ∈ t, g x

lemma reordering_lemma (f : ℕ → ℝ) (ℓ : ℝ) (i : ℕ → ℕ) (bij : Function.Bijective i) :
    HasSum f ℓ → HasSum (f ∘ i) ℓ := by
  simp only [HasSum, Filter.Tendsto, Filter.le_def, Filter.mem_map]
  simp only [SummationFilter.unconditional]
  -- ⊢ (∀ x ∈ nhds ℓ, (fun s => ∑ b ∈ s, f b) ⁻¹' x ∈ Filter.atTop) ↔
  -- ∀ x ∈ nhds ℓ, (fun s => ∑ b ∈ s, (f ∘ i) b) ⁻¹' x ∈ Filter.atTop
  -- Nota : Filter.atTop, as a Filter on `Finset ℕ`, is interesting :
  -- Filter.atTop is ⨅ a, Filter.principal (Set.Ici a)
  -- it's the coarsest filter that contains the all [s, +∞) for all
  -- finite sets s.
  -- The lattice structure on filter is based on the "min" (inf) of two filters
  -- generated by intersections of sets among those filters,
  -- and "max" (sup) of two filters, which contains sets that belong to both
  -- filters.
  -- The corresponding order is l₁ ≤ l₂ iff l₁ is finer than l₂ (i.e. l₂ ⊆ l₁).
  -- So Filter.principal (Set.Ici a) is the collection of finite sets that
  -- contain the finite set a and ⨅ a, Filter.principal (Set.Ici a) is
  -- the (coarsest) filter generated by the finite intersections among those
  -- filters.
  -- TODO: have a more detailled look at Filter.mem_iInf
  simp only [Filter.mem_atTop_sets]
  simp only [Set.mem_preimage]
  -- simp only [Function.comp_apply]
  -- ⊢ (∀ x ∈ nhds ℓ, ∃ a, ∀ b ≥ a, ∑ b ∈ b, f b ∈ x) ↔
  --   ∀ x ∈ nhds ℓ, ∃ a, ∀ b ≥ a, ∑ x ∈ b, f (i x) ∈ x
  --
  -- TODO : use Finset.sum_nbij to turn `∑ x ∈ b, (f ∘ i) x` into
  -- `∑ y ∈ (Finset.image i b), f y` (here `i`) is a bijection.
  have change_of_variables (b : Finset ℕ) :
      ∑ x ∈ b, (f ∘ i) x = ∑ y ∈ (Finset.image i b), f y := by
    exact Finset.sum_nbij (f := f ∘ i) (g := f)
      i
      (show ∀ a ∈ b, i a ∈ Finset.image i b from by
        simp only [Finset.mem_image]
        intro a a_in_b
        use a
      )
      (show Set.InjOn i b from by
        apply bij.injective.injOn
      )
      (show Set.SurjOn i b (Finset.image i b) from by
        simp only [Set.SurjOn]
        simp only [Finset.coe_image, Set.image_subset_iff]
        intro x x_in_b
        simp only [Set.mem_preimage, Set.mem_image]
        use x
      )
      (show ∀ a ∈ b, (f ∘ i) a = f (i a) from by
        intro a _
        apply Function.comp_apply
      )
  simp only [change_of_variables]
  intro h x x_in_nhds_ℓ
  let ⟨a, ha⟩ := h x x_in_nhds_ℓ
  have i_inj : Set.InjOn i (i ⁻¹' a) := bij.injective.injOn
  use Finset.preimage a i i_inj
  have image_ge_of_preimage_ge (b : Finset ℕ) : b ≥ a.preimage i i_inj -> b.image i ≥ a := by
    intro h x x_in_a
    have : i.invFun x ∈ a.preimage i i_inj := by
      simp only [Finset.mem_preimage]
      simp only [i.invFun_eq (bij.surjective x)]
      exact x_in_a
    specialize h this
    simp only [Finset.mem_image]
    use Function.invFun i x
    constructor
    exact h
    simp only [i.invFun_eq (bij.surjective x)]
  intro b b_ge_preimage_a
  specialize image_ge_of_preimage_ge b b_ge_preimage_a
  specialize ha (Finset.image i b) image_ge_of_preimage_ge
  exact ha

theorem reordering (f : ℕ → ℝ) (ℓ : ℝ) (i : ℕ → ℕ) (bij : Function.Bijective i) :
    HasSum f ℓ ↔ HasSum (f ∘ i) ℓ := by
  constructor
  . apply reordering_lemma
    assumption
  . have : (f ∘ i) ∘ i.invFun = f := by
      simp only [Function.comp_assoc]
      ext x
      simp only [Function.comp, Function.rightInverse_invFun bij.2 x]
    nth_rw 2 [<- this]
    apply reordering_lemma
    constructor
    . exact (Function.rightInverse_invFun bij.2).injective
    . exact (Function.leftInverse_invFun bij.1).surjective
