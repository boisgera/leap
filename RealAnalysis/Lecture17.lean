import Mathlib
open Filter

set_option pp.showLetValues true

namespace Series

#check Finset.sum
-- Finset.sum.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M]
-- (s : Finset ι) (f : ι → M) : M

def partial_sum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)), a k -- notation for Finset.sum Finset.range a


noncomputable def a₁ (n : ℕ) : ℝ := 1 / 2 ^ (n + 1)

-- 1 / 2 + 1 / 4 + ... + 1 / 2 ^ k = 1 - 2 ^ k
theorem partial_sum_a₁_eq : partial_sum a₁ = fun n => 1 - 1 / 2 ^ (n + 1) := by
  ext n
  simp only [partial_sum, a₁]
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf

#check Tendsto
-- Filter.Tendsto.{u_1, u_2} {α : Type u_1} {β : Type u_2}
--     (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop

#check Metric.tendsto_atTop
-- Metric.tendsto_atTop.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [Nonempty β] [SemilatticeSup β]
--     {u : β → α} {a : α} :
--     Tendsto u atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

example : Tendsto (partial_sum a₁) atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  rw [partial_sum_a₁_eq]
  simp only
  simp only [Real.dist_eq]
  norm_num
  intro ε ε_pos
  have : StrictMono fun n => (2 ^ (n  + 1) : ℝ)⁻¹ := by
    admit
  let N := max 0 ⌈Real.logb 2.0 ε⌉
  have : (2 ^ (N + 1))⁻¹ < ε := by
    admit
  admit

end Series

-- TODO: Manange infinite sums via
--     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html#tsum

-- Summation Filters:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.html
