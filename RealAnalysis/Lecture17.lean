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

-- TODO: prove that ∑ 1 / (k + 1)^2 is convergent.
-- Steps:
--  1. study ∑ 1 / (k + 1)(k + 2), (partial sum and convergence)
--  2. Show that the original series is monotone and bounded
--     and thus converges (via Cauchy and completeness).
--
-- Nota: we have 1 / (k + 1)^2 ≤ 1 if k = 1 else ≤ 1 / k * (k + 1).
-- Unfortunately there is an index shift wrt the Leibniz series,
-- that's a small extra difficulty.

noncomputable def LeibnizSeries (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)), 1 / (k + 1) / (k + 2)

lemma Leibniz_term (k : ℕ) :
    (1 / (k + 1) / (k + 2) : ℝ) = 1 / (k + 1) - 1 / (k + 2) := by
  field_simp
  norm_num

lemma Leibniz_sum (n : ℕ) : LeibnizSeries n = (1 - 1 / (n + 2) : ℝ) := by
  rw [LeibnizSeries]
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    simp only [Nat.cast_zero, zero_add]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring_nf

#check Metric.tendsto_atTop
-- Metric.tendsto_atTop.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
--     Tendsto u atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

theorem LeibnizSeries_lim_eq_one : Tendsto LeibnizSeries atTop (nhds 1) := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]
  simp only [Leibniz_sum]
  -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |1 - 1 / (↑n + 2) - 1.0| < ε
  ring_nf
  simp only [gt_iff_lt, ge_iff_le, abs_neg, abs_inv]
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → |2 + ↑n|⁻¹ < ε
  field_simp
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → 1 < ε * |2 + ↑n|
  have h_pos (n : ℕ) : (2 + ↑n : ℝ) ≥ 0 := by positivity
  -- We enter in conv mode so that we don't have to unfold the predicate
  -- which would force us to select the N yet immediately. The proper
  -- choice of N will be clear once we have simplified the inner expression.
  -- The other (simpler?) solution: use `let N := sorry` and change afterwards.
  conv =>
    intro ε ε_pos
    right
    ext n
    intro N
    intro n_ne_N
    rw [abs_of_nonneg (h_pos N)]

  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ n, ∀ (N : ℕ), n ≤ N → 1 < ε * (2 + ↑N)
  intro ε ε_pos
  use ⌈1 / ε⌉₊ -- what we are actually interested in: ⌈1 / ε⌉₊ ≥ 1 / ε
  intro N
  -- ⊢ ⌈1 / ε⌉₊ ≤ N → 1 < ε * (2 + ↑N)
  intro N_ge_t
  have l1 : ↑N ≥ 1 / ε := Nat.ceil_le.mp N_ge_t
  have l2 : ε * (2 + ↑N) ≥ ε * (2 + (1 / ε)) := by nlinarith
  apply lt_of_lt_of_le _ l2
  -- ⊢ 1 < ε * (2 + 1 / ε)
  field_simp
  have : ε * 2 > 0 := by positivity
  linarith

noncomputable def sum_inv_squares (n : ℕ) : ℝ := ∑ k ∈ (Finset.range (n + 1)), 1 / (k + 1)^2

lemma strict_mono : StrictMono sum_inv_squares := by
  admit

lemma domination (n : ℕ) :
    (n = 0 → sum_inv_squares n ≤ 1) ∧
    (n > 1 → sum_inv_squares n ≤ 1 + LeibnizSeries (n - 1))
    := by
  -- TODO: induction on n
  admit

lemma domination' (n : ℕ) : sum_inv_squares n ≤ 2 - 1 / (n + 1) := by
  admit

-- TODO: uniform bound from domination' ∧ strict_mono -> Cauchy -> converges.

end Series

-- TODO: Manage infinite sums via
--     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html#tsum

-- Summation Filters:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.html
