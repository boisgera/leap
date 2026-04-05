import Mathlib

/-!
TODO:
- Compute the derivative of x ↦ x ^ 2 - 1 at 2
- Show that x ↦ 2 * x is the derivative of x ↦ x ^ 2 - 1
- Show that x ↦ x ^ 2 - 1 is continuous at each point and thus continuous
-
-/

def f (x : ℝ) : ℝ := x ^ 2 - 1

namespace Ex_0

/-!
TODO: show that x ↦ x ^ 2 - 1 is continuous (everywhere)
-/

#check Metric.continuousAt_iff
-- Metric.continuousAt_iff.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [PseudoMetricSpace β]
--      {f : α → β} {a : α} :
--   ContinuousAt f a ↔
--   ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) (f a) < ε

lemma f_factorization (x x_0 : ℝ) :
    f x - f x_0 = (x - x_0) * ((x - x_0) + 2 * x_0) := by
  simp only [f]
  ring_nf

lemma f_diff_domination (x x_0 δ : ℝ) (δ_pos : δ > 0) :
    |x - x_0| ≤ δ -> |f x - f x_0| ≤ δ * (δ + 2 * |x_0|) := by
  simp only [f_factorization]
  intro h
  simp only [abs_mul]
  have hadd : |x - x_0 + 2 * x_0| ≤ |x - x_0| + |2 * x_0| :=
    abs_add_le _ _
  have hprod : |x - x_0| * |x - x_0 + 2 * x_0| ≤ |x - x_0| ^ 2 + |x - x_0| * (|2| * |x_0|) := by
    have := abs_add_le (x - x_0) (2 * x_0)
    simp only [abs_mul] at this
    nlinarith [abs_nonneg (x - x_0), abs_nonneg (x - x_0 + 2 * x_0)]
  have hsq : |x - x_0| ^ 2 ≤ δ ^ 2 := by nlinarith [abs_nonneg (x - x_0)]
  have hmix : |x - x_0| * (|2| * |x_0|) ≤ δ * (|2| * |x_0|) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h2 : |2| = (2 : ℝ) := by norm_num
  rw [h2] at hprod hmix
  nlinarith

theorem continuousAt_everywhere (x : ℝ) : ContinuousAt f x := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]
  intro ε ε_pos
  let δ := min 1 ε / (1 + 2 * |x|)
  have : δ > 0 := by positivity
  have : δ ≤ 1 := by grind
  have : δ ≤ ε / (1 + 2 * |x|) := by grind
  use δ
  admit

end Ex_0

namespace Ex_1

/-!
TODO: Compute the derivative of f at x = 2
-/

end Ex_1

namespace Ex_2

/-!
TODO: Compute the derivative function of f
-/

end Ex_2
