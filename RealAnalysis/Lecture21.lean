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
    |x - x_0| < δ -> |f x - f x_0| < δ * (δ + 2 * |x_0|) := by
  simp only [f_factorization]
  intro h
  simp only [abs_mul]
  have hadd : |x - x_0 + 2 * x_0| ≤ |x - x_0| + 2 * |x_0| := by
    have := abs_add_le (x - x_0) (2 * x_0)
    simp only [abs_mul, abs_two] at this
    linarith
  have hsq : |x - x_0| ^ 2 < δ ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg (x - x_0)]) h
  nlinarith [
    abs_nonneg (x - x_0),
    abs_nonneg x_0,
    mul_nonneg (abs_nonneg (x - x_0)) (abs_nonneg (x - x_0 + 2 * x_0))
  ]

theorem continuousAt_everywhere (x : ℝ) : ContinuousAt f x := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]
  intro ε ε_pos
  let δ := min 1 (ε / (1 + 2 * |x|))
  use δ
  constructor
  positivity
  intro x_1
  have dom := f_diff_domination x_1 x δ (by positivity)
  intro h
  specialize dom h
  have ineq : δ * (δ + 2 * |x|) ≤ ε := by
    have : δ * (δ + 2 * |x|) ≤ ε / (1 + 2 * |x|) * (1 + 2 * |x|) := by
      apply mul_le_mul
      . apply min_le_right
      . linarith [show δ ≤ 1 from by apply min_le_left]
      . positivity
      . positivity
    simp only [div_mul_cancel₀ ε (show (1 + 2 * |x|) ≠ 0 from by grind)] at this
    exact this
  linarith

#check continuous_iff_continuousAt
-- continuous_iff_continuousAt.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
-- [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} :
-- Continuous f ↔ ∀ (x : X), ContinuousAt f x

theorem continuous : Continuous f :=
  continuous_iff_continuousAt.mpr continuousAt_everywhere


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
