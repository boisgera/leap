import Mathlib

open Filter

#check Finset.sum_Ico_eq_sub
-- Finset.sum_Ico_eq_sub.{u_4} {δ : Type u_4} [AddCommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
--   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k - ∑ k ∈ Finset.range m, f k

theorem convergence_of_absolute_convergence (a : ℕ → ℝ) :
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), |a k|) atTop (nhds ℓ)) →
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ)) := by
  -- 1. get the Cauchyness of (|a ·|) from its convergence
  -- 2. transform it into the elementary version
  -- 3. deduce the Cauchyness of a from this (elementary version)
  -- 4. lift that into the abstract version
  -- 5. deduce the convergence of a
  --
  rintro ⟨lim_abs_a, conv_abs_sum_a⟩
  let cauchy_abs_sum_a := conv_abs_sum_a.cauchySeq
  simp only [Metric.cauchySeq_iff', Real.dist_eq] at cauchy_abs_sum_a
  -- cauchy_abs_sum_a : ∀ ε > 0, ∃ N, ∀ n ≥ N,
  --     |∑ k ∈ Finset.range (n + 1), |a k| - ∑ k ∈ Finset.range (N + 1), |a k|| < ε

  have cauchy_sum_a' : -- prov thet a is Cauchy, elementary flavor (step 3.)
      ∀ ε > 0, ∃ m, ∀ n ≥ m,
      |∑ k ∈ Finset.range (n + 1), a k - ∑ k ∈ Finset.range (m + 1), a k| < ε := by
    intro ε ε_pos
    let ⟨m, hm⟩ := cauchy_abs_sum_a ε ε_pos
    use m
    intro n n_ge_m
    specialize hm n n_ge_m
    simp [<- Finset.sum_Ico_eq_sub (|a ·|) (show m + 1 ≤ n + 1 from by linarith)] at hm
    -- hm : |∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|| < ε
    calc |∑ k ∈ Finset.range (n + 1), a k - ∑ k ∈ Finset.range (m + 1), a k|
      _ = |(∑ k ∈ Finset.Ico (m + 1) (n + 1), a k)| := by
        simp [Finset.sum_Ico_eq_sub a (show m + 1 ≤ n + 1 from by linarith)]
      _ ≤ (∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|) := by apply Finset.abs_sum_le_sum_abs
      _ ≤ |(∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|)| := by grind
      _ < ε := by exact hm

  have cauchy_sum_a : CauchySeq fun n => ∑ k ∈ Finset.range (n + 1), a k := by
    simp_rw [<- Real.dist_eq] at cauchy_sum_a'
    rw [<- Metric.cauchySeq_iff'] at cauchy_sum_a'
    exact cauchy_sum_a'

  apply cauchySeq_tendsto_of_complete

  admit

theorem t2 (a : ℕ → ℝ) :
    Tendsto a atTop (nhds 0) → Antitone a →
    ∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (-1)^k * (a k)) atTop (nhds ℓ) := by
  admit
