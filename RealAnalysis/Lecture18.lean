import Mathlib

open Filter

theorem t1 (a : ℕ → ℝ) :
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), |a k|) atTop (nhds ℓ)) →
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ)) := by
  admit

theorem t2 (a : ℕ → ℝ) :
    Tendsto a atTop (nhds 0) → Antitone a →
    ∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ) := by
  admit
