import Mathlib

example (n : ℕ) : ∃ k, n * (n + 1) * (2 * n + 1) = 6 * k := by
  induction n with
  | zero => use 0
  | succ n ih =>
    ring_nf at ih ⊢
    let ⟨k, hk⟩ := ih
    use k + n ^ 2 + 2 * n + 1
    ring_nf
    rw [<- hk]
    ring_nf

def seq_lim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

def converges (a : ℕ → ℝ) := ∃ ℓ, seq_lim a ℓ

def eventual_upper_bound (a : ℕ → ℝ) (y : ℝ) := ∃ n, ∀ m ≥ n, a m ≤ y

theorem order_limit (a : ℕ → ℝ) (ℓ y : ℝ)
(sl : seq_lim a ℓ) (bound : eventual_upper_bound a y) : ℓ ≤ y := by
  -- TODO!!! (by contradiction?)
  by_contra y_lt_ℓ
  simp at y_lt_ℓ
  rw [seq_lim, eventual_upper_bound] at *
  admit
