import Mathlib

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

#check mul_lt_mul_of_pos_left

theorem double_lim (a : ℕ -> ℝ) (ℓ : ℝ) :
SeqLim a ℓ -> SeqLim (fun n => 2 * a n) (2 * ℓ) := by
  repeat rw [SeqLim]
  intro h ε ε_pos
  let ε₂ := ε / 2
  have ε₂_pos : ε₂ > 0 := by simp_rw [ε₂]; linarith
  specialize h ε₂ ε₂_pos
  have ⟨N, hN⟩ := h; clear h
  use N
  intro n n_ge_N
  specialize hN n n_ge_N
  have e : |2 * a n - 2 * ℓ| = 2 * |a n - ℓ| := by
    calc |2 * a n - 2 * ℓ|
        = |2 * (a n - ℓ)| := by ring_nf
      _ = |2| * |a n - ℓ| := abs_mul 2 (a n - ℓ)
      _ = 2  * |a n - ℓ|  := by norm_num
  rw [e]
  have hN' := mul_lt_mul_of_pos_left hN (show 0 < 2 from by grind)
  simp_rw [ε₂] at hN'
  have s : (2 * |a n - ℓ| < 2 * (ε / 2)) = (2 * |a n - ℓ| < ε) := by
    conv =>
      lhs
      rhs
      ring_nf
  rw [s] at hN'
  exact hN'
