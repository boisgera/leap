import Mathlib

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

theorem lim_of_sums (a b : ℕ -> ℝ) {ℓ₁ ℓ₂ : ℝ}:
SeqLim a ℓ₁ -> SeqLim b ℓ₂ -> SeqLim (a + b) (ℓ₁ + ℓ₂) := by
  repeat rw [SeqLim]
  intro ha hb ε ε_pos
  let ε₂ := ε / 2
  have ε₂_pos : ε₂ > 0 := by simp_rw[ε₂] ; linarith [ε_pos]
  specialize ha ε₂ ε₂_pos
  specialize hb ε₂ ε₂_pos
  have ⟨N₁, hN₁⟩ := ha
  have ⟨N₂, hN₂⟩ := hb
  clear ha hb
  let N := max N₁ N₂
  have N₁_le_N : N₁ <= N := by apply le_max_left
  have N₂_le_N : N₂ <= N := by apply le_max_right
  use N
  intro n hn
  specialize hN₁ n (show N₁ <= n from le_trans N₁_le_N hn)
  specialize hN₂ n (show N₂ <= n from le_trans N₂_le_N hn)
  have h₁ : (a + b) n = a n + b n := by rfl
  have h₂ : |(a + b) n - (ℓ₁ + ℓ₂)| = |(a n - ℓ₁) + (b n - ℓ₂)| := by
    rw [h₁]
    ring_nf
  have h₃ : |(a + b) n - (ℓ₁ + ℓ₂)| <= |a n - ℓ₁| + |b n - ℓ₂| := by
    rw [h₂]
    apply abs_add_le
  have h₄: |a n - ℓ₁| + |b n - ℓ₂| < ε₂ + ε₂ := by
    apply add_lt_add hN₁ hN₂
  have h₅ : |a n - ℓ₁| + |b n - ℓ₂| < ε := by
    simp_rw [ε₂] at h₄
    simp only [add_halves] at h₄
    exact h₄
  exact lt_of_le_of_lt h₃ h₅
