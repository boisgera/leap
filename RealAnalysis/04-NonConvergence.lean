import Mathlib

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

def is_convergent (a : ℕ -> ℝ) : Prop :=
  ∃ (ℓ : ℝ), SeqLim a ℓ

def alt (n : ℕ) : ℝ := (-1) ^ n

theorem a_not_convergent: ¬is_convergent alt := by
  intro h
  rw [is_convergent] at h
  simp_rw [SeqLim] at h
  simp_rw [alt] at h
  have ⟨ℓ, p⟩ := h
  clear h
  specialize p (1/2 : ℝ)  -- Arf, 1 would have been good enough, reconsider the proof!
  have : (1/2 : ℝ) > 0 := by grind
  specialize p this
  have ⟨N, p'⟩ := p
  clear p
  let n₁ := 2 * N
  let n₂ := 2 * N + 1
  have h₁ : n₁ >= N := by grind
  have h₂ : n₂ >= N := by grind
  have p₁ := p' n₁ h₁
  have p₂ := p' n₂ h₂
  clear p' h₁ h₂ this
  simp_rw [n₁] at p₁
  simp_rw [n₂] at p₂
  simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_div] at p₁
  have : (-1 : ℝ) ^ (2 * N + 1) = -1 := by
    ring_nf
    simp only [even_two, Even.mul_left, Even.neg_pow, one_pow]
  simp_rw [this] at p₂
  simp only [one_div] at p₂
  clear this N n₁ n₂
  have : |-1 - ℓ| = |1 + ℓ| := by
    rw [show -1 - ℓ = -(ℓ + 1) by ring]
    rw [abs_neg]
    ring_nf
  rw [this] at p₂
  have t₁ : 2 <= |1 - ℓ| + |1 + ℓ| := by
    have l : |(1 - ℓ) + (1 + ℓ)| <= |1 - ℓ| + |1 + ℓ| :=
      abs_add_le (1 - ℓ) (1 + ℓ)
    simp at l
    norm_num at l
    exact l
  have t₂ : |1 - ℓ| + |1 + ℓ| < 1 := by
    have := add_lt_add p₁ p₂
    grind
  have t₂ := le_of_lt t₂
  have t₃ := le_trans t₁ t₂
  grind
