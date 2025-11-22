import Mathlib

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

#check abs_sub_le
#check abs_neg

lemma lemma₁ {x : ℝ} : 0 ≤ x -> (∀ ε > 0, x < ε) -> x = 0 := by
  intro x_non_neg
  contrapose
  intro x_non_zero
  have x_pos : x > 0 := by grind
  push_neg
  use x / 2
  constructor <;> linarith

theorem limit_is_unique (a : ℕ -> ℝ) (ℓ₁ ℓ₂ : ℝ) :
SeqLim a ℓ₁ -> SeqLim a ℓ₂ -> ℓ₁ = ℓ₂ := by
  repeat rw [SeqLim]
  intro h₁ h₂
  have h₃ : ∀ ε > 0, |ℓ₁ - ℓ₂| < ε := by
    intro ε ε_pos
    have half_ε_pos : ε / 2 > 0 := by
      linarith
    specialize h₁ (ε / 2) half_ε_pos
    specialize h₂ (ε / 2) half_ε_pos
    have ⟨N₁, h₁'⟩ := h₁
    clear h₁
    have ⟨N₂, h₂'⟩ := h₂
    clear h₂
    let n := max N₁ N₂
    specialize h₁' n (show n >= N₁ from by grind)
    specialize h₂' n (show n >= N₂ from by grind)
    have diff_lt_ε : |ℓ₁ - ℓ₂| < ε := by
      calc |ℓ₁ - ℓ₂|
          = |(a n - ℓ₂) - (a n - ℓ₁)| := by ring_nf
        _ ≤ |(a n - ℓ₂) - 0| + |0 - (a n - ℓ₁)| := abs_sub_le (a n - ℓ₂) 0 (a n - ℓ₁)
        _ = |a n - ℓ₂| + |-(a n - ℓ₁)| := by ring_nf
        _ = |a n - ℓ₂| + |a n - ℓ₁| := by rw [abs_neg]
        _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_lt h₂' h₁'
        _ = ε := by ring_nf
    exact diff_lt_ε
  have : |ℓ₁ - ℓ₂| = 0 :=
    lemma₁ (show |ℓ₁ - ℓ₂| >= 0 from abs_nonneg (ℓ₁ - ℓ₂)) h₃
  exact eq_of_abs_sub_eq_zero this

#check abs_sub_abs_le_abs_sub
#check abs_neg

theorem eventually_greater_than_half_the_limit (a : ℕ -> ℝ) (ℓ : ℝ):
  SeqLim a ℓ -> ℓ ≠ 0 ->
  ∃ N : ℕ, ∀ n : ℕ, n >= N -> |a n| >= |ℓ| / 2 := by
  intro seq_lim_a_ℓ ℓ_nonzero
  rw [SeqLim] at seq_lim_a_ℓ
  have half_abs_ℓ_pos: |ℓ| / 2 > 0 := by
    have : |ℓ| > 0 := abs_pos.mpr ℓ_nonzero
    linarith
  specialize seq_lim_a_ℓ (|ℓ| / 2) half_abs_ℓ_pos
  have ⟨N, hN⟩ := seq_lim_a_ℓ; clear seq_lim_a_ℓ
  use N
  intro n n_ge_N
  specialize hN n n_ge_N
  have hN' : |ℓ - a n| < |ℓ| / 2 := by
    calc |ℓ - a n|
      _ = |-(a n - ℓ)| := by ring_nf
      _ = |a n - ℓ| := by rw [abs_neg]
      _ < |ℓ| / 2 := hN
  have : |ℓ| - |a n| <= |ℓ - a n| :=
    abs_sub_abs_le_abs_sub ℓ (a n)
  have : |ℓ| - |a n| < |ℓ| / 2 :=
    lt_of_le_of_lt this hN'
  have : |ℓ| - |a n| <= |ℓ| / 2 := le_of_lt this
  linarith
