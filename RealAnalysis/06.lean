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

#check abs_le

example: ∀ {a : ℕ -> ℝ}, ∀ {ℓ : ℝ},
SeqLim a ℓ -> ∃ N, ∀ n ≥ N, a n ≥ ℓ - 1:= by
  intro a ℓ seqlim_a_ℓ
  rw [SeqLim] at seqlim_a_ℓ
  specialize seqlim_a_ℓ 1 (show 1 > 0 from by linarith)
  have ⟨N, hN⟩ := seqlim_a_ℓ
  clear seqlim_a_ℓ
  use N
  intro n n_ge_N
  specialize hN n n_ge_N
  have hN' := le_of_lt hN; clear hN
  have := (abs_le.mp hN').left
  linarith


theorem squeeze (a b c : ℕ -> ℝ) (ℓ : ℝ) :
a <= b -> b <= c -> SeqLim a ℓ -> SeqLim c ℓ -> SeqLim b ℓ := by
  intro hab hbc seqlim_a_ℓ seqlim_b_ℓ
  rw [SeqLim] at *
  intro ε ε_pos
  specialize seqlim_a_ℓ ε ε_pos
  specialize seqlim_b_ℓ ε ε_pos
  have ⟨Na, ha⟩ := seqlim_a_ℓ
  have ⟨Nb, hb⟩ := seqlim_b_ℓ
  clear seqlim_a_ℓ seqlim_b_ℓ
  let N := max Na Nb
  have ma :  Na <= N := by grind
  have mb : Nb <= N := by grind
  use N
  intro n n_ge_N
  specialize ha n (show n >= Na from le_trans ma n_ge_N)
  specialize hb n (show n >= Nb from le_trans mb n_ge_N)
  rw [abs_lt] at *
  have ha' := ha.left; clear ha
  have hb' := hb.right; clear hb
  have ha'' : ℓ - ε < a n := by linarith
  have hb'' : c n < ℓ + ε := by linarith
  specialize hab n
  specialize hbc n
  constructor
  . linarith
  . linarith
