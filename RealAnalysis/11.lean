import Mathlib

set_option pp.showLetValues true

def seq_lim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| < ε

def converges (a : ℕ → ℝ) := ∃ ℓ, seq_lim a ℓ

def is_cauchy (a : ℕ → ℝ) := ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| < ε

theorem converges_of_is_cauchy {a : ℕ → ℝ} : converges a -> is_cauchy a := by
  simp_rw [converges, seq_lim, is_cauchy]
  intro ⟨ℓ, hℓ⟩ ε ε_pos
  specialize hℓ (ε / 2) (show ε / 2 > 0 by linarith)
  let ⟨m, hm⟩ := hℓ
  use m
  intro n n_ge_m p p_ge_m
  let hn := hm n n_ge_m
  let hp := hm p p_ge_m
  calc |a n - a p|
    _ = |(a n - ℓ) - (a p - ℓ)| := by ring_nf
    _ ≤ |a n - ℓ| + |a p - ℓ| := by apply abs_sub
    _ < ε := by linarith

theorem sum_of_cauchy {a b : ℕ → ℝ} :
    is_cauchy a -> is_cauchy b -> is_cauchy (a + b) := by
  simp only [is_cauchy]
  intro ha hb ε ε_pos
  specialize ha (ε / 2) (by linarith)
  specialize hb (ε / 2) (by linarith)
  obtain ⟨ma, ha⟩ := ha
  obtain ⟨mb, hb⟩ := hb
  let m := max ma mb
  use m
  intro n n_ge_m p p_ge_m
  simp only [Pi.add_apply]
  specialize ha n (by grind) p (by grind)
  specialize hb n (by grind) p (by grind)
  calc |a n + b n - (a p + b p)|
    _ = |(a n - a p) + (b n - b p)| := by ring_nf
    _ ≤ |a n - a p| + |b n - b p|   := by apply abs_add_le
    _ < ε                           := by linarith

def is_bounded (a : ℕ → ℝ) := ∃ x, ∀ n, |a n| ≤ x


#check abs_add_le


-- Could be split into finite -> bounded and cauchy -> eventually bounded.
theorem bounded_of_cauchy {a : ℕ → ℝ} : is_cauchy a → is_bounded a := by
  have aux (m : ℕ) : ∃ b, ∀ n < m, |a n| ≤ b := by
    induction m with
    | zero =>
      use 0; grind
    | succ m ih =>
      let ⟨b, ihb⟩ := ih
      let b' := max b |a m|
      use b'
      intro n n_lt_succ_m
      by_cases h : n < m
      . specialize ihb n h
        apply le_trans ihb (show b ≤ b' by grind)
      . have : n = m := by linarith
        rw [this]; grind
  rw [is_cauchy, is_bounded]
  intro hcauchy
  specialize hcauchy 1 (by linarith)
  obtain ⟨m, hm⟩ := hcauchy
  have aux' : ∀ n ≥ m, |a n| <= |a m| + 1 := by
    intro n n_ge_m
    specialize hm n n_ge_m m (by grind)
    calc |a n|
      _ = |a m + (a n - a m)| := by ring_nf
      _ ≤ |a m| + |a n - a m| := by apply abs_add_le
      _ ≤ |a m| + 1           := by linarith
  let ⟨b, hb⟩ := aux m
  let x := max b (|a m| + 1)
  use x
  intro n
  by_cases h : n < m
  . specialize hb n h
    apply le_trans hb (show b ≤ x by grind)
  . simp only [not_lt] at h
    specialize aux' n h
    apply le_trans aux' (show |a m| + 1 ≤ x by grind)
