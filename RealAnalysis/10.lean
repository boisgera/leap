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

def seq_lim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| < ε

def converges (a : ℕ → ℝ) := ∃ ℓ, seq_lim a ℓ

def eventual_upper_bound (a : ℕ → ℝ) (y : ℝ) := ∃ m, ∀ n ≥ m, a n ≤ y

theorem order_limit (a : ℕ → ℝ) (ℓ y : ℝ)
(limit : seq_lim a ℓ) (bound : eventual_upper_bound a y) : ℓ ≤ y := by
  by_contra y_lt_ℓ
  simp at y_lt_ℓ
  rw [seq_lim, eventual_upper_bound] at *
  let ⟨m₁, hm₁⟩ := bound
  specialize limit (ℓ - y) (by linarith)
  let ⟨m₂, hm₂⟩ := limit
  have h : ∀ n ≥ m₂, a n > y := by
    intro n n_ge_m₂
    have : ℓ - a n ≤ |a n - ℓ| := by
      simp only [abs_sub_comm]
      apply le_abs_self
    have : ℓ - a n < ℓ - y := by
      linarith [hm₂ n n_ge_m₂]
    simp only [sub_lt_sub_iff_left] at this
    exact this
  clear hm₂
  let n := max m₁ m₂
  specialize hm₁ n (show n ≥ m₁ by grind)
  specialize h n (show n ≥ m₂ by grind)
  linarith

def sub_seq (a b : ℕ → ℝ) :=
∃ (σ : ℕ → ℕ), (∀ (i j : ℕ), i < j → σ i < σ j) ∧ a = b ∘ σ

theorem subindex_growth
    (σ : ℕ → ℕ) :
    (∀ (i j : ℕ), i < j → σ i < σ j) -> ∀ n, σ n ≥ n := by
  intro inc n
  induction n with
  | zero => simp only [zero_le]
  | succ n ih =>
    have lt_succ : n < n + 1 := by grind
    specialize inc n (n + 1) lt_succ
    linarith

theorem sub_seq_lim
    (a b : ℕ → ℝ) (ss : sub_seq a b) (ℓ : ℝ) (lim : seq_lim b ℓ) :
    (seq_lim a ℓ) := by
  rw [seq_lim] at *
  intro ε ε_pos
  specialize lim ε ε_pos
  have ⟨m, hm⟩ := lim
  use m
  intro n n_ge_m
  rw [sub_seq] at ss
  have ⟨σ, σ_inc, abσ ⟩ := ss
  have σ_growth := subindex_growth σ σ_inc
  rw [abσ]
  rw [Function.comp]
  let n' := σ n
  have n'_ge_n : n' ≥ n := σ_growth n
  specialize hm n' (ge_trans n'_ge_n n_ge_m)
  simp [n'] at hm
  exact hm

example (b : ℕ → ℝ) (b_def : ∀ n, b n = (-1) ^ n) :
  ∃ (a : ℕ → ℝ), sub_seq a b ∧ converges a
    := by
  let a := fun (n : ℕ) => 1
  -- TODO
  admit
