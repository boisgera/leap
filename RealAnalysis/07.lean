import Mathlib
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic

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

theorem lim_abs (a b : ℕ -> ℝ) (ℓ : ℝ) :
  SeqLim a ℓ -> (∀ n, b n = |a n|) ->
  SeqLim b |ℓ| := by
  repeat rw [SeqLim] at *
  intro seq_lim_a_ℓ b_eq_abs_a ε ε_pos
  specialize seq_lim_a_ℓ ε ε_pos
  have ⟨N, hN⟩ := seq_lim_a_ℓ; clear seq_lim_a_ℓ
  use N
  intro n n_ge_N
  specialize hN n n_ge_N
  specialize b_eq_abs_a n
  rw [b_eq_abs_a]
  apply lt_of_le_of_lt _ hN
  exact abs_abs_sub_abs_le_abs_sub (a n) ℓ

#check sq_pos_iff


-- Note: this result depends on `eventually_greater_than_half_the_limit`.
-- Note: given how / is defined, implictly we have defined
--       b n to be zero when a n = 0.
theorem lim_inv (a b : ℕ -> ℝ) (ℓ : ℝ) :
  SeqLim a ℓ -> ℓ ≠ 0 -> (∀ n, b n = 1 / (a n)) ->
  SeqLim b (1 / ℓ) := by
  repeat rw [SeqLim]
  intro seq_lim_a_ℓ ℓ_nonzero b_eq_inv_a ε ε_pos
  -- we need to make sure that ε' is small enough to ensure that a n != 0
  -- nooooo ! If we want to use eventually_greater_than_half_the_limit,
  -- we'll drop the min and play with max on n instead.
  let ε' := ε * ℓ ^ 2 / 2
  have sq_ℓ_pos: ℓ ^ 2 > 0 := sq_pos_iff.mpr ℓ_nonzero
  have ε'_pos : ε' > 0 := by
    simp only [ε']
    have : ε * ℓ ^ 2 > 0 := mul_pos ε_pos sq_ℓ_pos
    linarith

  have ⟨N₁, hN₁⟩ := eventually_greater_than_half_the_limit a ℓ seq_lim_a_ℓ ℓ_nonzero
  specialize seq_lim_a_ℓ ε' ε'_pos
  have ⟨N₂, hN₂⟩ := seq_lim_a_ℓ; clear seq_lim_a_ℓ
  let N := max N₁ N₂
  use N
  intro n n_ge_N
  rw [b_eq_inv_a]
  specialize hN₂ n (show n ≥ N₂ from by grind)
  have a_n_ge_half_abs_ell : |a n| >= |ℓ| / 2 :=
    hN₁ n (show n ≥ N₁ from by grind)
  have abs_ell_pos : |ℓ| > 0 := by simp_all
  have a_n_ne_zero : a n ≠ 0 := by
    have : |ℓ| / 2 > 0 := by linarith
    have abs_a_n_ne_zero : |a n| > 0 := by linarith
    simp_all
  have lemma₁ : (1 / a n - 1 / ℓ) = (ℓ - a n) / ((a n) * ℓ) := by
    field_simp
  rw [lemma₁]
  have lemma₂ : |(ℓ - a n) / (a n * ℓ)| <= |ℓ - a n| / (ℓ ^ 2 / 2) := by
    calc |(ℓ - a n) / (a n * ℓ)|
      _ = |ℓ - a n| / |a n * ℓ| := by simp only [abs_div]
      _ = |ℓ - a n| / (|a n| * |ℓ|) := by simp only [abs_mul]
      _ = |ℓ - a n| / |ℓ| / |a n| := by field_simp
      _ ≤ |ℓ - a n| / |ℓ| / (|ℓ| / 2) := by
        apply div_le_div_of_nonneg_left
          (show 0 <= |ℓ - a n| / |ℓ| from by
            apply div_nonneg; apply abs_nonneg; apply abs_nonneg)
          (show 0 < |ℓ| / 2 from by linarith)
          (show |ℓ| / 2 <= |a n| from a_n_ge_half_abs_ell)
      _ = |ℓ - a n| / (|ℓ| ^ 2 / 2) := by field_simp
      _ = |ℓ - a n| / (ℓ ^ 2 / 2) := by simp only [sq_abs]
  have lemma₃ : |ℓ - a n| / (ℓ ^ 2 / 2) < ε := by
    apply (div_lt_iff₀ (
      show ℓ ^ 2 / 2 > 0 by
        have : ℓ ^ 2 > 0 := by
          exact sq_pos_iff.mpr ℓ_nonzero
        linarith
    )).mpr
    rw [<- abs_neg]
    ring_nf
    rw [add_comm, <- sub_eq_add_neg]
    simp [ε'] at hN₂
    field_simp at hN₂ ⊢
    exact hN₂
  exact lt_of_le_of_lt lemma₂ lemma₃
