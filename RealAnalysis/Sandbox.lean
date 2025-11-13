import Mathlib

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

#check one_div_lt
-- one_div_lt.{u_2} {α : Type u_2} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
-- {a b : α} (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a

example : SeqLim (fun n => 1 / 2 ^ n) 0 := by
  rw [SeqLim]
  intro ε ε_pos
  simp only [sub_zero]
  simp only [one_div]
  simp only [abs_inv]
  simp only [abs_pow]
  simp only [Nat.abs_ofNat]
  simp only [<- one_div]
  -- ε : ℝ
  -- ε_pos : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, 1 / 2 ^ n < ε
  let N : ℕ := sorry
  use N
  intro n n_ge_N
  have n_pow_2_pos: (2 ^ n : ℝ) > 0 := by
    simp only [Nat.ofNat_pos, pow_pos]
  rw [one_div_lt n_pow_2_pos ε_pos]
  -- TODO: do stuff with logpow base 2
  -- make obvious what N should be, update that sorry
  -- conclude
  admit



lemma lemma₁ : ∀ ε > 0, 1 / ((Nat.ceil (1 / ε)) + 1) < ε := by
  admit

example {a : ℕ → ℝ} (ha: ∀ (n : ℕ), a n = 1 / ↑n) : SeqLim a 0 := by
  rw [SeqLim]
  intro ε ε_pos
  let N := (Nat.ceil (1 / ε)) + 1
  use N
  intro n n_ge_N
  simp
  have h1 : (n : ℝ) >= 1 := by
    admit
  have h2 : (a n) > 0 := by
    admit
  rw [abs_of_pos]
  rw [ha]
  -- TODO ...
  admit
