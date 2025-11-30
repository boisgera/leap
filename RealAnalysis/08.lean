import Mathlib

example : ∀ n, 1 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      simp [pow_add, pow_one]
      linarith

example : ∀ n : ℕ, n < 2 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_add, pow_one]
    linarith

example : ∀ n : ℕ, n < 2 ^ n := by
  intro n
  induction' n with n ih
  . norm_num
  . rw [pow_add, pow_one]
    linarith
