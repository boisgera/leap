import Mathlib

-- An inequality used to show that analytic function is differentiable:

lemma ineq (z h : ℂ) (h_neq_zero : h ≠ 0) (n : ℕ) (n_ge_two : n ≥ 2) :
‖((z + h) ^ n - z ^n) / h - n * z ^ (n - 1)‖ ≤
n * (n - 1) / 2 * (‖z‖ + ‖h‖) ^ (n - 2) * ‖h‖ := by
  admit -- Solvable by Aristotle
