/-
Source: https://www.youtube.com/watch?v=VY0WEUJMaXE
-/
import Mathlib

def has_limit' (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ (ε : ℝ), ε > 0 ->
  ∃ (m : ℕ), ∀ (n : ℕ), (n ≥ m) ->
  abs (x n - ℓ) ≤ ε

#print has_limit'

def has_limit (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n, n ≥ m -> |x n - ℓ| ≤ ε

#print has_limit

theorem has_limit_eq_has_limit' : has_limit = has_limit' := by
  rfl

theorem limit_abs (x : ℕ -> ℝ) (ℓ : ℝ) :
has_limit x ℓ -> has_limit (fun n => |x n|) |ℓ| := by
  intro has_limit_x_ℓ
  rw [has_limit] at ⊢ has_limit_x_ℓ
  intro ε ε_pos
  have h := has_limit_x_ℓ ε ε_pos
  have ⟨m, h'⟩ := h
  clear h ε_pos has_limit_x_ℓ; have h := h'; clear h'
  use m
  intro n n_geq_m
  have h := h n n_geq_m
  have h' := abs_abs_sub_abs_le_abs_sub (x n) ℓ
  have h'' := le_trans h' h
  exact h''

#check abs_abs_sub_abs_le_abs_sub -- reverse triangular inequality
#check le_trans
