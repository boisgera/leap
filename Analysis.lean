/-
Source: https://www.youtube.com/watch?v=VY0WEUJMaXE
-/
import Mathlib

def has_limit' (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ (ε : ℝ), ε > 0 ->
  ∃ (m : ℕ), ∀ (n : ℕ), (n ≥ m) ->
  abs (x n - ℓ) ≤ ε

#print has_limit'
-- def has_limit' : (ℕ → ℝ) → ℝ → Prop :=
-- fun x ℓ => ∀ ε > 0, ∃ m, ∀ n ≥ m, |x n - ℓ| ≤ ε

def has_limit (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n, n ≥ m -> |x n - ℓ| ≤ ε

#print has_limit
-- def has_limit' : (ℕ → ℝ) → ℝ → Prop :=
-- fun x ℓ => ∀ ε > 0, ∃ m, ∀ n ≥ m, |x n - ℓ| ≤ ε

theorem has_limit_eq_has_limit' : has_limit = has_limit' := by
  rfl

#synth (SemilatticeSup ℝ) -- Real.instSemilatticeSup

#check Real.instSemilatticeSup.2
-- SemilatticeSup.sup : ℝ → ℝ → ℝ

#check Real.lattice.toSemilatticeSup.2
-- SemilatticeSup.sup : ℝ → ℝ → ℝ

-- #print Real.lattice.toSemilatticeSup.2


theorem abs_eq_if_le_zero (x : ℝ) : abs x = if 0 <= x then x else -x := by
  split_ifs with h
  . simp
    exact h
  . simp
    apply le_of_not_ge
    exact h

theorem reverse_triangular_inequality (a b : ℝ) :
  |(|a| - |b|)| <= |a - b| := by
  repeat rw [abs_eq_if_le_zero]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  . rfl
  . rfl
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith
  . linarith


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
-- abs_abs_sub_abs_le_abs_sub.{u_1} {G : Type u_1} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b : G) :
--   ||a| - |b|| ≤ |a - b|

#check le_trans
-- le_trans.{u_1} {α : Type u_1} [Preorder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c
