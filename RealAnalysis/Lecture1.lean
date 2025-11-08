/-
Alex Kontorovich: First Analysis Lecture
================================================================================

Source: https://www.youtube.com/watch?v=VY0WEUJMaXE
-/

import Mathlib

def seqLimIs (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n, n ≥ m -> |x n - ℓ| ≤ ε

#print seqLimIs
-- def seLimIs : (ℕ → ℝ) → ℝ → Prop :=
-- fun x ℓ => ∀ ε > 0, ∃ m, ∀ n ≥ m, |x n - ℓ| ≤ ε

/-
We could also adopt a very explicit variant of this definition where:

  - we add explicit types everywhere (even where Lean could
    guess them from the context),

  - we desugar what `∀ ε > 0, P ε` and `∀ n >= m, Q n` into
    `∀ ε, ε > 0 -> P ε` and `∀ n, n >= m -> Q n` and we
    indent the definition to make the propositions `P` and `Q`
    used in the theorem stand out more,

  - we desugar the absolute value notation `∣·∣` into `abs ·`.
-/

def seqLimIs' (x : ℕ -> ℝ) (ℓ : ℝ) :=
  ∀ (ε : ℝ), ε > 0 ->
    ∃ (m : ℕ),
      ∀ (n : ℕ), (n ≥ m) ->
        abs (x n - ℓ) ≤ ε

/-
For Lean, this new definition is obviously the same as the original:
-/

#print seqLimIs'
-- def seqLimIs' : (ℕ → ℝ) → ℝ → Prop :=
-- fun x ℓ => ∀ ε > 0, ∃ m, ∀ n ≥ m, |x n - ℓ| ≤ ε

/-
Since it is obvious, we can prove easily, "by definition" (`rfl` tactic):
-/

theorem seqLimIs_eq_seqLimIs' : seqLimIs = seqLimIs' := by rfl

/-
The absolute value is a beast, since it is defined with the utmost
generality, in every space which is a group and an lattice -- since
it is a place where the expression `sup a -a` makes sense.
-/

#print abs
-- def abs.{u_1} : {α : Type u_1} → [Lattice α] → [AddGroup α] → α → α :=
-- fun {α} [Lattice α] [AddGroup α] a => a ⊔ -a

/-
For the gory details, have a look at [Mathlib.Algebra.Order.Group.Abs]

[Mathlib.Algebra.Order.Group.Abs]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Abs.html#abs_eq
-/

/-
Unfolding all the definitions when dealing with proofs with abs
would be a mistake so we are merely going to use two lemmas that contain
all the info we need to know about abs and call it a day.
-/


#check abs_of_nonneg
-- abs_of_nonneg.{u_1} {α : Type u_1} [Lattice α] [AddGroup α] {a : α} [AddLeftMono α]
-- (h : 0 ≤ a) : |a| = a

#check abs_of_neg
-- abs_of_neg.{u_1} {α : Type u_1} [Lattice α] [AddGroup α] {a : α} [AddLeftMono α]
-- (h : a < 0) : |a| = -a

/-
Note that for these theorems to work, addition (on the left) needs to be monotonic:
b₁ <= b₂ -> a + b₁ <= a + b₂

The real numbers satisfy all that:
-/

#check (inferInstance : Lattice ℝ)
#check (inferInstance : AddGroup ℝ)
#check (inferInstance : AddLeftMono ℝ)

/-
Thus we can specialize these two results to our use case (not necessary,
but it could provide some peace of mind...):
-/

theorem Real.abs_of_nonneg {a : ℝ} (h : 0 <= a) : |a| = a :=
  _root_.abs_of_nonneg h

theorem Real.abs_of_neg {a : ℝ} (h : a < 0) : |a| = -a :=
  _root_.abs_of_neg h

/-
Q: Why are these two lemmas better than the "obvious" theorem below?
-/

theorem abs_eq_if_le_zero (x : ℝ) : abs x = if 0 <= x then x else -x := by
  split_ifs with h
  . simp
    exact h
  . simp
    apply le_of_not_ge
    exact h

/-
How deep do we want to go here? Deal manually with <= ? With = and simp?
Use linarith to solve all this trivially? Do all variants?
-/

theorem triangular_inequality (a b : ℝ): |a + b| ≤ |a| + |b| := by
  have h_a := Classical.em (0 <= a)
  have h_b := Classical.em (0 <= b)
  have h_ab := Classical.em (0 <= a + b)
  cases h_a with
  | inl h =>
    cases h_b with
    | inl h' =>
      rw [abs_of_nonneg h]
      rw [abs_of_nonneg h']
      have h'' := add_nonneg h h'
      rw [abs_of_nonneg h'']
    | inr h' =>
      rw [abs_of_nonneg h]
      simp at h'
      rw [abs_of_neg h']
      simp only [le_add_neg_iff_add_le]
      cases h_ab with
      | inl h'' =>
        rw [abs_of_nonneg h'']
        rw [add_assoc]
        nth_rewrite 2 [<- add_zero a]
        apply add_le_add
        . rfl
        . have b_nonneg : b <= 0 :=
            le_of_lt h'
          exact add_nonpos b_nonneg b_nonneg
      | inr h'' => admit
  | inr h =>
    cases h_b with
    | inl h' =>
      simp at h
      cases h_ab with
      | inl h'' =>
        rw [abs_of_neg h]
        rw [abs_of_nonneg h']
        rw [abs_of_nonneg h'']
        apply add_le_add
        . have a_nonneg : a <= 0 := le_of_lt h
          have zero_le_neg_a : 0 <= -a := neg_nonneg.mpr a_nonneg
          exact le_trans a_nonneg zero_le_neg_a
        . rfl
      | inr h'' => admit
    | inr h' =>
      simp at h h'
      rw [abs_of_neg h]
      rw [abs_of_neg h']
      have h'' := add_neg h h'
      rw [abs_of_neg h'']
      simp only [neg_add_rev, le_add_neg_iff_add_le, neg_add_cancel_comm, le_refl]

/-
Make a proof that leverages the direct triangular inequality.
-/

theorem reverse_triangular_inequality (a b : ℝ) :
  |(|a| - |b|)| <= |a - b| := by
  admit

theorem reverse_triangular_inequality' (a b : ℝ) :
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
seqLimIs x ℓ -> seqLimIs (fun n => |x n|) |ℓ| := by
  intro seqLimIs_x_ℓ
  rw [seqLimIs] at ⊢ seqLimIs_x_ℓ
  intro ε ε_pos
  have h := seqLimIs_x_ℓ ε ε_pos
  have ⟨m, h'⟩ := h
  clear h ε_pos seqLimIs_x_ℓ; have h := h'; clear h'
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
