import Mathlib

-- import Mathlib.Data.Complex.Abs
-- open Complex

open Finset

#print Finset
-- structure Finset.{u_4} (α : Type u_4) : Type u_4
-- number of parameters: 1
-- fields:
--   Finset.val : Multiset α
--   Finset.nodup : self.val.Nodup
-- constructor:
--   Finset.mk.{u_4} {α : Type u_4} (val : Multiset α) (nodup : val.Nodup) : Finset α

#print Finset.sum
-- protected def Finset.sum.{u_1, u_3} :
-- {ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M :=
-- fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum

#print Multiset.sum
-- def Multiset.sum.{u_3} : {M : Type u_3} → [AddCommMonoid M] → Multiset M → M :=
-- fun {M} [AddCommMonoid M] => Multiset.foldr (fun x1 x2 => x1 + x2) 0

#print Multiset.foldr
-- def Multiset.foldr.{v, u_1} : {α : Type u_1} →
--   {β : Type v} → (f : α → β → β) → [LeftCommutative f] → β → Multiset α → β :=
-- fun {α} {β} f [LeftCommutative f] b s => Quot.liftOn s (fun l => List.foldr f b l) ⋯

#print Multiset
-- def Multiset.{u} : Type u → Type u :=
-- fun α => Quotient (List.isSetoid α)

#print List.isSetoid
-- def List.isSetoid.{u_1} : (α : Type u_1) → Setoid (List α) :=
-- fun α => { r := List.Perm, iseqv := ⋯ }

#check Finset.sum_union
-- Finset.sum_union.{u_1, u_4}
-- {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [AddCommMonoid M] {f : ι → M}
-- [DecidableEq ι] (h : Disjoint s₁ s₂) :
-- ∑ x ∈ s₁ ∪ s₂, f x = ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x


example : ∀ n, ∑ _ ∈ range n, 1 = n := by
  intro n
  induction n with
  | zero =>
    rw [range_zero, sum_empty]
  | succ n ih =>
    have aux : Disjoint (range n) {n} := by
      rw [disjoint_singleton_right]
      rw [mem_range]
      linarith
    have main :
      ∑ _ ∈ range n ∪ {n}, 1 = ∑ _ ∈ range n, 1 + ∑ _ ∈ {n}, 1 :=
      sum_union (f := fun _ => 1) aux
    have aux : (range n) ∪ {n} = range (n + 1) := by
      rw [range_add_one, union_singleton]
    rw [aux] at main
    have aux : ∀ (n : ℕ), ∑ _ ∈ {n}, 1 = 1 := by
      intro i ; rw [sum_singleton]
    rw [aux] at main
    rw [ih] at main
    exact main

lemma Finset.disjoint_range_singleton (n : ℕ) : Disjoint (range n) {n} := by
    rw [disjoint_singleton_right]
    rw [mem_range]
    linarith

example : ∀ (z : ℂ), z ≠ 1 -> ∀ (n : ℕ),
∑ i ∈ range n, z ^ i = (1 - z ^ n) / (1 - z) := by
  intro z z_ne_1 n
  induction n with
  | zero =>
    simp only [range_zero, sum_empty, pow_zero, sub_self, zero_div]
  | succ n ih =>
    rw [range_add_one]
    rw [<- union_singleton]
    rw [sum_union (h := disjoint_range_singleton n)]
    rw [ih]
    rw [sum_singleton]
    field_simp [show 1 - z ≠ 0 from by grind]
    ring

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
∑ k ∈ range (n + 1), a k = (∑ k ∈ range n, a k) + a n := by
  rw [range_add_one]
  rw [<- union_singleton]
  rw [sum_union (h := disjoint_range_singleton n)]
  rw [sum_singleton]


example (a : ℕ → ℝ) (N : ℕ) : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
  intro n n_le_N
  induction N with
  | zero =>
    simp at n_le_N
  | succ N ih =>
    rw [sum_range_succ]
    by_cases h : n < N
    . specialize ih h
      have ineg : ∑ k ∈ range N, |a k| ≤ ∑ k ∈ range N, |a k| + |a N| := by
        apply (le_add_iff_nonneg_right _).mpr
        apply abs_nonneg
      exact le_trans ih ineg
    . have aux₁ : N ≤ n := by grind
      have aux₂ : n ≤ N := by grind
      have n_eq_N : n = N := by grind
      rw [n_eq_N]
      apply (le_add_iff_nonneg_left _).mpr
      apply sum_nonneg
      intro i i_in_range_N
      simp only [mem_range] at i_in_range_N
      apply abs_nonneg

def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - ℓ| < ε

def converges (a : ℕ → ℝ) := ∃ ℓ, SeqLim a ℓ

theorem every_converging_sequence_is_bounded
(a : ℕ → ℝ) (converges_a : converges a) :
∃ M, ∀ n, |a n| ≤ M := by
  have ⟨ℓ, h⟩ := converges_a
  clear converges_a
  specialize h 1 (show 1 > 0 from by norm_num)
  have ⟨N, h'⟩ := h
  clear h
  have aux (N : ℕ) : ∃ b, ∀ n ∈ range N, |a n| ≤ b := by
    by_cases N_zero? : N = 0
    . simp
      use 1
      intro n n_lt_N
      simp [N_zero?] at n_lt_N
    . let abs_vals : Finset ℝ := range N |>.image fun n => |a n|
      have nonempty : abs_vals.Nonempty := by
        sorry -- 🚧 TODO
      let b := abs_vals.max' nonempty
      use b
      simp [b, abs_vals]
      sorry -- 🚧 TODO
  have h'' : ∀ n ≥ N, |a n| <= |ℓ| + 1 := by
    intro n n_ge_N
    specialize h' n n_ge_N
    calc |a n|
      _ = |ℓ + (a n - ℓ)| := by ring_nf
      _ ≤ |ℓ| + |a n - ℓ| := by apply abs_add_le
      _ ≤ |ℓ| + 1 := by linarith
  have ⟨b, hb⟩ := aux N; clear aux
  let M := max b (|ℓ| + 1)
  use M
  intro n
  by_cases n_lt_N? : n < N
  . simp at n_lt_N?
    simp [mem_range] at hb
    specialize hb n n_lt_N?
    have aux : b ≤ M := by grind
    linarith
  . simp at n_lt_N?
    specialize h'' n n_lt_N?
    have aux : |ℓ| + 1 <= M := by grind
    linarith

-- An inequality used to show that analytic function is differentiable:

lemma ineq (z h : ℂ) (h_neq_zero : h ≠ 0) (n : ℕ) (n_ge_two : n ≥ 2) :
‖((z + h) ^ n - z ^n) / h - n * z ^ (n - 1)‖ ≤
n * (n - 1) / 2 * (‖z‖ + ‖h‖) ^ (n - 2) * ‖h‖ := by
  admit
