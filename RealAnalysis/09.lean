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


example (a : ℕ → ℝ) (N : ℕ) : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
  admit -- TODO!

-- An inequality used to show that analytic function is differentiable?

lemma ineq (z h : ℂ) (h_neq_zero : h ≠ 0) (n : ℕ) (n_ge_two : n ≥ 2) :
‖((z + h) ^ n - z ^n) / h - n * z ^ (n - 1)‖ ≤
n * (n - 1) / 2 * (‖z‖ + ‖h‖) ^ (n - 2) * ‖h‖ := by
  admit
