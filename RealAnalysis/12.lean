import Mathlib

set_option pp.showLetValues true

def Lim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| < ε

def HasLim (a : ℕ → ℝ) := ∃ ℓ, Lim a ℓ

def IsCauchy (a : ℕ → ℝ) := ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| < ε

#print StrictMono
-- def StrictMono.{u, v} :
--     {α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] →
--     (α → β) → Prop :=
--   fun {α} {β} [Preorder α] [Preorder β] f =>
--     ∀ ⦃a b : α⦄, a < b → f a < f b

def IsSubSeq {α} (a b : ℕ → α) := ∃ (σ : ℕ → ℕ), StrictMono σ ∧ a = b ∘ σ

-- Function iterate: `f^[n]` stands for `f ∘ f ∘ ... ∘ f`,
-- with `n` occurences of `f`

#check Function.iterate_succ'
-- Function.iterate_succ'.{u} {α : Type u} (f : α → α) (n : ℕ) :
--     f^[n.succ] = f ∘ f^[n]

#check strictMono_of_lt_succ
-- strictMono_of_lt_succ.{u_3, u_4} {α : Type u_3} {β : Type u_4}
--     [PartialOrder α] [Preorder β] [SuccOrder α]
--     [IsSuccArchimedean α] {f : α → β}
--     (hf : ∀ (a : α), ¬IsMax a → f a < f (Order.succ a)) :
--     StrictMono f

/-
Our own version of this result, more restrictive but simpler since our indices
are in ℕ.
-/
lemma strictMono_of_lt_succ' {α} [p : Preorder α] (a : ℕ → α) :
    (∀ n, a n < a (n + 1)) -> StrictMono a := by
  intro h
  rw [StrictMono]
  intro m n m_lt_n
  let d := n - 1 - m
  rw [show n = m + 1 + d by grind] at *
  induction d with
  | zero =>
    apply h
  | succ p' ih =>
    apply lt_trans ih _
    apply h

theorem strictMono_of_superDiagonal (a : ℕ → ℕ) (h : ∀ n, a n > n) :
    ∃ b, IsSubSeq b a ∧ StrictMono b := by

  admit
