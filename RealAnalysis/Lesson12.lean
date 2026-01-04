 import Mathlib

set_option pp.showLetValues true

/-
The final goal in this chapter: to prove that we if P(n) holds for infinitely
many n, we may exhibit an increasing sequence of n where it holds.
-/

#check Classical.choose
-- Classical.choose.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α

#check Classical.choose_spec
-- Classical.choose_spec.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (Classical.choose h)


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

/-
If we want to use the Mathlib version instead to derive this result, we can:
-/

lemma strictMono_of_lt_succ'' {α} [p : Preorder α] (a : ℕ → α) :
    (∀ n, a n < a (n + 1)) -> StrictMono a := by
  intro h
  apply strictMono_of_lt_succ
  intro a_1 not_isMax -- not_isMax not used here
  specialize h a_1
  assumption

/-
By the way, in ℕ we have automatically:
-/

lemma not_IsMax (n : ℕ) : ¬IsMax n := by
  rw [IsMax]
  intro h
  specialize h (b := n + 1)
  specialize h (by grind only)
  linarith

/-
TODO: improve the name of this theorem and the one after
-/
theorem strictMono_and_p_holds_aux (p : ℕ → Prop) :
    (∀ n, ∃ m > n, p m) ->
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ (∀ i, p (ns i)) := by
  intro h
  choose ns_aux ns_aux_h using h
  /-
  Why we would to define `ns` recursively with `let rec`,
  but then we could not use `simp [ns]`: we would get the error:

      Invalid argument: Variable `ns` is not a proposition or let-declaration

  Apparently, you cannot unfold a `let rec`
  (see https://github.com/leanprover/lean4/issues/7878#issuecomment-2804166875)
  -/
  -- let rec ns (i : ℕ) : ℕ :=
  --   match i with
  --   | 0 => ns_aux 0
  --   | i + 1 => ns_aux (ns i)
  /-
  So instead, we do the same thing with a recursor:
  -/
  let ns : ℕ → ℕ := Nat.rec
    (ns_aux 0)
    (fun i prev => ns_aux prev)

  have lemma_1 : ∀ (i : ℕ), ns i < ns (i + 1) := by
    simp only [ns]
    intro i
    match i with
    | 0 =>
      simp only [Nat.rec_zero]
      apply (ns_aux_h _).1
    | j + 1 =>
      simp only
      apply (ns_aux_h _).1
  have lemma_2 : ∀ (i : ℕ), p (ns i) := by
    intro i
    simp only [ns]
    match i with
    | 0 =>
      simp only [Nat.rec_zero]
      exact (ns_aux_h 0).2
    | j + 1 =>
      simp only
      exact (ns_aux_h _).2
  use ns
  constructor
  . apply strictMono_of_lt_succ'
    apply lemma_1
  . apply lemma_2

theorem choice_sequence (p : ℕ → Prop) :
    (∀ n, ∃ m ≥ n, p m) ->
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ (∀ i, p (ns i)) := by
  intro h
  have h_aux : ∀ n, ∃ m > n, p m := by
    intro n
    specialize h (n + 1)
    grind
  apply strictMono_and_p_holds_aux p h_aux

example (p : ℕ → Prop):
    (∀ n, ∃ m ≥ n, p m) ->
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ i, p (ns i) := by
  intro h
  let ns : Nat → Nat :=
    Nat.rec (Classical.choose (h 0)) (fun n ih => Classical.choose (h ih))
  admit -- TODO

#print Nat.rec

#print StrictMono
-- def StrictMono.{u, v} :
--     {α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] →
--     (α → β) → Prop :=
--   fun {α} {β} [Preorder α] [Preorder β] f =>
--     ∀ ⦃a b : α⦄, a < b → f a < f b

def SubSeq {α} (a b : ℕ → α) := ∃ (σ : ℕ → ℕ), StrictMono σ ∧ a = b ∘ σ

-- Function iterate: `f^[n]` stands for `f ∘ f ∘ ... ∘ f`,
-- with `n` occurences of `f`

#check Function.iterate_succ'
-- Function.iterate_succ'.{u} {α : Type u} (f : α → α) (n : ℕ) :
--     f^[n.succ] = f ∘ f^[n]




lemma strictMono_of_lt_succ''' {α} [p : Preorder α] (a : ℕ → α) :
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
    ∃ b, SubSeq b a ∧ StrictMono b := by
  let b := fun n => a^[n] (a 0)
  use b
  constructor
  . admit
  . admit


def SeqLim (a : ℕ -> ℝ) (ℓ : ℝ) : Prop := ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| < ε

def Converges (a : ℕ → ℝ) := ∃ ℓ, SeqLim a ℓ

def IsCauchy (a : ℕ → ℝ) := ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| < ε
