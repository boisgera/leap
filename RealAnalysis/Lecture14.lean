import Mathlib
import RealAnalysis.Lesson13

#print IsCauchy
-- def IsCauchy : (ℕ → ℝ) → Prop :=
--   fun a => ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| < ε

def BolzanoWeierstrass (a : ℕ → ℝ) :
    ∃ M > 0, ∀ n, |a n| ≤ M -> ∃ b, SubSeq b a ∧ IsCauchy b := by
  admit

#check strictMono_or_antitone_subsequence
-- strictMono_or_antitone_subsequence (a : ℕ → ℝ) :
--     ∃ b, SubSeq b a ∧ (StrictMono b ∨ Antitone b)

#check lt_trichotomy
-- lt_trichotomy.{u_1} {α : Type u_1} [LinearOrder α] (a b : α) :
--     a < b ∨ a = b ∨ b < a

lemma Monotone.isCauchy_iff {a : ℕ → ℝ} (monotone_a : Monotone a) :
    IsCauchy a ↔ ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p > n, a p - a n < ε := by
  apply Iff.intro
  . intro isCauchy
    rw [IsCauchy] at isCauchy
    intro ε ε_pos
    let ⟨m, hm⟩ := isCauchy ε ε_pos
    use m
    intro n n_ge_m p p_gt_n
    specialize hm n n_ge_m p (show p ≥ m from by omega)
    have : a p ≥ a n := by apply monotone_a ; grind
    have : |a n - a p| = a p - a n := by grind
    rw [this] at hm
    exact hm
  . intro h
    rw [IsCauchy]
    intro ε ε_pos
    specialize h ε ε_pos
    have ⟨m, hm⟩ := h
    use m
    intro n n_ge_m p p_ge_m
    rcases lt_trichotomy n p with n_lt_p | n_eq_p | p_lt_n
    · specialize hm n n_ge_m p n_lt_p
      rw [Monotone] at monotone_a
      specialize monotone_a (show n ≤ p from by omega)
      grind
    · grind
    · specialize hm p p_ge_m n p_lt_n
      rw [Monotone] at monotone_a
      specialize monotone_a (show p ≤ n from by omega)
      grind

-- TODO: get rid of ε > 0? (ε ≥ 0 is a csq of the existence)?
-- Encapsulate that in a subtype?
def is_approximate_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [NoMinOrder α]
    (a : ℕ → α) (ε : α) (_ε_pos : ε > 0) (ℓ : α) : Prop :=
  (∀ n, a n ≤ ℓ) ∧ (∃ n, ℓ ≤ a n + ε)

-- Nope that's not what i want! I really want the ε > 0 and ub
lemma improve_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [NoMinOrder α]
    (a : ℕ → α) (ε : α) (ε_pos : ε > 0) :
    (approximate_lub a ub ε ε_pos) → (approximate_lub a ub (ε / 2))  :=
  by admit

-- TODO:
-- - show that if a lub exists for some ε,
-- - find some ε for which there is a lub
-- - conclude by induction that there is a lub for any ε


theorem IsCauchy_of_monotone_and_upperBound (a : ℕ → ℝ) :
    Monotone a -> (∃ ub, ∀ n, a n ≤ ub) -> IsCauchy a := by
  intro monotone_a ⟨ub, a_n_le_ub⟩
  apply monotone_a.isCauchy_iff.mpr
  -- by_contra h
  -- push_neg at h

  admit
  -- rw [IsCauchy]
  -- intro ε ε_pos
  -- by_contra h
  -- push_neg at h -- ∀ (m : ℕ), ∃ n ≥ m, ∃ p ≥ m, ε ≤ |a n - a p|
  -- -- extract a subsequence that breaks the bounded by induction?
  -- -- first "sort" n and m by order to simplify the |·| (aux lemma).
  -- have h' : ∀ (m : ℕ), ∃ n > m, ε ≤ a n - a m := by
  --   admit
  -- have h_2 : ∃ b, SubSeq b a ∧ ∀ n, ε ≤ a (n + 1) - a n := by
  --   admit
  -- have h_3 : ∃ n, a n > ub := by admit
  -- grind
