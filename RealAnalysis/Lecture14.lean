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

theorem IsCauchy_of_monotone_and_upperBound (a : ℕ → ℝ) :
    Monotone a -> (∃ ub, ∀ n, a n ≤ ub) -> IsCauchy a := by
  intro monotone_a ⟨ub, a_n_le_ub⟩
  rw [IsCauchy]
  intro ε ε_pos
  by_contra h
  push_neg at h -- ∀ (m : ℕ), ∃ n ≥ m, ∃ p ≥ m, ε ≤ |a n - a p|
  -- extract a subsequence that breaks the bounded by induction?
  -- first "sort" n and m by order to simplify the |·| (aux lemma).
  have h' : ∀ (m : ℕ), ∃ n > m, ε ≤ a n - a m := by
    admit
  have h_2 : ∃ b, SubSeq b a ∧ ∀ n, ε ≤ a (n + 1) - a n := by
    admit
  have h_3 : ∃ n, a n > ub := by admit
  grind
