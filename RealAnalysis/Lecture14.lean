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
    -- we need a trichotomy here : n < p, n = p or n > p and do some
    -- case analysis, using hm in two different ways.
    admit

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
