import Mathlib
import RealAnalysis.Lesson13

set_option pp.showLetValues true

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

def approximate_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : ℕ → α) (ε : α) (ℓ : α) : Prop :=
  (∀ n, a n ≤ ℓ) ∧ (∃ n, ℓ ≤ a n + ε)

lemma worse_approximate_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : ℕ → α) (ε₁ ε₂: α) (ℓ : α) :
    ε₁ ≤ ε₂ →
    approximate_lub a ε₁ ℓ →
    approximate_lub a ε₂ ℓ := by
  intro ε₁_le_ε₂ approximate_lub_a_ε₁_ℓ
  rw [approximate_lub] at *
  constructor
  . exact approximate_lub_a_ε₁_ℓ.1
  . have ⟨n, hn⟩ := approximate_lub_a_ε₁_ℓ.2
    use n
    linarith

lemma improve_approximate_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : ℕ → α) (ε : α) :
    ε > 0 →
    (∃ ℓ, approximate_lub a ε ℓ ) →
    (∃ ℓ, approximate_lub a (ε / 2) ℓ) := by
  intro ε_pos ⟨ℓ, approximate_lub_a_ℓ_ε⟩
  let ℓ' := ℓ - ε / 2
  by_cases h : approximate_lub a (ε / 2) ℓ'
  . exact ⟨ℓ', h⟩
  . simp only [approximate_lub] at *
    use ℓ
    push_neg at h
    constructor
    . exact approximate_lub_a_ℓ_ε.1
    . by_contra h'
      push_neg at h'
      specialize h (by grind)
      simp [ℓ'] at h
      have ⟨n, hn⟩ := approximate_lub_a_ℓ_ε.2
      specialize h n
      linarith

-- TODO:
-- - show that if a lub exists for some ε,
-- - find some ε for which there is a lub
-- - conclude by induction that there is a lub for any ε

lemma arbitrary_precision_approximate_lub {α}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α]
    (a : ℕ → α) (ε : α) (ub : α) :
    (∀ n, a n ≤ ub) →
    ε > 0 →
    (∃ ℓ, approximate_lub a ε ℓ ) := by
  intro h_ub ε_pos
  let ε₀ := ub - (a 0) + 1
  have ε₀_pos : ε₀ > 0 := by
    specialize h_ub 0
    linarith
  have approximate_lub_a_ε₀_ub : approximate_lub a ε₀ ub  := by
    rw [approximate_lub]
    constructor
    . intro n
      specialize h_ub n
      linarith
    . use 0
      linarith
  have has_approximate_lub_a_ε₀_div_two_pow_n (n : ℕ) :
    ∃ ℓ, approximate_lub a (ε₀ / 2 ^ n) ℓ := by
    induction n with
    | zero =>
      simp only [pow_zero, div_one]
      exact ⟨ub, approximate_lub_a_ε₀_ub⟩
    | succ n ih =>
      have := improve_approximate_lub a (ε₀ / 2 ^ n) (by positivity) ih
      field_simp at this
      grind
  have chose_n : ∃ n, ε₀ / 2 ^ n ≤ ε := by
    have : ε₀ / ε > 0 := by positivity
    have ⟨n, hn⟩ : ∃ n, (ε₀ / ε) < 2 ^ n := by
      apply pow_unbounded_of_one_lt
      linarith
    use n
    field_simp at ⊢ hn
    linarith

  let ⟨n, ε'_le_ε⟩ := chose_n
  let ε' := ε₀ / 2 ^ n
  let ⟨ℓ, approximate_lub_a_ε'_ℓ⟩ := has_approximate_lub_a_ε₀_div_two_pow_n n
  use ℓ
  apply worse_approximate_lub a ε' ε ℓ ε'_le_ε approximate_lub_a_ε'_ℓ


theorem IsCauchy_of_monotone_and_upperBound (a : ℕ → ℝ) :
    Monotone a -> (∃ ub, ∀ n, a n ≤ ub) -> IsCauchy a := by
  intro monotone_a ⟨ub, a_n_le_ub⟩
  apply monotone_a.isCauchy_iff.mpr
  admit

-- TODO: document/do the "other way", by contradiction, where you don't need to
--       focus on the precision of the lub but you prove that by contradiction
--       if you are not Cauchy you exceeded any threshold.

-- theorem IsCauchy_of_monotone_and_upperBound (a : ℕ → ℝ) :
--     Monotone a -> (∃ ub, ∀ n, a n ≤ ub) -> IsCauchy a := by
--   intro monotone_a ⟨ub, a_n_le_ub⟩
--   apply monotone_a.isCauchy_iff.mpr
--   -- by_contra h
--   -- push_neg at h

--   admit
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
