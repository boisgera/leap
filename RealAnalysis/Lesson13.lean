import Mathlib
import RealAnalysis.Lesson12

set_option pp.showLetValues true


/-
New definition: peak

This concept appears when you think about maximal (i.e. non-extendable)
finite "subsequences" of increasing functions: the latest point in the
finite sequence has to be a peak.
-/

def IsAPeak (a : ℕ → ℝ) (n : ℕ) := ∀ m ≥ n, a m ≤ a n

def FinitelyManyPeaks (a : ℕ → ℝ) :=
  ∃ m, ∀ n, IsAPeak a n -> n ≤ m

theorem not_finitelyManyPeaks (a : ℕ → ℝ) :
    ¬FinitelyManyPeaks a ↔ ∀ m, ∃ n > m, IsAPeak a n := by
  constructor
  . intro h
    rw [FinitelyManyPeaks] at h
    push_neg at h
    intro m
    specialize h m
    let ⟨n, peak_a_n, m_lt_n⟩ := h
    use n
  . intro h
    rw [FinitelyManyPeaks]
    push_neg
    intro m
    specialize h m
    let ⟨n, n_gt_m, isAPeak_a_n⟩ := h
    use n

/-
Main theorem
-/

-- From the previous lesson
#check choice_sequence
-- choice_sequence (p : ℕ → Prop) :
--     (∀ (n : ℕ), ∃ m ≥ n, p m) →
--     ∃ ns, StrictMono ns ∧ ∀ (i : ℕ), p (ns i)

theorem monotone_subsequence_of_boundedPeaks {a : ℕ → ℝ} :
    ¬FinitelyManyPeaks a -> ∃ b, SubSeq b a ∧ Antitone b := by
  intro h_not_finitelyManyPeaks
  have h := (not_finitelyManyPeaks a).mp h_not_finitelyManyPeaks
  have h' : ∀ (m : ℕ), ∃ n ≥ m, IsAPeak a n := by
    intro m
    specialize h m
    have ⟨n, n_gt_m, isAPeak_a_n⟩ := h
    use n
    apply And.intro
    . linarith
    . assumption
  have hseq := choice_sequence (IsAPeak a)
  specialize hseq h'
  have ⟨ns, h_strictMono, h_peak⟩ := hseq
  let b := a ∘ ns
  use b
  constructor
  . rw [SubSeq]
    use ns
  . simp only [IsAPeak] at h_peak
    have : ∀ i, ns i < ns (i+1) → a (ns i) < a (ns (i + 1)) := by
      intro i
      specialize h_peak i (ns (i + 1))
      intro h
      specialize h_peak (show ns i ≤ ns (i +1) from by linarith [h])

      admit
    admit
