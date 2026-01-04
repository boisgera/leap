import Mathlib
import RealAnalysis.Lesson12

set_option pp.showLetValues true


/-
New definitions
-/

def IsAPeak (a : ℕ → ℝ) (n : ℕ) := ∀ m ≥ n, a m ≤ a n

def UnboundedPeaks (a : ℕ → ℝ) := ∀ n, ∃ m ≥ n, IsAPeak a m

/-
Main theorem (which is a preparation for Bolzano-Weirestrass:
every bounded sequence has a Cauchy sub-sequence)
-/

#check choice_sequence
-- choice_sequence (p : ℕ → Prop) :
--     (∀ (n : ℕ), ∃ m ≥ n, p m) →
--     ∃ ns, StrictMono ns ∧ ∀ (i : ℕ), p (ns i)

theorem monotone_subsequence_of_boundedPeaks {a : ℕ → ℝ} :
    ¬UnboundedPeaks a -> ∃ b, SubSeq a b ∧ StrictMono b := by
  intro not_unbounded_peaks
  simp only [UnboundedPeaks, IsAPeak] at not_unbounded_peaks
  push_neg at not_unbounded_peaks --  ∃ n, ∀ x ≥ n, ∃ m ≥ x, a x < a m
  let ⟨n, hn⟩ := not_unbounded_peaks
  -- need to "massage" hn here. to get rid of the `≥ n` part.
  -- let seq := choice_sequence (fun (m) => ∃ m ≥ x, a x < a m)
  sorry

/-!
I'd also like to prove "directly" that any real-valued sequence has either
an increasing subsequence or a non-increasing one. Arf, state that as an
intro of this file, this is actually the main statement. Nothing about
boundedness of the sequence at this stage.

I don't *think* at this stage that UnboundedPeak stuff is relevant.
We can make a case analysis and prove that if there is no increasing
subsequence, then there is a non-decreasing one and that's over ... right?
Unless the proof is too hairy?
-/
