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

/-
OK, reboot, let's do this from scratch without extra hints: I want to prove
that from any real-valued sequence I can extract an increasing sequence
or a non-decreasing one.
-/

/-
Let's start with
-/

lemma exists_increasing_subsequence_of_eventually_exist_greater
    (a : ℕ → ℝ) :
    (∀ m, ∃ n > m, a m > a n) → ∃ (b : ℕ → ℝ), SubSeq b a ∧ StrictMono b := by
  intro h
  choose next hnext using h
  let ns : ℕ → ℕ := Nat.rec 0 (fun _ n => next n)
  let b := a ∘ ns
  use b
  constructor
  . rw [SubSeq]
    use ns
    constructor
    . apply strictMono_of_lt_succ
      intro n not_is_max_n
      induction n with
      | zero =>
        simp only [ns]
        simp only [Nat.rec_zero, Nat.succ_eq_succ, Nat.succ_eq_add_one, zero_add, Nat.rec_one]
        exact (hnext 0).1
      | succ n ih =>
        simp only [ns]
        -- apply (hnext (n+1)).1
        simp
        apply (hnext _).1
    . simp only [b]
  . admit


/- Could we have obtained that from ? -/
#check choice_sequence
-- choice_sequence (p : ℕ → Prop) :
--   (∀ (n : ℕ), ∃ m ≥ n, p m) → ∃ ns, StrictMono ns ∧ ∀ (i : ℕ), p (ns i)
/- Arf no, we need a more powerful version where p can also depend on n,
forget about it -/

lemma lemma_1 (a : ℕ → ℝ) :
    ¬(∀ m, ∃ n > m, a m > a n) -> ∃ m, ∀ n > m, a m ≤ a n := by
  intro h
  push_neg at h
  assumption

theorem main (a : ℕ → ℝ) :
    (∃ (b : ℕ → ℝ), SubSeq b a ∧ StrictMono b) ∨
    (∃ (b : ℕ → ℝ), SubSeq b a ∧ Antitone b) := by
    admit
