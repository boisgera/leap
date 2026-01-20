import Mathlib
import RealAnalysis.Lesson12

set_option pp.showLetValues true


/-!
New definition: peak

This concept appears when you think about "maximal" (i.e. non-extendable
on the right) finite "subsequences" of increasing functions: such as
finite sequence is non-extendable iff the its latest value is a peak.
-/

def IsPeak (a : ℕ → ℝ) (n : ℕ) := ∀ m ≥ n, a m ≤ a n

/-!
The practical definition of having a finite number of peak
(which conveniently bypasses the explicit use of finiteness)
-/
def FinitelyManyPeaks (a : ℕ → ℝ) := ∃ m, ∀ n, IsPeak a n → n ≤ m

theorem not_finitelyManyPeaks (a : ℕ → ℝ) :
    ¬FinitelyManyPeaks a ↔ ∀ m, ∃ n > m, IsPeak a n := by
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

-- Note: I'd like to complement that with another lemma that "lifts" the
--       local ("next") existence to global by induction.

lemma next_to_global (p : ℕ → Prop) (h0 : ∃ n, p n)
    (h1 : ∀ n, p n → ∃ m > n, p m) :
    (∀ n, ∃ m ≥ n, p m) := by
  intro n
  induction n with
  | zero =>
    let ⟨n, hn⟩ := h0
    use n
    grind
  | succ n ih =>
    let ⟨m, m_ge_n, p_m⟩ := ih
    have ⟨l, l_gt_m, p_l⟩ := h1 m p_m
    use l
    grind

def choice_sequence'
    (p : ℕ → Prop)
    (h0 : ∃ n, p n)
    (h1 : ∀ n, p n → ∃ m > n, p m) :
    ∃ ns, StrictMono ns ∧ ∀ (i : ℕ), p (ns i) :=
  next_to_global p h0 h1 |> choice_sequence p

/-!
This we need below to prove `strictMono_subSeq_of_finitelyManyPeaks`
(at least a very specialized version of it).
Is it or is it not a corollary of choice_sequence'? Dunno, not obvious.
-/

theorem choice_sequence_dep
    (p : ℕ → ℕ → Prop)
    (h0 : ∃ k > 0, p 0 k)
    (h1 : ∀ m, ∀ n > m, p m n  → ∃ k > n, p n k) :
    ∃ ns, StrictMono ns ∧ ∀ (i : ℕ), p (ns i) (ns (i + 1)) := by
  admit

theorem antitone_subsequence_of_infinitelyManyPeaks {a : ℕ → ℝ} :
    ¬FinitelyManyPeaks a -> ∃ b, SubSeq b a ∧ Antitone b := by
  intro h_not_finitelyManyPeaks
  have h := (not_finitelyManyPeaks a).mp h_not_finitelyManyPeaks
  have h' : ∀ (m : ℕ), ∃ n ≥ m, IsPeak a n := by
    intro m
    specialize h m
    have ⟨n, n_gt_m, isAPeak_a_n⟩ := h
    use n
    apply And.intro
    . linarith
    . assumption
  have hseq := choice_sequence (IsPeak a)
  specialize hseq h'
  have ⟨ns, h_strictMono, h_peak⟩ := hseq
  let b := a ∘ ns
  use b
  constructor
  . rw [SubSeq]
    use ns
  . simp only [IsPeak] at h_peak
    have : ∀ i, b (i + 1) ≤ b i := by
      simp only [b]
      intro i
      specialize h_peak i (ns (i + 1))
      have : ns (i + 1) ≥ ns i := by
        apply le_of_lt
        apply h_strictMono
        linarith
      specialize h_peak this
      simp only [Function.comp_apply]
      assumption
    apply antitone_nat_of_succ_le
    assumption

#check strictMono_nat_of_lt_succ
-- strictMono_nat_of_lt_succ.{u} {α : Type u} [Preorder α] {f : ℕ → α}
--     (hf : ∀ (n : ℕ), f n < f (n + 1)) : StrictMono f

#print Nat.rec_add_one
-- @[defeq] theorem Nat.rec_add_one.{u_1} : ∀ {C : ℕ → Sort u_1}
--     (h0 : C 0) (h : (n : ℕ) → C n → C (n + 1)) (n : ℕ),
--      Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) :=
--   fun {C} h0 h n => rfl

-- TODO: make the aux result with the same conclusion but with the
-- "has no peak" assumption. The induction that is required can be
-- carried on on ℕ instead of a subtype and that is MUCH easier.

theorem strictMono_subSeq_of_noPeak {a : ℕ → ℝ} :
    (∀ n, ¬IsPeak a n) -> ∃ b, SubSeq b a ∧ StrictMono b := by
  intro noPeak
  simp_rw [IsPeak] at noPeak
  push_neg at noPeak
  choose f hf using noPeak
  have f_gt_id (n : ℕ) : f n > n := by
    specialize hf n
    let ⟨fn_ge_n, a_n_lt_a_f_n⟩ := hf
    let eq_or_lt := eq_or_gt_of_not_lt (show ¬(f n < n) from by grind)
    cases eq_or_lt with
    | inl fn_eq_n => -- absurd
        have h := hf.right
        rw [fn_eq_n] at h
        simp only [lt_self_iff_false] at h
    | inr n_lt_fn =>
        exact n_lt_fn
  let σ (k : ℕ) : ℕ := f^[k] 0
  let b := a ∘ σ
  use b
  constructor
  . rw [SubSeq]
    use σ
    constructor
    . simp only [σ]
      apply strictMono_nat_of_lt_succ
      intro n
      rw [Function.iterate_succ']
      rw [Function.comp_apply]
      apply f_gt_id
    . simp only [b]
  . apply strictMono_nat_of_lt_succ
    intro n
    simp only [b, Function.comp_apply, σ, Function.iterate_succ']
    specialize hf (f^[n] 0)
    exact hf.right

lemma peak_translation_invariance (a : ℕ → ℝ) (m n : ℕ) :
    IsPeak a (m + n) ↔ IsPeak (a ∘ (· + m)) n := by
  constructor
  . simp only [IsPeak] at *
    intro h
    rw [Function.comp_apply]
    intro n_1 n_1_ge_n
    specialize h (n_1 + m) (show n_1 + m ≥ m + n from by linarith)
    rw [Function.comp_apply]
    rw [add_comm m n] at h
    exact h
  . admit

-- The desired theorem is a corollary of `strictMono_subSeq_of_noPeak`
theorem strictMono_subSeq_of_finitelyManyPeaks {a : ℕ → ℝ} :
    FinitelyManyPeaks a -> ∃ b, SubSeq b a ∧ StrictMono b := by
  intro finitelyManyPeak_a
  rw [FinitelyManyPeaks] at finitelyManyPeak_a
  let ⟨m, no_peak_after_m⟩ := finitelyManyPeak_a
  let σ : ℕ → ℕ := fun n => n + (m + 1)
  let a' := a ∘ σ

  have no_peak_a' : (∀ n, ¬IsPeak a' n) := by
    intro k
    simp only [a', σ]
    simp only [IsPeak] at *
    repeat simp only [Function.comp]
    push_neg

    admit

  admit
