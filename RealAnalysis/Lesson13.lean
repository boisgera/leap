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
    let eq_or_lt := eq_or_gt_of_not_lt (show ¬ (f n < n) from by grind)
    cases eq_or_lt with
    | inl fn_eq_n => -- this branch is absurd
        have h := hf.right
        rw [fn_eq_n] at h
        simp at h
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
      -- perform an induction on k. Or use an existing theorem. Yes, do that
      admit
    . simp only [b]
  . admit

theorem strictMono_subSeq_of_finitelyManyPeaks {a : ℕ → ℝ} :
    FinitelyManyPeaks a -> ∃ b, SubSeq b a ∧ StrictMono b := by
  intro h_finitelyManyPeaks
  rw [FinitelyManyPeaks] at h_finitelyManyPeaks
  let ⟨m, hm⟩ := h_finitelyManyPeaks; clear h_finitelyManyPeaks
  have hm' : ∀ n > m, ¬IsPeak a n := by
    intro n
    specialize hm n
    rw [gt_iff_lt, <- not_le]
    apply mt
    exact hm
  simp only [IsPeak] at hm'
  push_neg at hm' -- ∀ n > m, ∃ k ≥ n, a n < a k

  -

  -- Now we just need to choice the fuck up hm' to get a fct f : n > m -> k
  -- and then build by recursion (actually dependent choice would be enough)
  choose f hf using hm'
  -- need to build the indice by recursion and prove at each step that they
  -- are > m. Jeeez that stuff is complex. Good luck proving what we need
  -- with it!
  -- Update. TODO: add the property that each new sample is greater than
  -- the other in the result instead of extracting it later.
  -- Arf nope, I can't do that... Or can I?
  -- let ns : (i : ℕ) → { k : ℕ // k > m } ∧ a (i + 1) > a i
  -- Mmmm let's try!
  let ns : ℕ → { k : ℕ // k > m } := Nat.rec
    ⟨m + 1, show (m + 1) > m by linarith⟩
    fun i ⟨n, n_gt_m⟩ =>
      let n' := f n n_gt_m
      ⟨
        n',
        show n' > m from by
          specialize hf n n_gt_m
          simp [n']
          linarith
      ⟩
  let b := a ∘ (·.val ) ∘ ns
  use b
  constructor
  . -- ⊢ SubSeq b a
    rw [SubSeq]
    use (·.val ) ∘ ns
    constructor
    . apply strictMono_nat_of_lt_succ
      intro i
      simp only [Function.comp_apply, Subtype.coe_lt_coe]
      conv => rhs ; simp only [ns] -- the def of ns for the rsh only (ns (i + 1))
      --- Mmm how could we simplify the rec given that's its applied to a (i + 1)?
      -- simp only [Nat.rec_add_one] -- Doesn't work??? Ah SHOOT, now our induction
      -- is defined on the subtype { k : ℕ // k > m }, not ℕ ...
      admit
    . grind
  . admit -- ⊢ StrictMono b
