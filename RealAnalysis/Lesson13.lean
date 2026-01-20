import Mathlib
-- import RealAnalysis.Lesson12 -- get `SubSeq` and `choice_sequence`

set_option pp.showLetValues true


/--
The peak concept appears when you think about "maximal" (non-extendable
on the right) finite "subsequences" of increasing functions: such as
finite sequence is non-extendable iff the its latest value is a peak.
-/
def IsPeak (a : ℕ → ℝ) (n : ℕ) := ∀ m ≥ n, a m ≤ a n

/--
The practical definition of having a finite number of peak
(which conveniently bypasses explicit use of finiteness)
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
  . intro h
    rw [IsPeak] at *
    simp only [Function.comp_apply] at h
    intro p p_ge_m_add_n
    specialize h (p - m)
    specialize h (show p - m ≥ n from by omega)
    rw [add_comm n m] at h
    rw [show p - m + m = p from by omega] at h
    exact h

/--
Corollary of `strictMono_subSeq_of_noPeak`
-/

theorem strictMono_subSeq_of_finitelyManyPeaks {a : ℕ → ℝ} :
    FinitelyManyPeaks a -> ∃ b, SubSeq b a ∧ StrictMono b := by
  intro finitelyManyPeak_a
  rw [FinitelyManyPeaks] at finitelyManyPeak_a
  let ⟨m, no_peak_after_m⟩ := finitelyManyPeak_a
  let σ : ℕ → ℕ := fun n => n + (m + 1)
  let a_σ := a ∘ σ

  have no_peak_a_σ : (∀ n, ¬IsPeak a_σ n) := by
    simp only [a_σ, σ]
    intro n
    rw [<- peak_translation_invariance a (m + 1)]
    intro h
    specialize no_peak_after_m (m + 1 + n) h
    omega

  let ⟨b_σ, subseq_b_σ_a_σ, strictMono_b_σ⟩ :
      ∃ b_σ, SubSeq b_σ a_σ ∧ StrictMono b_σ :=
    strictMono_subSeq_of_noPeak no_peak_a_σ
  use b_σ
  constructor
  . rw [SubSeq] at subseq_b_σ_a_σ ⊢
    have ⟨τ, strictMono_τ, b_σ_eq_a_σ_comp_τ⟩ := subseq_b_σ_a_σ
    simp only [a_σ] at b_σ_eq_a_σ_comp_τ
    use σ ∘ τ
    constructor
    . apply StrictMono.comp
      . simp only [σ, StrictMono]
        intro a b a_lt_b
        linarith
      . exact strictMono_τ
    . rw [Function.comp_assoc] at b_σ_eq_a_σ_comp_τ
      exact b_σ_eq_a_σ_comp_τ
  . exact strictMono_b_σ

/--
Main theorem
-/
theorem strictMono_or_antitone_subsequence (a : ℕ → ℝ) :
  ∃ b, SubSeq b a ∧ (StrictMono b ∨ Antitone b)
    := by
  by_cases h : FinitelyManyPeaks a
  . let ⟨b, subSeq_b, strictMono_b⟩ := strictMono_subSeq_of_finitelyManyPeaks h
    use b
    constructor
    . exact subSeq_b
    . left
      exact strictMono_b
  . let ⟨b, subSeq_b, antitone_b⟩ := antitone_subsequence_of_infinitelyManyPeaks h
    use b
    constructor
    . exact subSeq_b
    . right
      exact antitone_b
