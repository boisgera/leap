import Mathlib

open Filter

#check Finset.sum_Ico_eq_sub
-- Finset.sum_Ico_eq_sub.{u_4} {δ : Type u_4} [AddCommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
--   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k - ∑ k ∈ Finset.range m, f k

theorem convergence_of_absolute_convergence (a : ℕ → ℝ) :
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), |a k|) atTop (nhds ℓ)) →
    (∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ)) := by
  -- 1. get the Cauchyness of (|a ·|) from its convergence
  -- 2. transform it into the elementary version
  -- 3. deduce the Cauchyness of a from this (elementary version)
  -- 4. lift that into the abstract version
  -- 5. deduce the convergence of a
  --
  rintro ⟨lim_abs_a, conv_abs_sum_a⟩
  let cauchy_abs_sum_a := conv_abs_sum_a.cauchySeq
  simp only [Metric.cauchySeq_iff', Real.dist_eq] at cauchy_abs_sum_a
  -- cauchy_abs_sum_a : ∀ ε > 0, ∃ N, ∀ n ≥ N,
  --     |∑ k ∈ Finset.range (n + 1), |a k| - ∑ k ∈ Finset.range (N + 1), |a k|| < ε

  have cauchy_sum_a' : -- prov thet a is Cauchy, elementary flavor (step 3.)
      ∀ ε > 0, ∃ m, ∀ n ≥ m,
      |∑ k ∈ Finset.range (n + 1), a k - ∑ k ∈ Finset.range (m + 1), a k| < ε := by
    intro ε ε_pos
    let ⟨m, hm⟩ := cauchy_abs_sum_a ε ε_pos
    use m
    intro n n_ge_m
    specialize hm n n_ge_m
    simp [<- Finset.sum_Ico_eq_sub (|a ·|) (show m + 1 ≤ n + 1 from by linarith)] at hm
    -- hm : |∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|| < ε
    calc |∑ k ∈ Finset.range (n + 1), a k - ∑ k ∈ Finset.range (m + 1), a k|
      _ = |(∑ k ∈ Finset.Ico (m + 1) (n + 1), a k)| := by
        simp [Finset.sum_Ico_eq_sub a (show m + 1 ≤ n + 1 from by linarith)]
      _ ≤ (∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|) := by apply Finset.abs_sum_le_sum_abs
      _ ≤ |(∑ k ∈ Finset.Ico (m + 1) (n + 1), |a k|)| := by grind
      _ < ε := by exact hm

  have cauchy_sum_a : CauchySeq fun n => ∑ k ∈ Finset.range (n + 1), a k := by
    simp_rw [<- Real.dist_eq] at cauchy_sum_a'
    rw [<- Metric.cauchySeq_iff'] at cauchy_sum_a'
    exact cauchy_sum_a'

  apply cauchySeq_tendsto_of_complete

  admit

-- This def has an issue here: since this is a prop we can't properly
-- distinguish the two component cases to build a theorem?
def Alternating (a : ℕ → ℝ) :=
  (∀ k, a (2 * k) ≥ 0 ∧  a (2 * k + 1) ≤ 0) ∨
  (∀ k, a (2 * k) ≤ 0 ∧  a (2 * k + 1) ≥ 0)

-- Example: with

-- theorem demo (a : ℕ → ℝ) (h : Alternating a) :
--     match h with
--     | Or.inl _ => a 0 ≥ 0
--     | Or.inr _ => a 0 ≤ 0
--   := by admit

-- we get the error:

-- Tactic `cases` failed with a nested error:
-- Tactic `induction` failed: recursor `Or.casesOn` can only eliminate into `Prop`

inductive AlternatingAntitone (a : ℕ → ℝ) : Type where
| up :
    (∀ k, 0 ≤ a (2 * k)) →
    (∀ k, a (2 * k + 1) ≤ 0) →
    (∀ k, -a (2 * k + 1) ≤ a (2 * k)) →
    (∀ k, a (2 * k + 2) ≤ -a (2 * k + 1)) →
    AlternatingAntitone a
| down :
    (∀ k, a (2 * k) ≤ 0) →
    (∀ k, 0 ≤ a (2 * k + 1)) →
    (∀ k, a (2 * k + 1) ≤ -a (2 * k)) →
    (∀ k, -a (2 * k + 2) ≤ a (2 * k + 1)) →
    AlternatingAntitone a

abbrev AA := AlternatingAntitone

#check Nat.bodd

theorem core (a : ℕ → ℝ) (aa : AA a) (n : ℕ) :
    match aa, Nat.bodd n with
    | .up _ _ _ _, false | .down _ _ _ _, true
      =>
        (∑ k ∈ Finset.range (n + 2), a k) ≥ (∑ k ∈ Finset.range n, a k)  ∧
        (∑ k ∈ Finset.range (n + 2), a k) ≤ (∑ k ∈ Finset.range (n + 1), a k)
    | .down _ _ _ _, false | .up _ _ _ _, true
      =>
        (∑ k ∈ Finset.range (n + 2), a k) ≤ (∑ k ∈ Finset.range n, a k)  ∧
        (∑ k ∈ Finset.range (n + 2), a k) ≥ (∑ k ∈ Finset.range (n + 1), a k)
    := by
  induction n with
  | zero =>
    simp only [Nat.bodd_zero, zero_add, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.sum_empty]
    match aa with
    | AlternatingAntitone.up a_1 a_2 a_3 a_4 =>
      simp
      constructor
      . simp only [Finset.range_add_one]
        simp only [Finset.range_zero, insert_empty_eq, Finset.mem_singleton, one_ne_zero,
          not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
        linarith [a_3 0]
      . rw [Finset.range_add_one]
        simp only [
          Finset.range_one,
          Finset.mem_singleton,
          one_ne_zero,
          not_false_eq_true,
          Finset.sum_insert,
          Finset.sum_singleton]
        linarith [a_2 0]
    | AlternatingAntitone.down a_1 a_2 a_3 a_4 =>
      simp
      constructor
      . simp only [Finset.range_add_one]
        simp only [Finset.range_zero, insert_empty_eq, Finset.mem_singleton, one_ne_zero,
          not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
        linarith [a_3 0]
      . simp only [Finset.range_add_one]
        simp only [Finset.range_zero, insert_empty_eq, Finset.mem_singleton, one_ne_zero,
          not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, le_add_iff_nonneg_left]
        linarith [a_2 0]
  | succ n ih =>
    match aa, parity: (n + 1).bodd with
    | .up a_1 a_2 a_3 a_4, false =>
      simp only [Nat.bodd_succ, Bool.not_eq_eq_eq_not, Bool.not_false] at parity
      rw [parity] at ih
      have ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := by
        grind
      simp only at ih
      simp only
      constructor
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [<- add_assoc]
        simp only [ge_iff_le, le_add_iff_nonneg_left]
        rw [hk]
        simp [add_assoc]
        specialize a_3 (k + 1)
        ring_nf at a_3
        ring_nf
        linarith
      . sorry
        -- ⊢ ∑ k ∈ Finset.range (n + 1 + 2), a k ≤ ∑ k ∈ Finset.range (n + 1 + 1), a k
    |.down a_1 a_2 a_3 a_4, true
      => sorry
    | .up a_1 a_2 a_3 a_4, true
      => sorry
    |.down a_1 a_2 a_3 a_4, false
      => sorry


theorem core_coro (a : ℕ → ℝ) (aa : AA a) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), a k ∈
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k)
    := by
  admit


inductive Alt (a : ℕ → ℝ) where
| up : (∀ k, a (2 * k) ≥ 0 ∧  a (2 * k + 1) ≤ 0) → Alt a
| down : (∀ k, a (2 * k) ≥ 0 ∧  a (2 * k + 1) ≤ 0) → Alt a



theorem alternating_neg_of_alternating (a : ℕ → ℝ) :
    Alternating a → Alternating (-a) := by
  intro alt
  rw [Alternating] at *
  cases alt with
  | inl h =>
    right
    simp only [Pi.neg_apply]
    intro k
    let ⟨h1, h2⟩ := h k
    constructor
    . linarith
    . linarith
  | inr h =>
    left
    simp only [Pi.neg_apply]
    intro k
    let ⟨h1, h2⟩ := h k
    constructor
    . linarith
    . linarith

theorem antitone_neg_abs_of_antitone_abs (a : ℕ → ℝ) :
    Antitone (|a ·|) → Antitone (|(-a) ·|) := by
    intro anti
    simp only [Pi.neg_apply]
    simp only [abs_neg]
    exact anti

-- TODO: prove that a shifted alteranting seq is alternating
-- and that a shifted convergent to ℓ converges to ℓ

#print Set.uIcc
-- def Set.uIcc.{u_1} : {α : Type u_1} → [Lattice α] → α → α → Set α :=
--     fun {α} [Lattice α] a b => Set.Icc (a ⊓ b) (a ⊔ b)

#check Finset.sum_pair
-- Finset.sum_pair.{u_1, u_4} {ι : Type u_1} {M : Type u_4} [AddCommMonoid M]
-- {f : ι → M} [DecidableEq ι] {a b : ι}
-- (h : a ≠ b) : ∑ x ∈ {a, b}, f x = f a + f b


theorem core_even (a : ℕ → ℝ) (k : ℕ) : Alt a → Antitone (|a ·|) →
    ∑ i ∈ Finset.range (2*k + 2), a i ∈
      Set.Icc
        (∑ i ∈ Finset.range (2*k), a i)
        (∑ i ∈ Finset.range (2*k + 1), a i) := by
  sorry

theorem core_odd (a : ℕ → ℝ) (k : ℕ) : Alternating a → Antitone (|a ·|) →
    ∑ i ∈ Finset.range (2*k + 3), a i ∈
      Set.Icc
        (∑ i ∈ Finset.range (2*k + 1), a i)
        (∑ i ∈ Finset.range (2*k + 2), a i) := by
  sorry

theorem key (a : ℕ → ℝ) : Alternating a → Antitone (|a ·|) →
    ∀ n,
      ∑ k ∈ Finset.range (n + 2), a k ∈
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k) := by
  intro alt anti n
  induction n with
  | zero =>
    simp only [
      Finset.range_zero,
      Finset.sum_empty, zero_add,
      Finset.range_one,
      Finset.sum_singleton,
      show Finset.range 2 = {0, 1} from by decide,
      Finset.sum_pair (show 0 ≠ 1 from by norm_num)
    ]
    cases alt with
    | inl h =>
      have in1: 0 ≤ a 0 := (h 0).left
      have in2: a 1 ≤ 0 := (h 0).right
      have in3: - a 1 ≤ a 0 := by
        rw [Antitone] at anti
        specialize anti (show 0 ≤ 1 from by norm_num)
        simp only [abs_of_nonneg in1] at anti
        simp only [abs_of_nonpos in2] at anti
        exact anti
      rw [Set.uIcc_of_le in1, Set.mem_Icc]
      constructor <;> linarith
    | inr h =>
      have in1: a 0 ≤ 0 := (h 0).left
      have in2: 0 ≤ a 1  := (h 0).right
      have in3: a 1 ≤ - a 0 := by
        rw [Antitone] at anti
        specialize anti (show 0 ≤ 1 from by norm_num)
        simp only [abs_of_nonneg in2] at anti
        simp only [abs_of_nonpos in1] at anti
        exact anti
      rw [Set.uIcc_of_ge in1, Set.mem_Icc]
      constructor <;> linarith
  | succ n ih =>

    admit

-- This one should be ok (from key)
theorem coro (a : ℕ → ℝ) : Alternating a → Antitone (|a ·|) →
    ∀ n,
      Set.uIcc
        (∑ k ∈ Finset.range (n + 1), a k)
        (∑ k ∈ Finset.range (n + 2), a k)
      ⊆
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k) := by admit

-- This one is easy (from coro)
theorem coro' (a : ℕ → ℝ) : Alternating a → Antitone (|a ·|) →
    ∀ n,
      Set.uIcc
        0
        (a 0)
      ⊆
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k) := by admit

-- This should be some massaging of coro'
theorem almost_there (a : ℕ → ℝ) : Alternating a → Antitone (|a ·|) →
    ∀ n , |∑ k ∈ Finset.range n, a k| ≤ |a 0| := by

  admit

-- TODO: use almost_there on the sequence a shifted by m
theorem what_we_actually_need (a : ℕ → ℝ) : Alternating a → Antitone (|a ·|) →
    ∀ (m n : ℕ), (m ≤ n) → |∑ k ∈ Finset.Ico m n, a k| ≤ |a m| := by

  admit

theorem t2 (a : ℕ → ℝ) :
    Tendsto a atTop (nhds 0) → Alternating a → Antitone (|a ·|) →
    ∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ) := by
  admit
