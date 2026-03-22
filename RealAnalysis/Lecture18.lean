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



-- `Nat.even_or_odd` is great (and standard) to deal with parity
-- but it captures it as a Prop, not a Type
#check Nat.even_or_odd
-- Nat.even_or_odd (n : ℕ) : Even n ∨ Odd n

-- The modulo `· % 2` would encode parity as a Type,
-- but the result is in ℕ,
-- so the pattern match on 0 and 1 is not exhaustive...
#check Nat.mod
-- Nat.mod : ℕ → ℕ → ℕ

-- What we need here is `Nat.bodd` whicj encodes parity as a Bool.
#check Nat.bodd
-- Nat.bodd (n : ℕ) : Bool

-- When we need the k such that n = 2 * k or n = 2 * k + 1,
-- we can use k = n.div2 and prove the equality with `Nat.bodd_add_div2`
#check Nat.bodd_add_div2
-- Nat.bodd_add_div2 (n : ℕ) : n.bodd.toNat + 2 * n.div2 = n

-- Yeah, Nat.div2 is equivalent to (· / 2), but it's not immediately
-- obvious.

#print Nat.div2
-- def Nat.div2 : ℕ → ℕ :=
--   fun n => n.boddDiv2.2

#print Nat.boddDiv2
-- def Nat.boddDiv2 : ℕ → Bool × ℕ :=
-- fun x =>
--   Nat.brecOn x fun x f =>
--     (match (motive := (x : ℕ) → Nat.below x → Bool × ℕ) x with
--       | 0 => fun x => (false, 0)
--       | n.succ => fun x =>
--         match x.1 with
--         | (false, m) => (true, m)
--         | (true, m) => (false, m.succ))
--       f

theorem core (a : ℕ → ℝ) (aa : AA a) (n : ℕ) :
    match aa, n.bodd with
    | .up _ _ _ _, false | .down _ _ _ _, true
      =>
        (∑ k ∈ Finset.range (n + 2), a k) ≥ (∑ k ∈ Finset.range n, a k)  ∧
        (∑ k ∈ Finset.range (n + 2), a k) ≤ (∑ k ∈ Finset.range (n + 1), a k)
    | .down _ _ _ _, false | .up _ _ _ _, true
      =>
        (∑ k ∈ Finset.range (n + 2), a k) ≤ (∑ k ∈ Finset.range n, a k)  ∧
        (∑ k ∈ Finset.range (n + 2), a k) ≥ (∑ k ∈ Finset.range (n + 1), a k)
    := by

    let k := n.div2
    let n_eq : match n.bodd with
        | false => n = 2 * k
        | true => n = 2 * k + 1 := by
      match p : n.bodd with
      | false =>
        have := Nat.bodd_add_div2 n
        simp only [
          show n.div2 = k from by rfl,
          show n.bodd.toNat = 0 from by grind
        ] at this
        grind
      | true =>
        have := Nat.bodd_add_div2 n
        simp only [
          show n.div2 = k from by rfl,
          show n.bodd.toNat = 1 from by grind
        ] at this
        grind

    match aa, parity: n.bodd with
    | .up a_1 a_2 a_3 a_4, false =>
      simp only
      constructor
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [<- add_assoc]
        simp only [ge_iff_le, le_add_iff_nonneg_left]
        simp [parity] at n_eq
        grind -- Claude suggests that I work a lot for nothing...
        -- since grind is powerful enough to end right here.
        -- rw [n_eq]
        -- specialize a_3 k
        -- grind
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [add_le_iff_nonpos_left]
        simp [parity] at n_eq; rw [n_eq]
        specialize a_2 k
        grind
    |.down a_1 a_2 a_3 a_4, true
      =>
      simp only
      constructor
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [le_add_iff_nonneg_left]
        simp [parity] at n_eq; rw [n_eq]
        specialize a_4 k
        grind
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [add_le_add_iff_right, add_le_iff_nonpos_left]
        simp [parity] at n_eq; rw [n_eq]
        specialize a_1 (k + 1)
        grind
    | .up a_1 a_2 a_3 a_4, true
      =>
      simp only
      constructor
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [add_le_iff_nonpos_left]
        simp [parity] at n_eq; rw [n_eq]
        specialize a_4 k
        grind
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [ge_iff_le, add_le_add_iff_right, le_add_iff_nonneg_left]
        simp [parity] at n_eq; rw [n_eq]
        specialize a_1 (k + 1)
        grind
    | .down a_1 a_2 a_3 a_4, false
      =>
      simp only
      constructor
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [add_le_iff_nonpos_left]
        simp [parity] at n_eq
        rw [n_eq]
        specialize a_4 k
        grind
      . rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        rw [Finset.range_add_one, Finset.sum_insert (by grind)]
        simp only [<- add_assoc]
        simp only [ge_iff_le, add_le_add_iff_right, le_add_iff_nonneg_left]
        specialize a_4 k
        grind

theorem core_coro (a : ℕ → ℝ) (aa : AA a) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), a k ∈
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k)
    := by
  have c := core a aa n
  match aa, parity : n.bodd with
  | .up a_1 a_2 a_3 a_4, false | .down a_1 a_2 a_3 a_4, true  =>
    simp only [parity] at c
    simp only [Set.mem_uIcc]
    left; grind
  | .down a_1 a_2 a_3 a_4, false | .up a_1 a_2 a_3 a_4, true =>
    simp only [parity] at c
    simp only [Set.mem_uIcc]
    right; grind

#check Set.uIcc_subset_uIcc
-- Set.uIcc_subset_uIcc.{u_1} {α : Type u_1} [Lattice α] {a₁ a₂ b₁ b₂ : α}
-- (h₁ : a₁ ∈ Set.uIcc a₂ b₂) (h₂ : b₁ ∈ Set.uIcc a₂ b₂) :
-- Set.uIcc a₁ b₁ ⊆ Set.uIcc a₂ b₂

#check Set.right_mem_uIcc
-- Set.right_mem_uIcc.{u_1} {α : Type u_1} [Lattice α] {a b : α} :
-- b ∈ Set.uIcc a b


theorem core_coro' (a : ℕ → ℝ) (aa : AA a) (m n : ℕ) :
    (m ≤ n) →
    Set.uIcc (∑ k ∈ Finset.range n, a k) (∑ k ∈ Finset.range (n + 1), a k) ⊆
    Set.uIcc (∑ k ∈ Finset.range m, a k) (∑ k ∈ Finset.range (m + 1), a k) := by
    intro m_le_n
    let p := n - m
    have : n = m + p := by grind
    rw [this]
    induction p with
    | zero =>
      intro _ x
      exact x
    | succ p ih =>
      apply Set.uIcc_subset_uIcc
      . have : (∑ k ∈ Finset.range (m + p + 1), a k) ∈ Set.uIcc (∑ k ∈ Finset.range (m + p), a k) (∑ k ∈ Finset.range (m + p + 1), a k) :=
          Set.right_mem_uIcc
        exact ih this
      . have cc := core_coro a aa (m + p)
        ring_nf at *
        have := ih cc
        exact this

-- Alternative route
-- -----------------------------------------------------------------------------
-- When I think of it, I now believe (after much murking around) that the
-- "definition" of AA that is actually the proper compromise between
-- understandability, conciseness and usefuleness is proof is AA_ultimate
-- below.
-- The def is not 100% intuitive but it's still easily understandable
-- there is a single k ranking which is selectable and the Set.uIcc
-- allows us to pack a bunch of inequalities alternatives at once.

def AA_ultimate (a : ℕ → ℝ) :=
    ∀ k, a k + a (k + 1) ∈ Set.uIcc 0 (a k)

-- Note that AA_ultimate is a Prop, not a Type and still is exactly what we
-- need!

#check AA_ultimate
-- AA_ultimate (a : ℕ → ℝ) : Prop

-- Substitute for core_coro that uses the AA_ultimate def
theorem nested_uIcc_induction (a : ℕ → ℝ) (aa : AA_ultimate a) (n : ℕ) :
      Set.uIcc
        (∑ k ∈ Finset.range (n + 1), a k)
        (∑ k ∈ Finset.range (n + 2), a k) ⊆
      Set.uIcc
        (∑ k ∈ Finset.range n, a k)
        (∑ k ∈ Finset.range (n + 1), a k) := by
    have lemma_add (a b c d : ℝ) :
        a + b ∈ Set.uIcc (c + b) (d + b) → a ∈ Set.uIcc c d := by
      simp only [Set.mem_uIcc]
      grind
    apply Set.uIcc_subset_uIcc
    . apply Set.right_mem_uIcc
    . apply lemma_add (b := - ∑ k ∈ Finset.range n, a k)
      rw [Finset.range_add_one, Finset.sum_insert (by grind)]
      rw [Finset.range_add_one, Finset.sum_insert (by grind)]
      rw [Finset.range_add_one, Finset.sum_insert (by grind)]
      ring_nf
      have := aa n
      ring_nf at this
      exact this

theorem nested_uIcc (a : ℕ → ℝ) (aa : AA_ultimate a) (m n : ℕ) :
    (m ≤ n) →
    Set.uIcc (∑ k ∈ Finset.range n, a k) (∑ k ∈ Finset.range (n + 1), a k) ⊆
    Set.uIcc (∑ k ∈ Finset.range m, a k) (∑ k ∈ Finset.range (m + 1), a k) := by
    intro m_le_n
    let p := n - m
    have : n = m + p := by grind
    rw [this]
    induction p with
    | zero =>
      intro _ x
      exact x
    | succ p ih =>
      apply Set.uIcc_subset_uIcc
      . have : (∑ k ∈ Finset.range (m + p + 1), a k) ∈ Set.uIcc (∑ k ∈ Finset.range (m + p), a k) (∑ k ∈ Finset.range (m + p + 1), a k) :=
          Set.right_mem_uIcc
        exact ih this
      . have cc := nested_uIcc_induction a aa (m + p)
        ring_nf at *
        have : ∑ x ∈ Finset.range (2 + m + p), a x ∈
            Set.uIcc
              (∑ x ∈ Finset.range (1 + m + p), a x)
              (∑ x ∈ Finset.range (2 + m + p), a x)
          := by apply Set.right_mem_uIcc
        exact ih (cc this)

-- -----------------------------------------------------------------------------

theorem almost_there (a : ℕ → ℝ) (aa : AA_ultimate a) (n : ℕ) :
    |∑ k ∈ Finset.range n, a k| ≤ |a 0| := by
  have c := nested_uIcc a aa 0 n
  specialize c (by norm_num)
  have :
      (∑ k ∈ Finset.range n, a k) ∈
      Set.uIcc (∑ k ∈ Finset.range n, a k) (∑ k ∈ Finset.range (n + 1), a k) :=
    Set.left_mem_uIcc
  have l := c this
  simp only [Nat.zero_add, Finset.range_zero, Finset.sum_empty,
    Finset.range_one, Finset.sum_singleton] at l
  -- l : ∑ k ∈ Finset.range n, a k ∈ Set.uIcc 0 (a 0)
  simp only [Set.mem_uIcc] at l
  rcases l with h1 | h2
  . grind
  . grind

theorem shifted_AA_is_AA (a : ℕ → ℝ) (aa : AA_ultimate a) (n : ℕ) :
    AA_ultimate (fun k => a (k + n)) := by
  rw [AA_ultimate]
  intro k
  have := aa (k + n)
  ring_nf at *
  exact this


-- TODO
theorem what_we_actually_need (a : ℕ → ℝ) (aa : AA_ultimate a) (m n : ℕ) :
    (m ≤ n) → |∑ k ∈ Finset.Ico m n, a k| ≤ |a m| := by
  intro m_le_n
  have what_i_know : |∑ k ∈ Finset.range (n - m), a (k + m)| ≤ |a (0 + m)| :=
    almost_there (fun k => a (k + m)) (shifted_AA_is_AA a aa m) (n - m)
  grind -- Probably not good enough to conclude?

  -- TODO: extract the first bound from the ⊆, rewrite the stuff
  -- as inequalities, then substract ∑ k ∈ Finset.range m from
  -- everything and the result is almost there.
  -- admit

theorem t2 (a : ℕ → ℝ) :
    Tendsto a atTop (nhds 0) → AA_ultimate a →
    ∃ ℓ, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds ℓ) := by
  admit
