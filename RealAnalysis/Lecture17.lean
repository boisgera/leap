import Mathlib

open Filter

set_option pp.showLetValues true

namespace Series

#check Finset.sum
-- Finset.sum.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M]
-- (s : Finset ι) (f : ι → M) : M

def partial_sum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)), a k -- notation for Finset.sum Finset.range a


noncomputable def a₁ (n : ℕ) : ℝ := 1 / 2 ^ (n + 1)

-- 1 / 2 + 1 / 4 + ... + 1 / 2 ^ k = 1 - 2 ^ k
theorem partial_sum_a₁_eq : partial_sum a₁ = fun n => 1 - 1 / 2 ^ (n + 1) := by
  ext n
  simp only [partial_sum, a₁]
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf

#check Tendsto
-- Filter.Tendsto.{u_1, u_2} {α : Type u_1} {β : Type u_2}
--     (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop

#check Metric.tendsto_atTop
-- Metric.tendsto_atTop.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [Nonempty β] [SemilatticeSup β]
--     {u : β → α} {a : α} :
--     Tendsto u atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

example : Tendsto (partial_sum a₁) atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  rw [partial_sum_a₁_eq]
  simp only
  simp only [Real.dist_eq]
  norm_num
  intro ε ε_pos
  have : StrictMono fun n => (2 ^ (n  + 1) : ℝ)⁻¹ := by
    admit
  let N := max 0 ⌈Real.logb 2.0 ε⌉
  have : (2 ^ (N + 1))⁻¹ < ε := by
    admit
  admit

-- TODO: prove that ∑ 1 / (k + 1)^2 is convergent.
-- Steps:
--  1. study ∑ 1 / (k + 1)(k + 2), (partial sum and convergence)
--  2. Show that the original series is monotone and bounded
--     and thus converges (via Cauchy and completeness).
--
-- Nota: we have 1 / (k + 1)^2 ≤ 1 if k = 1 else ≤ 1 / k * (k + 1).
-- Unfortunately there is an index shift wrt the Leibniz series,
-- that's a small extra difficulty.

noncomputable def LeibnizSeries (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)), 1 / (k + 1) / (k + 2)

lemma Leibniz_term (k : ℕ) :
    (1 / (k + 1) / (k + 2) : ℝ) = 1 / (k + 1) - 1 / (k + 2) := by
  field_simp
  norm_num

lemma Leibniz_sum (n : ℕ) : LeibnizSeries n = (1 - 1 / (n + 2) : ℝ) := by
  rw [LeibnizSeries]
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    simp only [Nat.cast_zero, zero_add]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring_nf

#check Metric.tendsto_atTop
-- Metric.tendsto_atTop.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
--     Tendsto u atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

theorem LeibnizSeries_lim_eq_one : Tendsto LeibnizSeries atTop (nhds 1) := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]
  simp only [Leibniz_sum]
  -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |1 - 1 / (↑n + 2) - 1.0| < ε
  ring_nf
  simp only [gt_iff_lt, ge_iff_le, abs_neg, abs_inv]
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → |2 + ↑n|⁻¹ < ε
  field_simp
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → 1 < ε * |2 + ↑n|
  have h_pos (n : ℕ) : (2 + ↑n : ℝ) ≥ 0 := by positivity
  -- We enter in conv mode so that we don't have to unfold the predicate
  -- which would force us to select the N yet immediately. The proper
  -- choice of N will be clear once we have simplified the inner expression.
  -- The other (simpler?) solution: use `let N := sorry` and change afterwards.
  conv =>
    intro ε ε_pos
    right
    ext n
    intro N
    intro n_ne_N
    rw [abs_of_nonneg (h_pos N)]

  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ n, ∀ (N : ℕ), n ≤ N → 1 < ε * (2 + ↑N)
  intro ε ε_pos
  use ⌈1 / ε⌉₊ -- what we are actually interested in: ⌈1 / ε⌉₊ ≥ 1 / ε
  intro N N_ge_t
  have l1 : ↑N ≥ 1 / ε := Nat.ceil_le.mp N_ge_t
  have l2 : ε * (2 + ↑N) ≥ ε * (2 + (1 / ε)) := by nlinarith
  apply lt_of_lt_of_le _ l2
  -- ⊢ 1 < ε * (2 + 1 / ε)
  field_simp
  have : ε * 2 > 0 := by positivity
  linarith

noncomputable def sum_inv_squares (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)), 1 / (k + 1)^2

lemma strictMono_sum_inv_squares : StrictMono sum_inv_squares := by
  simp only [StrictMono, sum_inv_squares]
  apply strictMono_nat_of_lt_succ
  intro n
  nth_rw 2 [Finset.sum_range_succ]
  simp only [lt_add_iff_pos_right]
  positivity

lemma domination (n : ℕ) :
    (n = 0 → sum_inv_squares n ≤ 1) ∧ -- TODO: "factor in" the two clauses
    (n ≥ 1 → sum_inv_squares n ≤ 1 + LeibnizSeries (n - 1))
    := by
  induction n with
  | zero =>
    constructor
    . intro n_eq_0; clear n_eq_0
      simp only [sum_inv_squares]
      simp only [
        zero_add,
        Finset.range_one,
        Finset.sum_singleton,
      ]
      grind
    . grind
  | succ n ih =>
    constructor
    . grind
    . intro _
      simp only [sum_inv_squares, LeibnizSeries]
      simp only [add_tsub_cancel_right]
      by_cases h : n = 0
      . simp only [h]
        norm_num
      . have n_ge_1 : n ≥ 1 := by grind
        let ih' := ih.right
        specialize ih' n_ge_1
        rw [sum_inv_squares, LeibnizSeries] at ih'
        simp only [Nat.sub_add_cancel n_ge_1] at ih'
        rw [Finset.sum_range_succ]
        nth_rewrite 2 [Finset.sum_range_succ]
        have aux:
          (∑ x ∈ Finset.range (n + 1),
            (1 / (↑x + 1) ^ 2 : ℝ)) + (1 / (↑(n + 1) + 1) ^ 2 : ℝ) ≤
          (1 : ℝ) +
            (∑ x ∈ Finset.range n, (1 / (↑x + 1) / (↑x + 2) : ℝ)
          ) + 1 / (↑n + 1) / (↑n + 2) := by
          apply add_le_add
          . assumption
          . field_simp
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
            nlinarith
        grind

lemma domination' (n : ℕ) : sum_inv_squares n ≤ 2 - 1 / (n + 1) := by
  match n  with
  | 0 =>
    rw [
      sum_inv_squares,
      zero_add,
      Finset.range_one,
      Finset.sum_singleton
    ]
    norm_num
  | n + 1 =>
    have dom : sum_inv_squares (n + 1) ≤ 1 + LeibnizSeries n :=
      (domination (n + 1)).right (by grind)
    -- lemma Leibniz_sum (n : ℕ) : LeibnizSeries n = (1 - 1 / (n + 2) : ℝ)
    simp [Leibniz_sum] at dom
    simp only [Nat.cast_add, Nat.cast_one]
    grind

theorem bound_sum_inv_squares  (n : ℕ) : sum_inv_squares n ≤ 2 := by
  have dom := domination' n -- sum_inv_squares n ≤ 2 - 1 / (↑n + 1)
  apply le_trans (a := sum_inv_squares n) (b := 2 - 1 / (n + 1))
  . exact dom
  . field_simp
    linarith

theorem cauchySeq_of_upperBound_and_strictMono
    (a : ℕ → ℝ)
    (ub : ∃ b, ∀ n, a n ≤ b)
    (strictMono : StrictMono a) :
    CauchySeq a := by
  apply Metric.cauchySeq_iff.mpr
  simp only [Real.dist_eq] at *
  by_contra h
  push_neg at h
  let ⟨ε, ε_pos, h'⟩ := h
  have p : ∀ (m : ℕ), ∃ n ≥ m, a n ≥ a m + ε := by
    admit
  choose next h_next using p
  -- A definition by induction of `a'` will be easier to deal with.
  -- let a' := a ∘ (next^[·] 0)
  let next_iter := Nat.rec
    (motive := fun (_ : ℕ) => ℕ)
    (zero := 0)
    (succ := (fun _ n => next n))
  -- There is not someting like that which is automatically generated?
  -- Not for local functions?
  have next_iter_eq : next_iter = Nat.rec 0 (fun _ n => next n) := by
    rfl
  let a' := a ∘ next_iter
  have a'_eq (n : ℕ) : a' n = a (next_iter n) := by
    simp only [a']
    rw [Function.comp_apply]
  have super_linear_subseq(n : ℕ) : a' 0 + n * ε ≤ a' n  := by
    induction n with
    | zero =>
      grind
    | succ n ih =>
      simp only [a']
      simp only [Function.comp_apply]
      simp only [next_iter]
      simp only [Nat.rec_zero, Nat.cast_add, Nat.cast_one]
      simp only [<- next_iter_eq]
      -- ih : a' 0 + ↑n * ε ≤ a' n
      -- a 0 + (↑n + 1) * ε ≤ a (next (next_iter n))
      have : a (next (next_iter n)) ≥ a (next_iter n) + ε :=
        h_next (next_iter n) |>.right
      have : a' n + ε ≤ a (next (next_iter n)) := by
        simp only [a'_eq]
        exact this
      ring_nf
      have : a 0 + ↑n * ε + ε ≤ a' n + ε := by
        simp only [add_le_add_iff_right]
        exact ih
      linarith
  have ⟨b, b_bound⟩ := ub
  -- Relevant context at this stage:
  -- ε : ℝ
  -- ε_pos : ε > 0
  -- super_linear_subseq : ∀ (n : ℕ), a' 0 + ↑n * ε ≤ a' n
  -- b : ℝ
  -- b_bound : ∀ (n : ℕ), a n ≤ b
  have ⟨n, n_gt_t⟩ := exists_nat_gt ((b - a' 0) / ε)
  have : b < a' 0 + n * ε := by
    field_simp at n_gt_t
    grind
  specialize super_linear_subseq n
  have : b < a' n := by
    linarith
  have : b < a (next_iter n) := by
    simp only [a'_eq] at this
    exact this
  specialize b_bound (next_iter n)
  linarith

theorem cauchySeq_sum_inv_squares: CauchySeq sum_inv_squares := by
  apply cauchySeq_of_upperBound_and_strictMono sum_inv_squares
  . use 2
    exact bound_sum_inv_squares
  . exact strictMono_sum_inv_squares

-- # Problem set 15
-- ## Ex #1

namespace Ex1

-- Aim: prove that `a n < 2` for all n and that `a` converges.
noncomputable def a (n : ℕ) : ℝ :=
  match n with
  | 0 => √2
  | n + 1 => √(2 + a n)

theorem a_nonneg (n : ℕ) : 0 ≤ a n := by
  induction n with
  | zero =>
    simp only [a]
    positivity
  | succ n ih =>
    simp only [a]
    apply Real.sqrt_nonneg

theorem a_lt_two (n : ℕ) : a n < 2 := by
  induction n with
  | zero =>
    simp only [a]
    apply (Real.sqrt_lt _ _).mpr
    repeat grind
  | succ n ih =>
    simp only [a]
    have := a_nonneg n
    apply (Real.sqrt_lt _ _).mpr
    repeat grind

theorem a_strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  nth_rewrite 2 [a.eq_def]; simp only
  induction n with
  | zero =>
    simp only [a.eq_def]
    apply Real.sqrt_lt_sqrt (by grind)
    simp only [lt_add_iff_pos_right]
    positivity
  | succ n ih =>
    simp only [a]
    have := a_nonneg n
    apply Real.sqrt_lt_sqrt
    repeat linarith

theorem bingo : CauchySeq a :=
  cauchySeq_of_upperBound_and_strictMono
    a
    ⟨2, show ∀ n, a n ≤ 2 from by
      intro n ; linarith [a_lt_two n]
    ⟩
    a_strictMono

end Ex1

-- Ex #2. Compute the limit of Real.sqrt(n * n + n) - n
namespace Ex2

noncomputable def a (n : ℕ) := √(n ^ 2 + n) - n

theorem trick
    (a b : ℝ)
    (a_add_b_nonzero : a + b ≠ 0) :
    a - b = (a^2 - b^2) / (a + b) := by
  field_simp
  ring_nf

theorem a_eq₁ (n : ℕ) (n_pos : n > 0) : a n = n / (√(n ^ 2 + n) + n) := by
  rw [a]
  have : ↑n > 0 := by positivity
  have : ↑n ^ 2 + ↑n > (0 : ℝ) := by positivity
  have : √(↑n ^ 2 + ↑n) > 0 := by positivity
  have : √(↑n ^ 2 + ↑n) + ↑n > 0 := by positivity
  rw [trick]
  grind
  grind

theorem a_eq (n : ℕ) (n_pos : n > 0) : a n = 1 / (√(1 + 1/n) + 1) := by
  have n_nonzero : ↑n ≠ (0 : ℝ) := by
    have : ↑n > (0 : ℝ) := by positivity
    grind
  have : ↑n > 0 := by positivity
  have : ↑n ^ 2 + ↑n > (0 : ℝ) := by positivity
  have : √(↑n ^ 2 + ↑n) > 0 := by positivity
  have : √(↑n ^ 2 + ↑n) + ↑n > 0 := by positivity
  have q_ne_0 : √(↑n ^ 2 + ↑n) + ↑n ≠ (0 : ℝ) := by positivity

  rw [← mul_div_mul_left (c := ↑n) _ _ n_nonzero]
  simp only [mul_one]
  rw [← Real.sqrt_sq (show 0 ≤ ↑ n from by admit)]
  rw [mul_add]
  rw [← Real.sqrt_mul]
  have : √(↑n ^ 2) = (↑n : ℝ) := by
    apply Real.sqrt_sq
    linarith
  simp only [this]
  field_simp
  nth_rewrite 2 [mul_add]
  rw [mul_one]
  rw [← sq]
  rw [← eq_div_iff q_ne_0]
  apply a_eq₁
  repeat positivity

noncomputable def f (x : ℝ) : ℝ := 1 / (√(1 + x) + 1)

lemma continuousAt_f_zero: ContinuousAt f 0 := by
  unfold f
  have : √(1 + 0) + 1 ≠ 0 := by grind
  fun_prop (disch := assumption)

-- `Tendsto` is actually more than even the general concept of a limit AFAICT.
-- It is the general concept of limit when the target filter is actually a
-- class of neighbourhoods of some kind. But in general `Tendsto` captures
-- that the image of filter by and application is finer that a given target
-- filter. UPDATE: no, not exactly, pre-images are involved instead
-- (as they should).
-- Note: the documentation of `Tendsto` use terminology of neighbourhoods as
-- generic members of filters, without any topological setting.
#print Tendsto
-- def Filter.Tendsto.{u_1, u_2} : {α : Type u_1} → {β : Type u_2} →
--     (α → β) → Filter α → Filter β → Prop :=
--   fun {α} {β} f l₁ l₂ => map f l₁ ≤ l₂

#check map

theorem lim_f_at_zero : Tendsto f (nhds (0 : ℝ)) (nhds (1/2 : ℝ)) := by
  have := continuousAt_f_zero
  rw [ContinuousAt] at this
  have f_zero_eq : f 0 = (1 / 2 : ℝ) := by
    rw [f] ; norm_num
  rw [f_zero_eq] at this
  exact this

theorem lim_inv_at_top :
    Tendsto (fun (n : ℕ) => (1 / n : ℝ)) atTop (nhds 0) := by
  admit

#check Tendsto.comp

-- This stuff is 99% there, except that the sequence used differ from a at n=0.
theorem almost_a_tendsto_one :
    Tendsto (fun (n : ℕ) => f (1 / (n : ℝ))) atTop (nhds (1 / 2)) := by
  have comp := Tendsto.comp lim_f_at_zero lim_inv_at_top
  have : (f ∘ (fun (n : ℕ) => 1 / (n : ℝ))) = (fun (n : ℕ) => f (1 / (n : ℝ))) := by
    ext n; simp only [Function.comp_apply]
  simp only [this] at comp
  exact comp


#check eventually_atTop
-- Filter.eventually_atTop.{u_3} {α : Type u_3} [Preorder α] [IsDirectedOrder α] {p : α → Prop} [Nonempty α] :
--   (∀ᶠ (x : α) in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b

theorem a_eventuallyEq: a =ᶠ[atTop] (fun (n : ℕ) => f (1 / (n : ℝ))) := by
  rw [EventuallyEq]
  -- ⊢ ∀ᶠ (x : ℕ) in atTop, a x = f (1 / ↑x)
  apply eventually_atTop.mpr
  -- ⊢ ∃ a, ∀ b ≥ a, Ex2.a b = f (1 / ↑b)
  use 1
  intro n n_ge_one
  rw [f]
  apply a_eq
  linarith

#check Tendsto.congr'
-- Filter.Tendsto.congr'.{u_1, u_2} {α : Type u_1} {β : Type u_2}
--     {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β}
--     (hl : f₁ =ᶠ[l₁] f₂) (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂

theorem a_tendsto_one : Tendsto a atTop (nhds (1 / 2 : ℝ)) := by
  apply Tendsto.congr' a_eventuallyEq.symm
  exact almost_a_tendsto_one

end Ex2

-- -----------------------------------------------------------------------------
-- Ex #3. Show that the (Cesaro-)average of a series converging to ℓ
-- converges to ℓ.

namespace Cesaro

noncomputable def cesaro (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  -- ∑ x ∈ s, f x is notation for Finset.sum s f
  (∑ i ∈ Finset.range (n + 1), a i) / (n + 1)

-- Alternative notation, less idiomatic, but shorter
noncomputable def cesaro_Iic (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  -- Notation for (∑ i ∈ Finset.Iic n, a i) / (↑n + 1)
  -- 'i' for -∞, 'c' for closed
  (∑ i ≤ n, a i) / (n + 1)

-- Both definition are equivalent:
lemma cesaro_eq_cesaro_Iic : cesaro = cesaro_Iic := by
  ext a n
  rw [cesaro, cesaro_Iic]
  rw [Nat.range_succ_eq_Iic]

-- The recursive definition is also interesting:
noncomputable def cesaro_rec (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => a 0
  | n + 1 =>
    (cesaro_rec a n) * (n + 1) / (n + 2) + (a (n + 1)) / (n + 2)

theorem cesaro_rec_eq_cesaro : cesaro_rec = cesaro := by
  ext a n
  induction n with
  | zero =>
    rw [cesaro, cesaro_rec]
    rw [Nat.cast_zero, zero_add, zero_add, div_one]
    rw [Finset.range_one, Finset.sum_singleton]
  | succ n ih =>
    rw [cesaro, cesaro_rec]
    rw [ih]
    rw [Finset.sum_range_succ]
    have : (∑ i ∈ Finset.range (n + 1), a i) = (cesaro a n) * (n + 1) := by
      rw [cesaro]
      rw [div_mul_cancel₀]
      positivity
    rw [this]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring_nf

-- Some general properties of the Cesaro operator (that we need for the
-- `cesaro_lift` helper lemma).

-- The finite sum is additive:
#check Finset.sum_add_distrib
-- Finset.sum_add_distrib.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s : Finset ι}
--     [AddCommMonoid M] {f g : ι → M} :
--     ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x

lemma cesaro_add (a b : ℕ → ℝ) : cesaro (a + b) = cesaro a + cesaro b := by
  ext n
  rw [Pi.add_apply]
  simp only [cesaro]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  ring_nf

-- The finite sum is homogeneous:
#check Finset.smul_sum
-- Finset.smul_sum.{u_1, u_2, u_3} {M : Type u_1} {N : Type u_2} {γ : Type u_3}
--     [AddCommMonoid N] [DistribSMul M N] {r : M} {f : γ → N} {s : Finset γ} :
--     r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x

lemma cesaro_smul(s : ℝ) (a : ℕ → ℝ) : cesaro (s • a) = s • cesaro a := by
  ext n
  rw [cesaro]
  simp only [Pi.smul_apply]
  rw [cesaro]
  rw [<- Finset.smul_sum]
  simp [smul_eq_mul]
  ring_nf

lemma cesaro_cst (c : ℝ) : cesaro (fun _ => c) = (fun _ => c) := by
  ext n
  simp only [cesaro]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

-- Let's define it as a `LinearMap` (bundle of the operator and the proof bits)
-- We don't use it later on but we could easily use `cesaroMap` instead of
-- `cesaro` since there is a coercion (right?)
noncomputable def cesaroMap : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) := {
  toFun := cesaro,
  map_add' := cesaro_add,
  map_smul' := cesaro_smul,
}

lemma cesaro_lift:
    (∀ (a : ℕ → ℝ), Tendsto a atTop (nhds 0) -> Tendsto (cesaro a) atTop (nhds 0)) ->
    (∀ (a : ℕ → ℝ), ∀ (ℓ : ℝ), Tendsto a atTop (nhds ℓ) -> Tendsto (cesaro a) atTop (nhds ℓ)) := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]
  intro h a ℓ hε
  let b := (a · - ℓ)
  have b_eq (n : ℕ) : b n = (a n - ℓ) := by
    rfl
  have b_eq_a_sub_cst_ℓ : b = a - fun x => ℓ := by
    rfl
  simp only [<- b_eq] at hε
  specialize h b
  simp only [sub_zero] at *
  specialize h hε
  have lemma₁ (n : ℕ) : ℓ = cesaro (fun _ => ℓ) n := by
    rw [cesaro_cst]
  have lemma₂ (a b : ℕ → ℝ) (n : ℕ) : cesaro a n - cesaro b n = cesaro (a - b) n := by
    have h := cesaro_add (a - b) b
    simp only [sub_add_cancel] at h
    rw [funext_iff] at h
    specialize h n
    simp only [Pi.add_apply] at h
    grind
  conv =>
    rhs; rhs ; rhs; ext; ext n; rhs; lhs; arg 1
    rw [lemma₁ n, lemma₂, <- b_eq_a_sub_cst_ℓ]
  exact h

def exists_local_bound (a : ℕ → ℝ) (m : ℕ): ∃ b, ∀ n < m, a n ≤ b := by
  induction m with
  | zero =>
    use 0
    intro n n_neg -- impossible
    grind
  | succ m ih =>
    let ⟨b, is_bound⟩ := ih
    use max b (a m)
    intro n n_lt_succ_m
    by_cases h : n < m
    . specialize is_bound n h
      grind
    . have : n = m := by grind
      grind

theorem exists_global_bound {a : ℕ → ℝ} {ℓ : ℝ} (h : Tendsto a atTop (nhds ℓ)) :
    ∃ b, ∀ n, |a n| ≤ b := by
  simp only [Metric.tendsto_atTop, Real.dist_eq] at h
  specialize h 1 (by positivity)
  let ⟨N, hN⟩ := h
  have hb (n : ℕ) (n_ge_N : n ≥ N): |a n| < |ℓ| + 1 := by
    specialize hN n n_ge_N
    have : |a n| - |ℓ| ≤ |a n - ℓ| := by
      apply abs_sub_abs_le_abs_sub
    linarith
  have ⟨b', hb'⟩ := exists_local_bound (|a ·|) N
  let b := max (|ℓ| + 1) b'
  use b
  intro n
  by_cases h : n < N
  . specialize hb' n h
    grind
  . simp only [not_lt] at h
    specialize hb n
    grind

#check Finset.sum_range_add
-- Finset.sum_range_add.{u_4} {M : Type u_4} [AddCommMonoid M]
--     (f : ℕ → M) (n m : ℕ) :
--     ∑ x ∈ Finset.range (n + m), f x =
--     ∑ x ∈ Finset.range n, f x + ∑ x ∈ Finset.range m, f (n + x)

theorem TODO (a : ℕ → ℝ) : Tendsto a atTop (nhds 0) -> Tendsto (cesaro a) atTop (nhds 0) := by
  intro h
  let ⟨b, hb⟩ := exists_global_bound h
  have b_nonneg : b ≥ 0 := by
    specialize hb 0
    have : |a 0| ≥ 0 := by
      apply abs_nonneg
    linarith

  simp only [Metric.tendsto_atTop, Real.dist_eq] at *
  simp only [sub_zero] at *
  intro ε ε_pos

  have lemma₁ : ∀ (N' : ℕ), ∃ N ≥ N', ∀ n ≥ N,
      |(∑ i ∈ Finset.range (N' + 1), a i) / (n + 1)| < ε / 2 := by
    intro N'

    let ⟨N, ineq₁, ineq₂⟩ : ∃ N, N ≥ N' ∧ N + 1 > 2 * (N' + 1) * b / ε := by
      let N := max N' ⌈2 * (N' + 1) * b / ε⌉₊
      have ineq₁ : N ≥ N' := by grind
      have : ⌈2 * (N' + 1) * b / ε⌉₊ ≤ N := by
        apply le_max_right
      have : ⌈2 * (N' + 1) * b / ε⌉₊ ≤ (N : ℝ) := by
        apply Nat.cast_le.mpr this
      have : 2 * (N' + 1) * b / ε ≤ ⌈2 * (N' + 1) * b / ε⌉₊ := by
        apply Nat.le_ceil
      have : 2 * (N' + 1) * b / ε ≤ N  := by
        linarith
      have ineq₂: 2 * (N' + 1) * b / ε < N + 1 := by
        linarith
      exact ⟨N, ineq₁, ineq₂⟩

    use N
    constructor
    . grind
    . simp only [abs_div]
      intro n n_ge_N
      calc |∑ i ∈ Finset.range (N' + 1), a i| / |↑n + 1|
      _ ≤ ∑ i ∈ Finset.range (N' + 1), |a i| / |↑n + 1| := by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ ∑ i ∈ Finset.range (N' + 1), b / |↑n + 1| := by
        apply Finset.sum_le_sum
        intro i _
        apply div_le_div_of_nonneg_right (hb i) (abs_nonneg _)
      _ ≤ (N' + 1) * b / |↑n + 1| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc]
        rw [Nat.cast_add, Nat.cast_one]
      _ ≤ (N' + 1) * b / (n + 1) := by
        rw [abs_of_pos (by positivity)]
      _ < ε / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have hn : (n : ℝ) + 1 ≥ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right n_ge_N 1
        have ineq₂' : 2 * (↑N' + 1) * b < (↑N + 1) * ε := by
          rwa [gt_iff_lt, div_lt_iff₀ ε_pos] at ineq₂
        nlinarith

  have lemma₂ : ∃ (N' : ℕ), ∀ n ≥ N',
      |(∑ i ∈ Finset.Ico (N' + 1) (n + 1), a i) / (n + 1)| < ε / 2 := by
    specialize h (ε / 2) (by positivity)
    have ⟨N, hN⟩ := h; clear h
    use N
    intro n n_ge_N

    rw [abs_div]

    have : (n : ℝ) + 1 ≥ 0 := by positivity
    simp only [abs_of_nonneg this]

    apply div_lt_iff₀ (by positivity) |>.mpr

    have : |∑ i ∈ Finset.Ico (N + 1) (n + 1), a i| < (↑n + 1) * (ε / 2) := by
      rcases Nat.eq_or_lt_of_le n_ge_N with rfl | hn
      · -- case n = N: Ico (N+1) (N+1) is empty
        simp only [le_refl, Finset.Ico_eq_empty_of_le, Finset.sum_empty, abs_zero] --[Finset.Ico_self]
        positivity
      · -- case n > N: Ico is nonempty
        calc |∑ i ∈ Finset.Ico (N + 1) (n + 1), a i|
            ≤ ∑ i ∈ Finset.Ico (N + 1) (n + 1), |a i| := Finset.abs_sum_le_sum_abs _ _
          _ < ∑ _i ∈ Finset.Ico (N + 1) (n + 1), ε / 2 := by
              apply Finset.sum_lt_sum
              · intro i hi
                exact le_of_lt (hN i (by have := Finset.mem_Ico.mp hi; omega))
              · exact ⟨N + 1, Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩, hN (N+1) (by omega)⟩
          _ = Finset.card (Finset.Ico (N + 1) (n + 1)) * (ε / 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (↑n + 1) * (ε / 2) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith)
              simp only [Nat.card_Ico]
              push_cast
              exact_mod_cast (by omega : n - N ≤ n + 1)

    linarith



  simp only [cesaro]
  have ⟨N', hN'⟩ := lemma₂
  clear lemma₂
  specialize lemma₁ N'
  have ⟨N, hN⟩ := lemma₁
  clear lemma₁
  -- specialize hN' N
  have ⟨N_ge_N', hN''⟩ := hN
  clear hN
  -- specialize hN' N_ge_N'
  use N
  intro n n_ge_N
  specialize hN' n (show n ≥ N' from by linarith)
  specialize hN'' n n_ge_N
  -- hN' : |(∑ i ∈ Finset.Ico (N' + 1) (n + 1), a i) / (↑n + 1)| < ε / 2
  -- hN'' : |(∑ i ∈ Finset.range (N' + 1), a i) / (↑n + 1)| < ε / 2
  -- ⊢ |(∑ i ∈ Finset.range (n + 1), a i) / (↑n + 1)| < ε

  have hsplit :
      Finset.range (n + 1) =
      Finset.range (N' + 1) ∪ (Finset.Ico (N' + 1) (n + 1)) := by
    ext x
    simp only [Finset.mem_range, Order.lt_add_one_iff, Finset.mem_union, Finset.mem_Ico,
      Order.add_one_le_iff]
    grind
  rw [hsplit, Finset.sum_union (Finset.disjoint_left.mpr (by simp [Finset.mem_Ico]; omega)), add_div]
  calc |(∑ x ∈ Finset.range (N' + 1), a x) / (↑n + 1) + (∑ x ∈ Finset.Ico (N' + 1) (n + 1), a x) / (↑n + 1)|
    _ ≤ |(∑ x ∈ Finset.range (N' + 1), a x) / (↑n + 1)| + |(∑ x ∈ Finset.Ico (N' + 1) (n + 1), a x) / (↑n + 1)| := by apply abs_add_le _ _
    _ < ε := by linarith

end Cesaro


end Series

-- TODO: Manage infinite sums via
--     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html#tsum

-- Summation Filters:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.html
