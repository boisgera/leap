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

-- Ex #3. Show that the (Cesaro-)average of a series converging to ℓ
-- converges to ℓ.

namespace Cesaro

noncomputable def cesaro (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), a i) / (n + 1)

noncomputable def cesaro' (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => a 0
  | n + 1 =>
    (cesaro' a n) * (n + 1) / (n + 2) + (a (n + 1)) / (n + 2)

theorem cesaro'_eq_cesaro : cesaro' = cesaro := by
  ext a n
  induction n with
  | zero =>
    rw [cesaro, cesaro']
    rw [Nat.cast_zero, zero_add, zero_add, div_one]
    rw [Finset.range_one, Finset.sum_singleton]
  | succ n ih =>
    rw [cesaro, cesaro']
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


-- Let's make our final result easier to reach:
lemma cesaro_add (a b : ℕ → ℝ) : cesaro (a + b) = cesaro a + cesaro b := by
  ext n
  induction n with
  | zero =>
    simp only [Pi.add_apply]
    simp only [cesaro]
    simp only [
      zero_add,
      Finset.range_one,
      Nat.cast_zero,
      Pi.add_apply,
      Finset.sum_singleton,
      div_one
    ]
  | succ n ih =>
    simp only [Pi.add_apply]
    simp only [cesaro]
    simp only [Finset.sum_range_add]
    -- TODO
    admit

lemma cesaro_cst (c : ℝ) : cesaro (fun _ => c) = (fun _ => c) := by
  ext n
  simp only [cesaro]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

lemma lift₁:
    (∀ (a : ℕ → ℝ), Tendsto a atTop (nhds 0) -> Tendsto (cesaro a) atTop (nhds 0)) ->
    (∀ (a : ℕ → ℝ), ∀ (ℓ : ℝ), Tendsto a atTop (nhds ℓ) -> Tendsto (cesaro a) atTop (nhds ℓ)) := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]
  intro h a ℓ hε
  admit


-- TODO: extract cleanly the existence of a bound on a finite set.
-- TODO; ask Claude for a nice formulation of that.
def b (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  match m with
  | 0 => 0
  | m + 1 =>
    let range := Finset.range (m + 1)
    let image := Finset.image a range
    have : range.Nonempty := by grind
    have image_nonempty : image.Nonempty := Finset.image_nonempty.mpr this
    Finset.max' image image_nonempty

def b_is_bound (a : ℕ → ℝ) (m : ℕ): ∀ n < m, a n ≤ b a m := by
  intro n
  induction n with
  | zero =>
    simp [b]
    -- ...
    admit
  | succ n ih => sorry

theorem convergent_sequences_are_bounded (a : ℕ → ℝ) (ℓ : ℝ) :
    Tendsto a atTop (nhds ℓ) ->
    ∃ b, ∀ n, |a n| ≤ b := by
  intro h
  simp only [Metric.tendsto_atTop, Real.dist_eq] at h
  -- To begin with, a is *eventually* bounded
  specialize h 1 (by positivity)
  have ⟨m, hm⟩ := h
  have eventually_bounded (n : ℕ) : n ≥ m → |a n| ≤ |ℓ| + 1 := by
    intro n_ge_m
    specialize hm n n_ge_m
    have : |a n| - |ℓ| ≤ |a n - ℓ| := abs_sub_abs_le_abs_sub (a n) ℓ
    linarith
  -- a is also bounded on range m since this set is finite.

  have bounded_on_finite (n : ℕ) : ∃ b, n < m -> |a n| ≤ b := by
    induction n with
    | zero =>
      use |a 0|
      intro _
      rfl
    | succ n ih =>

      sorry

  admit

lemma TODO (a : ℕ → ℝ) : Tendsto a atTop (nhds 0) -> Tendsto (cesaro a) atTop (nhds 0)) := by
  admit

end Cesaro


end Series

-- TODO: Manage infinite sums via
--     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html#tsum

-- Summation Filters:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.html
