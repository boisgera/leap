import Mathlib

/-!
TODO:
- Compute the derivative of x ↦ x ^ 2 - 1 at 2
- Show that x ↦ 2 * x is the derivative of x ↦ x ^ 2 - 1
- Show that x ↦ x ^ 2 - 1 is continuous at each point and thus continuous
-
-/

def f (x : ℝ) : ℝ := x ^ 2 - 1

namespace Ex_0

/-!
TODO: show that x ↦ x ^ 2 - 1 is continuous (everywhere)
-/

#check Metric.continuousAt_iff
-- Metric.continuousAt_iff.{u, v} {α : Type u} {β : Type v}
--     [PseudoMetricSpace α] [PseudoMetricSpace β]
--      {f : α → β} {a : α} :
--   ContinuousAt f a ↔
--   ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) (f a) < ε

lemma f_factorization (x x_0 : ℝ) :
    f x - f x_0 = (x - x_0) * ((x - x_0) + 2 * x_0) := by
  simp only [f]
  ring_nf

lemma f_diff_domination (x x_0 δ : ℝ) (δ_pos : δ > 0) :
    |x - x_0| < δ -> |f x - f x_0| < δ * (δ + 2 * |x_0|) := by
  simp only [f_factorization]
  intro h
  simp only [abs_mul]
  have hadd : |x - x_0 + 2 * x_0| ≤ |x - x_0| + 2 * |x_0| := by
    have := abs_add_le (x - x_0) (2 * x_0)
    simp only [abs_mul, abs_two] at this
    linarith
  have hsq : |x - x_0| ^ 2 < δ ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg (x - x_0)]) h
  nlinarith [
    abs_nonneg (x - x_0),
    abs_nonneg x_0,
    mul_nonneg (abs_nonneg (x - x_0)) (abs_nonneg (x - x_0 + 2 * x_0))
  ]

theorem continuousAt_everywhere (x : ℝ) : ContinuousAt f x := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]
  intro ε ε_pos
  let δ := min 1 (ε / (1 + 2 * |x|))
  use δ
  constructor
  positivity
  intro x_1
  have dom := f_diff_domination x_1 x δ (by positivity)
  intro h
  specialize dom h
  have ineq : δ * (δ + 2 * |x|) ≤ ε := by
    have : δ * (δ + 2 * |x|) ≤ ε / (1 + 2 * |x|) * (1 + 2 * |x|) := by
      apply mul_le_mul
      . apply min_le_right
      . linarith [show δ ≤ 1 from by apply min_le_left]
      . positivity
      . positivity
    simp only [div_mul_cancel₀ ε (show (1 + 2 * |x|) ≠ 0 from by grind)] at this
    exact this
  linarith

#check continuous_iff_continuousAt
-- continuous_iff_continuousAt.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
-- [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} :
-- Continuous f ↔ ∀ (x : X), ContinuousAt f x

theorem continuous : Continuous f :=
  continuous_iff_continuousAt.mpr continuousAt_everywhere


end Ex_0

namespace Ex_1

#check deriv
-- deriv.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v}
-- [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
-- (f : 𝕜 → F) (x : 𝕜) : F

#check HasDerivAt
-- HasDerivAt.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- {F : Type v} [AddCommGroup F] [Module 𝕜 F]
-- [TopologicalSpace F] [ContinuousSMul 𝕜 F]
-- (f : 𝕜 → F) (f' : F) (x : 𝕜) : Prop

#check HasDerivAt.deriv
-- HasDerivAt.deriv.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
--   {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : HasDerivAt f f' x) : deriv f x = f'

#check hasDerivAt_iff_tendsto_slope
-- hasDerivAt_iff_tendsto_slope.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- {F : Type v} [NormedAddCommGroup F]
-- [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} :
-- HasDerivAt f f' x ↔ Filter.Tendsto (slope f x) (nhdsWithin x {x}ᶜ) (nhds f')

#check slope
-- slope.{u_1, u_2, u_3} {k : Type u_1} {E : Type u_2} {PE : Type u_3} [Field k]
-- [AddCommGroup E] [Module k E] [AddTorsor E PE]
-- (f : k → PE) (a b : k) : E

#check slope_def_field
-- slope_def_field.{u_1} {k : Type u_1} [Field k]
-- (f : k → k) (a b : k) :
-- slope f a b = (f b - f a) / (b - a)

/-!
TODO: Compute the derivative of f at x = 2
-/

lemma slope_f_at_2 (x : ℝ) : x ∈ ({2}ᶜ : Set ℝ) →
  (f x - f 2) / (x - 2) - 4 = x - 2 := by
  intro h
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
  push Not at h
  have h' : x - 2 ≠ 0 := by grind
  simp only [f]
  simp only [sub_sub_sub_cancel_right]
  norm_num
  have : x ^ 2 - 4 = (x + 2) * (x - 2) := by ring_nf
  simp only [this]
  have : (x + 2) * (x - 2) / (x - 2) = x + 2 := by
    simp only [mul_div_assoc, div_self h']
    ring_nf
  simp only [this]
  ring_nf

theorem hasDerivAt_f_4_2 : HasDerivAt f 4 2 := by
  -- Reduce the general concepts to the elementary formulation
  simp only [hasDerivAt_iff_tendsto_slope]
  simp only [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
  simp only [slope_def_field]
  -- ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄, x ∈ {2}ᶜ →
  -- |x - 2| < δ → |(f x - f 2) / (x - 2) - 4| < ε
  intro ε ε_pos
  use ε
  constructor
  exact ε_pos
  intro x x_ne_2
  simp only [slope_f_at_2 x x_ne_2]
  intro k
  exact k

/-!
TODO: same proof with general theorems (derivative of sums, products, etc.)
-/

#check hasDerivAt_const
-- hasDerivAt_const.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-- (x : 𝕜) (c : F) :
-- HasDerivAt (fun x => c) 0 x

#check hasDerivAt_id
-- hasDerivAt_id.{u} {𝕜 : Type u} [NontriviallyNormedField 𝕜] (x : 𝕜) :
-- HasDerivAt id 1 x

#check HasDerivAt.add
-- HasDerivAt.add.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-- {f g : 𝕜 → F} {f' g' : F} {x : 𝕜}
-- (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
-- HasDerivAt (f + g) (f' + g') x

#check HasDerivAt.sub
-- HasDerivAt.sub.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-- {f g : 𝕜 → F} {f' g' : F} {x : 𝕜}
-- (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
-- HasDerivAt (f - g) (f' - g') x

#check HasDerivAt.mul
-- HasDerivAt.mul.{u, u_3} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {𝔸 : Type u_3} [NormedRing 𝔸]
-- [NormedAlgebra 𝕜 𝔸] {c d : 𝕜 → 𝔸} {c' d' : 𝔸}
-- (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
-- HasDerivAt (c * d) (c' * d x + c x * d') x

theorem decompo_f : f = id * id - 1 := by
  ext x
  rw [f]
  simp only [Pi.sub_apply, Pi.mul_apply, id, Pi.one_apply]
  ring_nf

theorem hasDerivAt_f_4_2' : HasDerivAt f 4 2 := by
  -- Here we massage the result we want to make its origin/structure "obvious"
  -- (top-down approach). We could also keep the top-down approach and exhibit
  -- the value/function structure one step at a time. But the bottom-up
  -- approach is probably more intuitive TBH.
  rw [decompo_f]
  simp only [show (4 : ℝ) = 1 * id 2 + (id 2) * 1 - 0 from by norm_num]
  -- ⊢ HasDerivAt (id * id - 1) (1 * id 2 + id 2 * 1 - 0) 2
  apply HasDerivAt.sub
  . apply HasDerivAt.mul
    . apply hasDerivAt_id
    . apply hasDerivAt_id
  . apply hasDerivAt_const

lemma f_eq : f = fun x => x * x - 1 := by
  ext x; rw [f]
  ring_nf

theorem hasDerivAt_f_4_2'' : HasDerivAt f 4 2 := by
  -- Bottom-up proof. I don't like it either, this is messy.
  -- I bet there is a better way. Anyway ATM I'd rather have the top-down
  -- approach. I guess that a progressive top-down approach is what is
  -- more intuitive.
  rw [f_eq]
  have one' : HasDerivAt (fun (x : ℝ) => (1 : ℝ)) 0 2 := by
    apply hasDerivAt_const
  have : HasDerivAt (fun (x : ℝ) => x) 1 2 := by
    apply hasDerivAt_id
  have : HasDerivAt (fun (x : ℝ) => x * x) 4 2 := by
    simp only [show (fun (x : ℝ) => x * x) = (id * id) from by ext x; simp]
    have : HasDerivAt (id * id) (1 * id 2 + (id 2) * 1 : ℝ) 2 := by
      apply HasDerivAt.mul
      repeat exact this
    norm_num at this
    exact this
  simp [show (fun (x : ℝ) => x * x - 1) = (fun x => x * x) - (fun x => 1) from by
    ext x; simp only [Pi.sub_apply]
  ]
  have : HasDerivAt ((fun x : ℝ => x * x) - (fun x => 1)) (4 - 0) 2 := by
    apply HasDerivAt.sub
    exact this
    exact one'
  norm_num at this
  exact this


end Ex_1

namespace Ex_2

/-!
Compute the derivative function of f
-/

lemma f_eq : f = fun (x : ℝ) => x * x - 1 := by
  ext x
  rw [f]
  ring_nf

theorem hasDerivAt_f (x : ℝ) : HasDerivAt f (2 * x) x := by
  -- Progressive top-down style; not bad (the best so far imho)
  rw [f_eq]
  rw [show (fun x : ℝ => x * x - 1) = (fun x => x * x) - (fun x => 1) from by
    ext x ; simp [Pi.sub_apply]
  ]
  rw [show 2 * x = 2 * x - 0 from by ring_nf]
  apply HasDerivAt.sub
  . rw [show (fun x : ℝ => x * x) = (id * id) from by
      ext x; rw [Pi.mul_apply, id]
    ]
    rw [show 2 * x = 1 * x + x * 1 from by ring_nf]
    apply HasDerivAt.mul
    repeat apply hasDerivAt_id
  . apply hasDerivAt_const

end Ex_2

namespace Ex_3

/-!
Show that gaussian function is differentiable and compute its derivative
-/

noncomputable def g (x : ℝ) := Real.exp (-x ^ 2)

#check HasDerivAt.comp
-- HasDerivAt.comp.{u, u_1} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
-- (x : 𝕜)
-- {𝕜' : Type u_1} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
-- {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
-- (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
-- HasDerivAt (h₂ ∘ h) (h₂' * h') x

-- We won't use this (too easy!) but that would be what we need
#check HasDerivAt.exp
-- HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x

-- The minimal version
#check Real.hasDerivAt_exp
-- Real.hasDerivAt_exp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x

#check HasDerivAt.pow
-- HasDerivAt.pow.{u_1, u_2} {𝕜 : Type u_1} {𝔸 : Type u_2}
-- [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸]
--   [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜}
--   (h : HasDerivAt f f' x) (n : ℕ) :
--   HasDerivAt (f ^ n) (↑n * f x ^ (n - 1) * f') x

#check HasDerivAt.neg
-- HasDerivAt.neg.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v}
-- [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-- {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : HasDerivAt f f' x) :
-- HasDerivAt (-f) (-f') x

#print g
-- def Ex_3.g : ℝ → ℝ := fun x => Real.exp (-x ^ 2)

theorem g' (x : ℝ) : HasDerivAt g (- 2 * x * g x) x := by
  -- Massage the goal to make it match the result of HasDerivAt.comp
  have g_eq : g = Real.exp ∘ (fun (x : ℝ) => -x ^ 2) := by
    ext x; simp only [g, Function.comp]
  nth_rewrite 1 [g_eq]
  have g'_eq : (-2 * x * g x) = (g * (fun y : ℝ => -2 * y)) x := by
    simp only [Pi.mul_apply] ; ring_nf
  rw [g'_eq]

  -- Apply HasDerivAt.comp and fill in the subgoal
  apply HasDerivAt.comp x (h₂ := Real.exp) (h := fun x => -x ^ 2)
  . apply Real.hasDerivAt_exp
  . simp only
    -- massage the target to apply HasDerivAt.neg
    simp only [show -2 * x = -(2 * x) from by ring_nf]
    simp only [show (fun (x : ℝ) => -x^2) = - fun (x : ℝ) => x^2 from by
      ext x ; simp only [Pi.neg_apply]
    ]
    apply HasDerivAt.neg
    -- New goal: ⊢ HasDerivAt (fun x => x ^ 2) (2 * x) x
    -- Massage the goal for the applicatoin of HasDerivAt.pow
    -- Need something like: ⊢  HasDerivAt (f ^ n) (↑n * f x ^ (n - 1) * f') x
    simp only [show (fun (x : ℝ) => x ^ 2) = id ^ 2 from by
      ext x; simp only [Pi.pow_apply, id]
    ]
    have h : HasDerivAt id 1 x := by apply hasDerivAt_id
    simp only [show (2 * x) = (2 * id x ^ (2 - 1) * 1) from by
      simp only [id]; ring_nf
    ]
    apply HasDerivAt.pow (f := id) (h := h) (n := 2) (x := x)

end Ex_3
