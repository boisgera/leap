import Mathlib

set_option pp.showLetValues true

namespace Ex1

/-!
The composition of continuous functions is continuous
-/

#check ContinuousAt
-- ContinuousAt.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
--   [TopologicalSpace X] [TopologicalSpace Y]
--   (f : X → Y) (x : X) : Prop

#check Continuous
-- Continuous.{u, v} {X : Type u} {Y : Type v}
--   [TopologicalSpace X] [TopologicalSpace Y]
--   (f : X → Y) : Prop

/-!
OK, the theorem we want actually exists but we want to prove it "ourselves"
from the composition of filters. Then we'll do it again with a specialization
of the defs to δ-ε statements.
-/

#check Continuous.comp
-- Continuous.comp.{u_1, u_2, u_3} {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
-- [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
-- {f : X → Y} {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
-- Continuous (g ∘ f)

#print ContinuousAt
-- def ContinuousAt.{u_1, u_2} : {X : Type u_1} → {Y : Type u_2} →
--     [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → X → Prop :=
-- fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] f x =>
--    Filter.Tendsto f (nhds x) (nhds (f x))

#check Filter.Tendsto.comp
-- Filter.Tendsto.comp.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3}
--   {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
--   (hg : Filter.Tendsto g y z) (hf : Filter.Tendsto f x y) :
--   Filter.Tendsto (g ∘ f) x z

theorem continuousAt_comp (f g : ℝ → ℝ) (x : ℝ) :
    ContinuousAt f x → ContinuousAt g (f x) → ContinuousAt (g ∘ f) x := by
  simp only [ContinuousAt]
  intro hf hg
  simp only [Function.comp]
  apply Filter.Tendsto.comp (y := nhds (f x))
  . exact hg
  . exact hf

theorem continousAt_comp_elementary (f g : ℝ → ℝ) (x : ℝ) :
    ContinuousAt f x → ContinuousAt g (f x) → ContinuousAt (g ∘ f) x := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]
  intro hf hg
  simp only [Function.comp]
  intro ε ε_pos
  have ⟨η, η_pos, hη⟩ := hg ε ε_pos; clear hg
  have ⟨δ, δ_pos, hδ⟩ := hf η η_pos; clear hf
  use δ
  constructor
  . exact δ_pos
  . intro x1 hx
    apply hη
    apply hδ
    apply hx

theorem continous_comp (f g : ℝ → ℝ) :
    Continuous f → Continuous g → Continuous (g ∘ f) := by
  simp only [continuous_iff_continuousAt]
  intro hcf hcg x
  apply continuousAt_comp
  exact hcf x
  exact hcg (f x)

end Ex1

namespace Ex2

/-!
A uniform limit of continuous functions is continuous.
-/

#check TendstoUniformly
-- TendstoUniformly.{u_1, u_2, u_4} {α : Type u_1} {β : Type u_2} {ι : Type u_4}
--   [UniformSpace β]
--   (F : ι → α → β) (f : α → β) (p : Filter ι) : Prop

theorem uniform_limit_of_continuous (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) :
    ∀ n, Continuous (F n) →
    TendstoUniformly F f Filter.atTop →
    Continuous f := by
  admit

end Ex2

namespace Ex3



/-!
Prove that f (x) = x is integrable on [a, b] for a < b:
-/

#check BoxIntegral.HasIntegral
-- BoxIntegral.HasIntegral.{u, v, w} {ι : Type u} {E : Type v} {F : Type w}
--   [NormedAddCommGroup E] [NormedSpace ℝ E]
--   [NormedAddCommGroup F] [NormedSpace ℝ F]
--   [Fintype ι]
--   (I : BoxIntegral.Box ι)
--   (l : BoxIntegral.IntegrationParams)
--   (f : (ι → ℝ) → E)
--   (vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤)
--   (y : F) : Prop

/-!
Main parameter breakdown:

- `ι : Type u`: the index type.
  It determines the dimension of the space.
  The space being integrated over is `ι → ℝ`
  which represents `ℝⁿ` when `ι := Fin n`.
  The typeclass `[Fintype ι]` ensures `ι` is finite.

- `I : BoxIntegral.Box ι`. The domain of integration.
  A `BoxIntegral.Box ι` is a nontrivial rectangular box in `ι → ℝ` with corners
  `lower` and `upper : ι → ℝ`, satisfying `∀ i, lower i < upper i`.
  It is interpreted as the product of half-open intervals `(lower i, upper i]`.
  So for `ι = Fin n`, this is an axis-aligned box in `ℝⁿ`.
  Note: the box is closed on the low side and open on the up side
  (a simple convention which simplifies partition of boxes).

- `l : BoxIntegral.IntegrationParams`. The choice of integration theory.
  `IntegrationParams` is a structure holding 3 Boolean values used to define a
  filter; it encodes eight different parameter sets, including those
  corresponding to the Riemann integral, the Henstock-Kurzweil integral,
  and the McShane integral. Passing different values of `l` lets a single
  definition cover all three theories without code duplication.
  The Riemann, Henstock, McShane, and Generalized Perron theories have predefined
  values in `IntegrationParams`: `.Riemann`, `.Henstock`, `.McShane` and `.GP`.

- `f : (ι → ℝ) → E`. The integrand.
  It takes a point in the box and returns a value in the normed space `E`.

- `vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤`. The volume measure.

  A function which associate to any box in the integration space a
  (linear, continuous) function from `E` to `F` and is box-additive
  It is a box-additive map: given a box `J` and a partition `π` of it,
  `∑ Ji ∈ π.boxes, vol Ji = vol J`. Note that in the usual case where
  `E = F = ℝ`, this equality holds in `(ℝ →L[ℝ] ℝ)` which is isomorphic
  to `ℝ`.

  Given a tagged partition `π` of `I`, the integral sum of `f` over `π` w.r.t.
  `vol` is the sum of `vol J (f (π.tag J))` over all boxes `J` of `π`,
  where `π.tag J` is the tag (sample point) associated with box `J`.

- `y : F`. The value of the integral.
  `HasIntegral I l f vol y` is a asserting that `y` is the limit of Riemann-style
  integral sums. Following the design of `HasSum`/`tsum` for infinite sums,
  `HasIntegral` is a predicate; the companion `BoxIntegral.integral`
  returns a vector satisfying the predicate,
  or zero if the function is not integrable.

-/

#print BoxIntegral.IntegrationParams.Riemann
-- def BoxIntegral.IntegrationParams.Riemann : BoxIntegral.IntegrationParams :=
-- { bRiemann := true, bHenstock := true, bDistortion := false }


def HasRiemannIntegral (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (y : ℝ) :=
  BoxIntegral.HasIntegral (ι := Fin 1)
    (I := BoxIntegral.Box.mk (fun _ => a) (fun _ => b) (fun _ => hab))
    (l := BoxIntegral.IntegrationParams.Riemann)
    (f := fun x => f (x 0))
    (vol := BoxIntegral.BoxAdditiveMap.volume)
    (y := y)

end Ex3
