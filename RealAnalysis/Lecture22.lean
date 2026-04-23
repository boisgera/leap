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
--   [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
--   [Fintype ι]
--   (I : BoxIntegral.Box ι) (l : BoxIntegral.IntegrationParams)
--   (f : (ι → ℝ) → E) (vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤) (y : F) : Prop

/-!
TODO: specialize to Riemann stuff in 1D, scalar-valued functions.
-/

end Ex3
