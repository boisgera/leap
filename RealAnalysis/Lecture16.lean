import Mathlib

set_option pp.showLetValues true

-- Need a generic version wrt ℚ or ℝ?

#print Cauchy
-- def Cauchy.{u} : {α : Type u} → [uniformSpace : UniformSpace α] →
--     Filter α → Prop :=
--   fun {α} [UniformSpace α] f => f.NeBot ∧ f ×ˢ f ≤ uniformity α

namespace K -- avoid collisions wrt redefinitions

def Cauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ p ≥ m, |a n - a p| ≤ ε

def SeqLim (a : ℕ → ℝ) (ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |a n - ℓ| ≤ ε

def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ ℓ, SeqLim a ℓ


-- Jump in, have a look at how real numbers are constructed?
-- Mmmm, we're going to have issue since it uses the "true" definition of
-- Cauchy of Mathlib that is rather complex.
theorem seqConv_of_cauchy {a : ℕ → ℝ} : Cauchy a → SeqConv a := by
  admit

end K

-- Need to study what is done in
-- https://github.com/AlexKontorovich/RealAnalysisGame/blob/main/Game/Levels/L15Levels/L01_check.lean
-- what are the students actually doing themselves in these lectures?


-- Theorem (Conv of IsCauchy): If a sequence a : N → Q satisfies
-- IsCauchy a, then SeqConv a holds – that is, the sequence converges.
-- Given that such a limit exists, we can define it explicitly:

-- Definition (Real of CauSeq): This takes IsCauchy a (for a : N → Q)
-- and returns the real number that a converges to.
-- This real number does what we want:

-- Theorem (SeqLim of Real of Cau): If ha : IsCauchy (a : N→Q),
-- then SeqLim a (Real_of_CauSeq ha) holds – that is, the sequence a converges
-- to the real number defined by Real_of_CauSeq.
