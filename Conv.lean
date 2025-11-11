import Mathlib

example (g : ℝ -> ℝ) : (∀ (x : ℝ), g (x + 1) = g x + 3) -> g 0 = 5 -> g 1 = 8 := by
  intro g_succ g_zero
  specialize g_succ 0 -- g (0 + 1) = g 0 + 3
  have h : g 1 = g 0 + 3 := by
    rw [<- g_succ] -- g 1 = g (0 + 1)
    conv =>
      rhs
      congr
      norm_num
  rw [h]
  rw [g_zero]
  norm_num
