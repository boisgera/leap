import Mathlib

-- Without conv
example (a b c : ℝ) : a * (b * c) = a * (c * b) := by
  have : b * c = c * b := mul_comm b c
  -- (fun x => a * x) (b * c) = (fun x => a * x) (c * b)
  have h := congrArg (a * ·) this
  simp only at h
  exact h

-- With conv
example (a b c : ℝ) : a * (b * c) = a * (c * b) := by
  conv =>
    rhs
    congr
    . skip
    . rw [mul_comm c b]

-- Without conv
example (g : ℝ -> ℝ) :
(∀ (x : ℝ), g (x + 1) = g x + 3)
-> g 0 = 5
-> g 1 = 8 := by
  intro g_succ g_zero
  have h := g_succ 0
  rw [g_zero] at h
  norm_num at h
  exact h

-- With conv
example (g : ℝ -> ℝ) :
(∀ (x : ℝ), g (x + 1) = g x + 3)
-> g 0 = 5
-> g 1 = 8 := by
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
