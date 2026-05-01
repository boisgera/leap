import Mathlib

def isConstant {α} {β} (f : α → β) : Prop := ∀ x y : α, f x = f y

def f (_ : ℝ) := (1 : ℝ)

example : isConstant f := by
  rw [isConstant]
  intro x y
  simp only [f]
