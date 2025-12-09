
import Mathlib

def f (x : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x₁, x₂) := x
  (x₁, x₂, x₁ + x₂)

def fLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) where
  toFun := f
  map_add' := by
    intro x y
    simp [f]
    ring
  map_smul' := by
    intro m x
    simp [f]
    ring

def f' (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  fun (n) =>
    match n with
    | 0 => x 0
    | 1 => x 1
    | 2 => x 0 + x 1

def f'' (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![x 0, x 1, x 0 + x 1] -- notation for finite functions

def f₃ (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  ![x 0, x 1, x 0 + x 1]

def fl' : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := fun x => ![x 0, x 1, x 0 + x 1]
  map_add' := by
    intro x y
    simp
    ring
  map_smul' := by
    intro m x
    simp
    ring

#eval fl' ![1.0, 2.0]
-- ![Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/),
--   Real.ofCauchy (sorry /- 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, ... -/),
--   Real.ofCauchy (sorry /- 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, ... -/)]

-- The implicit coercion from linear to "normal" function works
#eval fl' ![1.0, 2.0]
-- ![Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/),
--  Real.ofCauchy (sorry /- 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, ... -/),
--  Real.ofCauchy (sorry /- 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, ... -/)]

#check ContinuousLinearMap

def f_lin_cont : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  let f := fun x => ![x 0, x 1, x 0 + x 1]
  let f_lin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := {
    toFun := f
    map_add' := by intro x y ; simp [f] ; ring
    map_smul' := by intro m x ; simp [f] ; ring
  }
  let f_lin_cont : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) := {
    f_lin with
    cont := LinearMap.continuous_of_finiteDimensional f_lin
  }
  f_lin_cont

def f_lin_cont'' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  {
    toFun := fun x => ![x 0, x 1, x 0 + x 1]
    map_add' := by intro x y ; simp ; ring
    map_smul' := by intro m x ; simp ; ring
    : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)
  } |>.toContinuousLinearMap

def f_lin_cont''' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (
    {
    toFun := fun x => ![x 0, x 1, x 0 + x 1]
    map_add' := by intro x y ; simp ; ring
    map_smul' := by intro m x ; simp ; ring
    } : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)
  ) |>.toContinuousLinearMap
