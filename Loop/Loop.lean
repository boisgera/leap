import Mathlib

/-!

A certified version of Scicos/Simulink/Modelica/etc.

See also: https://zelus.di.ens.fr/

- limited to ODEs (at first?) and causal modelling. Ooooooor only
  discrete-time systems? Dunno, think about it. ODEs is richer.

- do we handle time as a special construct?

- define a collection of concrete "blocks" and ways to connect them
(I guess that makes block a typeclass)

- think if the input/output are Reals or Floats

- Input/outputs are numbered? Named? Or are optional (external) "labels"

- Loop must prove that there is no "causal loop"! The "no-dep" between one
  entry and the other is determined automatically? Or provided by the user
  in general and provided automatically for blocks that are predefined?

- The main job of the library is to go from a graph/distributed spec of an
  ODE to the "f" and "g" of the global ODE

- Code generation for Python(/numpy or /pytorch) would be nice...

-/



/-!
Small test: prove that a function does not depend on some argument
-/

def f (x y : ℝ) : ℝ :=
  let _ := x
  y * y + 1

theorem f_isConstant : ∀ (x x' y : ℝ), f x y = f x' y := by
  intro x x' y
  simp [f]
