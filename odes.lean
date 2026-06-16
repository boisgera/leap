import Mathlib

def VectorField (n : ℕ) : Type := (Float) → (Fin n → Float) → (Fin n → Float)

def lotkaVolterra (α β γ δ : Float) (t : Float) (x : Fin 2 → Float) :
  (Fin 2 → Float) :=
  let _ := t
  let x0 := x 0
  let x1 := x 1
  let dx0 := α * x0 - β * x1
  let dx1 := γ * x0 + δ * x1
  ![dx0, dx1]

def step {n : ℕ}
    (f : VectorField n)
    (t : Float) (x : Fin n → Float) (dt : Float) :
    (Fin n → Float) :=
  let dx := dt • (f t x)
  x + dx

def solve {n : ℕ} (f : VectorField n) (x0 : Fin n → Float) (t0 t1 dt : Float)
    : List (Float × (Fin n → Float)) := Id.run do
  let mut txs := [(t0, x0)]
  let mut t := t0
  let mut x := x0
  while t < t1 do
    x := step f t x dt
    t := t + dt
    txs := (t, x) :: txs
  return txs.reverse

#eval solve (lotkaVolterra 1.0 1.0 1.0 1.0) ![1.0, 1.0] 0.0 1.0 0.1
-- [(0.000000, ![1.000000, 1.000000]),
--  (0.100000, ![1.000000, 1.200000]),
--  (0.200000, ![0.980000, 1.420000]),
--  (0.300000, ![0.936000, 1.660000]),
--  (0.400000, ![0.863600, 1.919600]),
--  (0.500000, ![0.758000, 2.197920]),
--  (0.600000, ![0.614008, 2.493512]),
--  (0.700000, ![0.426058, 2.804264]),
--  (0.800000, ![0.188237, 3.127296]),
--  (0.900000, ![-0.105669, 3.458849]),
--  (1.000000, ![-0.462121, 3.794168]),
--  (1.100000, ![-0.887750, 4.127372])]


-- TODO: generalisation with partial solution.
namespace F
partial def solve_aux
    {n : ℕ}
    (f : VectorField n) (txs : List (Float × (Fin n → Float))) (t1 dt: Float) :
    List (Float × (Fin n → Float)) :=
    match txs with
    | [] => panic! "unreachable"
    | (t, x) :: _ =>
        if t < t1 then
          let txs := (t + dt, step f t x dt):: txs
          solve_aux f txs t1 dt
        else
          txs.reverse

def solve
    {n : ℕ}
    (f : VectorField n) (x0 : Fin n → Float) (t0 t1 dt : Float)
    : List (Float × (Fin n → Float)) :=
  solve_aux f [(t0, x0)] t1 dt

#eval solve (lotkaVolterra 1.0 1.0 1.0 1.0) ![1.0, 1.0] 0.0 1.0 0.1
-- [(0.000000, ![1.000000, 1.000000]),
--  (0.100000, ![1.000000, 1.200000]),
--  (0.200000, ![0.980000, 1.420000]),
--  (0.300000, ![0.936000, 1.660000]),
--  (0.400000, ![0.863600, 1.919600]),
--  (0.500000, ![0.758000, 2.197920]),
--  (0.600000, ![0.614008, 2.493512]),
--  (0.700000, ![0.426058, 2.804264]),
--  (0.800000, ![0.188237, 3.127296]),
--  (0.900000, ![-0.105669, 3.458849]),
--  (1.000000, ![-0.462121, 3.794168]),
--  (1.100000, ![-0.887750, 4.127372])]]

end F
