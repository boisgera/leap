import Mathlib
import Batteries.Lean.Float

def pi := 4 * Float.atan 1

#eval pi
-- 3.141593

#eval pi.toStringFull |> IO.println
-- 3.141592653589793115997963468544185161590576171875

-- "True" value of pi
-- 3.141592653589793238462643383279502884197169399375...

def pi_binary := pi.toBits

#check pi_binary
-- pi_binary : UInt64

#eval pi_binary
-- 4614256656552045848

#eval pi_binary >>> 63
-- 0

#eval ((1.0).toBits : UInt64) >>> 63
-- 0

#eval ((-1.0).toBits : UInt64) >>> 63
-- 1

-- The bit fiddling is not necessary here.
def sign (float : Float) : Float :=
  if float.toBits >>> 63 == 0 then 1.0 else -1.0

-- Is the bit fiddling necessary?
def exponent (float : Float) : Int :=
  float.toBits
    |> fun (bits : UInt64) => (bits &&& 2^63 - 1 : UInt64)
    |> fun (bits : UInt64) => (bits >>> 52)
    |>.toNat
    |> Int.ofNat
    |> (· - 1023)

#eval exponent pi
-- 1

#eval exponent 0.5
-- -1

#eval exponent 1.0
-- 0

#eval exponent 2.0
-- 1

#eval exponent 10.0
-- 3

/-!
TODO: mantissa (no idea what the signature should be actually)
Return a natural number which should be divided by 2^52?
Makes sense ... Do I need the bit fiddling for that?
Nope
-/

/--
2^52 times the fractional part, as a Nat
-/
def mantissa (f : Float) : Nat :=
  f
    |>.abs
    |> (· * 2.0 ^ (- (exponent f).toInt64.toFloat))
    |> (· * 2.0 ^ 52)
    |>.toUInt64.toNat

/-!
TODO: get ALL the decimal digits associated to the mantissa.
How?
-/

theorem uint64_shift_right_63 (u : UInt64) :
    (u >>> 63) = 0 ∨ (u >>> 63) = 1 := by bv_decide

-- def sign' (float : Float) : Float :=
--   match uint64_shift_right_63 float.toBits with
--   | Or.inl h => by
--       simp [h]
--       exact 1.0
--   | Or.inr h => by
--       simp [h]
--       exact -1.0
