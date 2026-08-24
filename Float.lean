import Mathlib
import Batteries
import RyuLean4

-- More than enough digits to get the best repr of pi as Float.
def pi := 3.14159265358979323846264338327950288419716939937510582097494459230781
def zeroDotThree := 0.3

#eval pi
-- 3.141593

-- Experimentally, we could have used the atan to compute the same pi float.
#eval pi == 4 * Float.atan 1
-- true

-- Exact value of "pi-as-a-Float"
#eval pi.toStringFull |> IO.println
-- 3.141592653589793115997963468544185161590576171875

-- Exact value of pi
-- 3.141592653589793238462643383279502884197169399375....

#eval zeroDotThree
-- 0.300000

#eval zeroDotThree.toStringFull |> IO.println
-- 0.299999999999999988897769753748434595763683319091796875

#eval 0.1 + 0.2
-- 0.300000

#eval (0.1 + 0.2).toStringFull |> IO.println
-- 0.3000000000000000444089209850062616169452667236328125


/-!
Bit-level exploration
--------------------------------------------------------------------------------
-/

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

def sign (float : Float) : Float :=
  if float.toBits >>> 63 == 0 then 1.0 else -1.0

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
A float which is the number to be scaled+signed?
-/

#eval pi
-- 3.141593

#eval exponent pi
-- 1

/--
2^52 times the float
-/
def shift (f : Float) : Nat :=
  f
    -- |>.abs -- get rid of the sign
    -- |> (· * 2.0 ^ (- (exponent f).toInt64.toFloat)) -- remove the exponent
    |> fun x => x * 2.0 ^ 52 -- shift to get a natural number
    |>.toUInt64.toNat -- convert

/-!
TODO: get ALL the decimal digits associated to the mantissa (/significand).
How? Easy multiply by 5^52 so that we get mantissa * 10^52
-/

#eval pi
-- 3.141593

#eval exponent pi
-- 1

/--
2^52 times the float, as an Int
-/
def sihft (f : Float) : Int :=
  f
    -- |>.abs -- get rid of the sign
    -- |> (· * 2.0 ^ (- (exponent f).toInt64.toFloat)) -- remove the exponent
    |> fun x => x * 2.0 ^ 52 -- shift to get a natural number
    |>.toInt64.toInt -- convert

/-!
TODO: get ALL the decimal digits associated to the mantissa (/significand).
How? Easy multiply by 5^52 so that we get mantissa * 10^52
-/

#eval (sihft pi) * 5 ^ 52
-- 31415926535897931159979634685441851615905761718750000

#eval pi |> (· * 2.0 ^ 52) |>.toInt64.toInt |> fun x : Int => x * 5 ^ 52
-- 31415926535897931159979634685441851615905761718750000

theorem uint64_shift_right_63 (u : UInt64) :
    (u >>> 63) = 0 ∨ (u >>> 63) = 1 := by bv_decide


/-!
Hadoken!
--------------------------------------------------------------------------------
-/

def Float.toF64 (f : Float) : F64 :=
  let bits := f.toBits
  let sign : Bool := (bits >>> 63) == 1
  let biasedExp : Fin 2048 := bits
    |>.toNat
    |> (· &&& 2 ^ 63 - 1)
    |> (· >>> 52)
    |> Fin.ofNat (n := 2048)
  let mantissa : Fin (2 ^ 52) := bits
    |>.toNat
    |> (· &&& 2 ^ 52 - 1)
    |> Fin.ofNat (n := 2 ^ 52)
  { sign, biasedExp, mantissa }

#eval pi.toF64
-- { sign := false, biasedExp := 1024, mantissa := 2570638124657944 }

#check F64.isFinite
-- F64.isFinite (x : F64) : Prop

#print F64.isFinite
-- fun x => x.classify =
--   FloatClass.zero ∨
--   x.classify = FloatClass.subnormal ∨
--   x.classify = FloatClass.normal

#synth ∀ x : F64, Decidable x.isFinite

#synth Decidable (F64.isFinite pi.toF64)

#check Ryu.ryu
-- Ryu.ryu (x : F64) (hfin : x.isFinite) : Decimal

#check Decimal.format
-- Decimal.format (d : Decimal) : String

#eval Ryu.ryu pi.toF64 (hfin := by decide) |>.format |> IO.println
-- 3.141592653589793e0

#eval Ryu.ryu zeroDotThree.toF64 (hfin := by decide) |>.format |> IO.println
-- 3e-1

#eval Ryu.ryu (0.1 + 0.2).toF64 (hfin := by decide) |>.format |> IO.println
-- 3.0000000000000004e-1

-- TODO: make a Float.toRyu (or similar) that special-cases the non-finite stuff
-- to give a string in any case.



/-!
Radix Rationals
--------------------------------------------------------------------------------
-/

-- Rationals of the form mantissa × base ^ exponent.
-- Nota: when in canonical form, the mantissa is 0 or not a multiple of base
-- (force the exponent to be "maximal" somehow) ; think of it more, given
-- that the exponent can be non-positive (which is necessary) or negative
-- (which is useful to limit the memory footprint)
structure RadixRat (base : Nat) where
  -- the rational is mantissa * base ^ exponent
  mantissa : Int
  exponent : Int

-- Nota : having neg_exponent : Nat instead of exponent would be as expressive
-- but less convenient and would have a larger memory footprint for some large
-- powers of the base.

abbrev DyadicRat := RadixRat 2
abbrev DecimalRat := RadixRat 1

-- Nota: default argument value to avoid an auxiliary recursive function
-- TODO: work on a version with proven termination? At the very least we
-- should have some extra assumption on the argument (m >= 2 to start with,
-- then n ≥ 1, etc.)
-- At the very least, we can question what kind of assumptions is necessary
-- to get the termination ; we could add those assumptions, even if we don't
-- want to make the effort to remove the partial.
partial def maxPow (m n : Nat) (p : Nat := 0) : Nat :=
  if (n % m == 0) then
    maxPow m (n / m) (p := p + 1)
  else
    p

#eval maxPow 2 16 -- 16 = 2 ^ 4
-- 4

#eval maxPow 2 100 -- 100 = 2 ^ 2 * 5 ^ 2
-- 2

#eval maxPow 2 7 -- 7 = 7
-- 0

theorem div_pos_of_dvd (m n : Nat) (hm : 2 ≤ m) (hn : 0 < n) (hmod : n % m = 0) :
    0 < n / m := by
  have m_le_n : m ≤ n := by
    by_contra h
    push Not at h
    have := Nat.mod_eq_of_lt h   -- n % m = n
    grind
  exact Nat.div_pos m_le_n (by grind)

def maxPow' (m n : Nat) (p : Nat := 0) (hm : m >= 2) (hn : n > 0) : Nat :=
  if m_div_n : n % m = 0 then
    maxPow' m (n / m) (p + 1) hm (show n / m > 0 from div_pos_of_dvd m n hm hn m_div_n)
  else
    p
termination_by n
decreasing_by
  apply Nat.div_lt_self
  repeat grind


def RadixRat.canonicalize {b} (r : RadixRat b) : RadixRat b :=
  let pow := maxPow b r.mantissa.natAbs
  {
    mantissa := r.mantissa / b ^ pow,
    exponent := r.exponent + (Int.ofNat pow)
  }

#eval {mantissa := 100, exponent := 0 : DyadicRat} |>.canonicalize
-- { mantissa := 25, exponent := 2 }

#eval {mantissa := 256, exponent := 8 : DyadicRat} |>.canonicalize
-- { mantissa := 1, exponent := 16 }

def DyadicRat.ofFloat (f : Float) : DyadicRat :=
  let bits := f.toBits.toNat
  let exponent : Int := -- unbiased exponent
    bits
    |> (· &&& 2^63 - 1) -- zero the sign bit
    |> (· >>> 52)       -- shift the exponent down and trash the mantissa
    |> Int.ofNat
    |> (· - 1023 - 52)  -- debias & compensate for mantissa shift

  dbg_trace (bits &&& (2^52 - 1)) -- should be 0 for f := 1.0

  let unsigned_mantissa :=
    if f == 0 then
      0
    else
      (bits &&& 2^52 - 1) -- d0...d52, the fractional part f of the mantissa
        |> (· + 2^52)     -- 1d0...d52 aka 1.f × b^52
  let isNeg := bits >= 2^63
  let mantissa :=
    unsigned_mantissa
    |> Int.ofNat
    |> fun n => if isNeg then -n else n
  {mantissa, exponent}

#eval DyadicRat.ofFloat 1.0
-- { mantissa := 4503599627370496, exponent := -52 }


#eval DyadicRat.ofFloat 3.14
-- { mantissa := 7070651414971679, exponent := -51 }

theorem two_divides_ten : 2 ∣ 10 := by
  simp [Dvd.dvd] -- ∃ c, 10 = 2 * c
  use 5

def RadixRat.coerce
    {m n : Nat} (m_divides_n : m ∣  n) (r : RadixRat m) : RadixRat n :=
  let _ := m_divides_n
  let k := n / m
  if r.exponent >= 0 then
    {
      mantissa := r.mantissa * m ^ r.exponent.natAbs,
      exponent := 0,
    }
  else
      {
      mantissa := r.mantissa * k ^ r.exponent.natAbs,
      exponent := r.exponent
      : RadixRat n
    }

#print BEq
-- class BEq.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   BEq.beq : α → α → Bool
-- constructor:
--   BEq.mk.{u} {α : Type u} (beq : α → α → Bool) : BEq α

def RadixRat.beq {m} (r s : RadixRat m) : Bool :=
  let cr := r.canonicalize
  let cs := s.canonicalize
  cr.mantissa == cs.mantissa && cr.exponent == cs.exponent

instance {m} : BEq (RadixRat m) where
  beq := RadixRat.beq

def RadixRat.toString {b} (r : RadixRat b) : String :=
  let r := r.canonicalize
  let exponentString :=
    if r.exponent ≥ 0 then
      s!"{r.exponent}"
    else
      s!"({r.exponent})"
  s!"{r.mantissa} * {b} ^ {exponentString}"

instance {b} : ToString (RadixRat b) where
  toString := RadixRat.toString

#eval DyadicRat.ofFloat 3.14
-- 7070651414971679 * 2 ^ (-51)

#eval ({ mantissa := 100, exponent := 0} : DyadicRat)
-- 25 × 2 ^ 2

#eval 1 + 1

-- TODO: coerce to Rat (properly, with a typeclass!). We *could* define binary
-- equality by decidable equality of the Rats?

-- TODO : expose the design of Rat which containes two proposition, but who
-- mostly "get out of the way" since we can coerce integers without any proof
-- and operations such as '/' that are already implemented carry the burden
-- of the proofs. We *could* do something similar for RadixRat

-- TODO : get a float, coerce it to DyadicRat (manage special cases),
-- then to DecimalRat, canonicalize, then truncate to 17 digits and
-- display appropriately.

def Float.toScientificNotation (f : Float) (precision : Nat := 17) : String :=
  -- TODO: handle special cases : ± inf, nan, -0.0 (?)
  let df :=
    f
    |> DyadicRat.ofFloat
    |> dbgTraceVal
    |>.coerce (n := 10) (show 2 ∣ 10 by grind)
  dbg_trace df
  let mabs := df.mantissa.natAbs |> ToString.toString
  let numDigits := mabs.length
  let e := df.exponent + (numDigits - 1)
  let m := (mabs.take 1).toString ++ "." ++ (mabs.drop 1)
  let m_trunc := m.take (precision + 1) -- round towards zero
  let sign := if df.mantissa < 0 then "-" else ""
  s!"{sign}{m_trunc}e{e}"

#eval Float.toScientificNotation 3.14
-- "3.1400000000000001e-102" WRONG

#eval Float.toScientificNotation 0.3
-- "2.9999999999999998e-1"

#eval Float.toScientificNotation (0.1 + 0.2)
-- "3.0000000000000004e-1"

#eval Float.toScientificNotation (-0.3)
-- -2.9999999999999998e-1

#eval Float.toScientificNotation 0.0001

-- #eval Float.toScientificNotation 0.0 runs forever?
-- where does it hang?

-- TODO:
-- - [X] float to DyadicRat
-- - canonicalization
-- - BEq and other typeclasses
-- - convert a DyadicRat to a DecimalRat
-- -

-- TODO: convert Scientific 2 to Scientific 10.

#eval Float.toScienticNotation 3.14
-- "2.0806951639991532e-324" -- *cough, cough* 🪲

-- Q: is the repr easy once we have the float components?

-- instance (priority := high) : ToString Float where
--   toString := sorry -- patchedToString

-- instance (priority := high) : Repr Float where
--   reprPrec f prec :=
--     if f < 0 then
--       Repr.addAppParen (Std.Format.text (toString f)) prec
--     else
--       Std.Format.text (toString f)

#eval 3.14e20
-- 314e18
