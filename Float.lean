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

#eval (shift pi) * 5^52
-#eval pi
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

-- def sign' (float : Float) : Float :=
--   match uint64_shift_right_63 float.toBits with
--   | Or.inl h => by
--       simp [h]
--       exact 1.0
--   | Or.inr h => by
--       simp [h]
--       exact -1.0

-- -- Step 1: as before
-- def decompose (bits : UInt64) : Bool × Int × Nat :=
--   let sign := (bits >>> 63) &&& 1 == 1
--   let biasedExp := (bits >>> 52) &&& 0x7FF
--   let M := (bits &&& ((1 <<< 52) - 1)).toNat
--   if biasedExp == 0 then
--     (sign, -1022, M)
--   else
--     (sign, biasedExp.toNat - 1023, M + (1 <<< 52))

-- -- Step 2: turn (mantissaFull, e) into an exact (N, d) with value = N * 10^(-d)
-- def toExactDecimal (mantissaFull : Nat) (e : Int) : Nat × Nat :=
--   let k := e - 52
--   if k ≥ 0 then
--     (mantissaFull * 2 ^ k.toNat, 0)          -- integer, no fractional digits
--   else
--     let negk := (-k).toNat
--     (mantissaFull * 5 ^ negk, negk)          -- N / 10^negk, exact

-- -- Step 3+4: round N's digit string to 17 sig figs, track exponent shift
-- def roundAndLocate (N d : Nat) : String × Int :=
--   let digits := toString N
--   let L := digits.length
--   -- exponent of leading digit before rounding: value = N * 10^(-d)
--   let exp10 : Int := (L : Int) - (d : Int) - 1
--   let (rounded, grew) := roundToSigDigits digits 17
--   (rounded, if grew then exp10 + 1 else exp10)

-- -- Full pipeline
-- def floatToRepr17g (bits : UInt64) : String :=
--   let (sign, e, mantissaFull) := decompose bits
--   if mantissaFull == 0 then
--     (if sign then "-0" else "0")
--   else
--     let (N, d) := toExactDecimal mantissaFull e
--     let (roundedDigits, exp10) := roundAndLocate N d
--     formatG sign roundedDigits exp10

-- Increment a decimal digit string by 1 at the last position, propagating carry.
-- Returns (result, grew) where grew=true if the string got one digit longer
-- (e.g. "999" -> "1000").
def incrementDecimalString (s : String) : String × Bool :=
  let digits := s.toList
  let rec go : List Char → List Char × Bool
    | [] => ([], true)  -- ran off the front: carry out
    | c :: rest =>
      if c == '9' then
        let (rest', carried) := go rest
        if carried then ('0' :: rest', true) else (c :: rest', false)
      else
        (Char.ofNat (c.toNat + 1) :: rest, false)
  -- process from the right: reverse, go, reverse back
  let (revResult, carryOut) := go digits.reverse
  let result := revResult.reverse
  if carryOut then
    (String.ofList ('1' :: result), true)
  else
    (String.ofList result, false)

-- Round a decimal digit string (no leading zeros, nonempty) to `keep`
-- significant digits, round-half-to-even. Returns (roundedDigits, grew)
-- where grew=true means the rounding caused a carry that grew the digit
-- count (so caller must bump the decimal exponent by 1).

def roundToSigDigits (digits : String) (keep : Nat) : String × Bool :=
  if digits.length ≤ keep then
    (digits, false)
  else
    let kept := (digits.take keep).toString.toList
    let rest := (digits.drop keep).toString.toList
    let firstDropped := rest.headD '0'
    let firstDigit := firstDropped.toNat - '0'.toNat
    let restIsAllZero := rest.tail.all (· == '0')
    let lastKeptDigit := (kept.getLastD '0').toNat - '0'.toNat
    let roundUp :=
      if firstDigit > 5 then true
      else if firstDigit < 5 then false
      else if !restIsAllZero then true
      else lastKeptDigit % 2 == 1
    if roundUp then
      let (incremented, grew) := incrementDecimalString (String.ofList kept)
      if grew then (incremented.dropEnd 1 |>.toString, true) else (incremented, false)
    else
      (String.ofList kept, false)

-- -- Step 1: decompose bits into sign, unbiased exponent, full mantissa (with implicit bit)
-- def decompose (bits : UInt64) : Bool × Int × Nat :=
--   let sign := (bits >>> 63) &&& 1 == 1
--   let biasedExp := (bits >>> 52) &&& 0x7FF
--   let M := (bits &&& ((1 <<< 52) - 1)).toNat
--   if biasedExp == 0 then
--     (sign, -1022, M)
--   else
--     (sign, biasedExp.toNat - 1023, M + (1 <<< 52))

-- -- Step 2: exact value = N * 10^(-d)
-- def toExactDecimal (mantissaFull : Nat) (e : Int) : Nat × Nat :=
--   let k := e - 52
--   if k ≥ 0 then
--     (mantissaFull * 2 ^ k.toNat, 0)
--   else
--     let negk := (-k).toNat
--     (mantissaFull * 5 ^ negk, negk)

-- -- Step 3+4: round to 17 sig digits, compute exponent of leading digit
-- def roundAndLocate (N d : Nat) : String × Int :=
--   let digits := toString N
--   let L := digits.length
--   let exp10 : Int := (L : Int) - (d : Int) - 1
--   let (rounded, grew) := roundToSigDigits digits 17
--   (rounded, if grew then exp10 + 1 else exp10)

-- -- helper: strip trailing zeros, keep at least one digit
-- def stripTrailingZeros (s : String) : String :=
--   let trimmed := s.dropRightWhile (· == '0')
--   if trimmed.isEmpty then "0" else trimmed

-- -- helper: pad exponent to at least 2 digits, printf-style
-- def padExp (n : Nat) : String :=
--   let s := toString n
--   if s.length < 2 then String.mk (List.replicate (2 - s.length) '0') ++ s else s

-- -- Step 5: %g-style formatting
-- def formatG (sign : Bool) (roundedDigits : String) (exp10 : Int) : String :=
--   let digits := stripTrailingZeros roundedDigits
--   let body :=
--     if exp10 < -4 || exp10 ≥ 17 then
--       let intPart := (digits.take 1).toString
--       let fracPart := (digits.drop 1).toString
--       let mantissaStr := if fracPart.isEmpty then intPart else intPart ++ "." ++ fracPart
--       mantissaStr ++ "e" ++ (if exp10 ≥ 0 then "+" else "-") ++ padExp exp10.natAbs
--     else if exp10 ≥ 0 then
--       let intLen := (exp10 + 1).toNat
--       let padded :=
--         if digits.length < intLen then
--           digits ++ String.mk (List.replicate (intLen - digits.length) '0')
--         else digits
--       let ip := (padded.take intLen).toString
--       let fp := (padded.drop intLen).toString
--       if fp.isEmpty then ip else ip ++ "." ++ fp
--     else
--       "0." ++ String.mk (List.replicate ((-exp10).toNat - 1) '0') ++ digits
--   (if sign then "-" else "") ++ body

-- -- Full pipeline
-- def floatToRepr17g (bits : UInt64) : String :=
--   let biasedExp := (bits >>> 52) &&& 0x7FF
--   let M := (bits &&& ((1 <<< 52) - 1)).toNat
--   let sign := (bits >>> 63) &&& 1 == 1
--   if biasedExp == 0x7FF then
--     if M == 0 then (if sign then "-inf" else "inf") else "nan"
--   else if biasedExp == 0 && M == 0 then
--     (if sign then "-0" else "0")
--   else
--     let (_, e, mantissaFull) := decompose bits
--     let (N, d) := toExactDecimal mantissaFull e
--     let (roundedDigits, exp10) := roundAndLocate N d
--     formatG sign roundedDigits exp10

#eval 67.0
-- 0

#eval 12.0
-- 0

#eval some (1.5)

#eval -1.5


-- def leadingZeros (s : String) : Nat :=
--   let rec lz (cs : List Char) : Nat :=
--     match cs with
--     | '0' :: cs => 1 + (lz cs)
--     | _ => 0
--   lz s.toList

-- def trailingZeros (s : String) : Nat :=
--   s.toList |>.reverse |> String.ofList |> leadingZeros

-- def patchLarge (s : String) :=
--   if s == "0" then
--     s
--   else if s.contains '.' then
--       s
--   else -- now we can deal with large entire numbers
--     let n := trailingZeros s
--     let cs := String.toList s
--     let cs' := cs.take (cs.length - n)
--     -- Not perfect yet, e.g. may produce 314e18
--     let exp := n + (cs'.length - 1)
--     let cs'' := cs'.head! :: ['.'] ++ (cs'.drop 1)
--     cs'' |> String.ofList |> (· ++ s!"e{exp}")

-- -- TODO: patchSmall

-- -- TODO: patchTooManyDigits

-- def patchedToString (f : Float) : String :=
--   f.toStringFull
--     |> patchLarge

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
    |> (· - 1023)       -- debias
  let unsigned_mantissa :=
    if f == 0 then
      0
    else
      (bits &&& 2^53 - 1) -- b0...b52, the fractional part f of the mantissa
        |> (· + 2^53)     -- 1b0...b52 aka 1.f × 2^52
        |> (· <<< 1023)   -- compensate for the bias in the exponent
  let isNeg := bits >= 2^63
  let mantissa :=
    unsigned_mantissa
    |> Int.ofNat
    |> fun n => if isNeg then -n else n
  {mantissa, exponent}

theorem two_divides_ten : 2 ∣ 10 := by
  simp [Dvd.dvd] -- ∃ c, 10 = 2 * c
  use 5

def RadixRat.coerce
    {m n : Nat} (m_divides_n : m ∣  n) (r : RadixRat m) : RadixRat n :=
  let k := n / m
  if r.exponent >= 0 then
    {
      mantissa := r.mantissa * (k ^ r.exponent.natAbs),
      exponent := r.exponent
      : RadixRat n
    }.canonicalize
  else
    {
      mantissa := sorry,
      exponent := sorry,
    }




-- TODO:
-- - [X] float to DyadicRat
-- - canonicalization
-- - BEq and other typeclasses
-- - convert a DyadicRat to a DecimalRat
-- -

-- TODO: convert Scientific 2 to Scientific 10.

#eval Float.scientific 3.14

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
