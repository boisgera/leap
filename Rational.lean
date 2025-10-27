import Mathlib

structure Rational where
  num : Int
  den : Nat
  den_neq_zero : den ≠ 0
  gcd_eq_one : Int.gcd num den = 1

def Rational.toString (r : Rational) : String :=
  if r.den = 1 then
    ToString.toString r.num
  else
    s!"{r.num} / {r.den}"

instance : ToString Rational where
  toString := Rational.toString

def zero := {
  num := 0
  den := 1
  den_neq_zero := by decide
  gcd_eq_one := by decide
  : Rational
}

#eval zero -- 0

def half := {
  num := 1,
  den := 2,
  den_neq_zero := by decide,
  gcd_eq_one := by decide,
  : Rational
}

#eval half -- 1 / 2

def Rational.add (r s : Rational) : Rational :=
  let n := r.num * s.den + r.den * s.num
  let d := r.den * s.den
  let num := n / (Int.gcd n d)
  let den := d / (Int.gcd n d)
  {
    num := num
    den := den
    den_neq_zero := sorry
    gcd_eq_one := sorry
  }

instance : Add Rational where
  add := Rational.add
