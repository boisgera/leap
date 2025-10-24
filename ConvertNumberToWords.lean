import Mathlib

def units := [
  "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"
]

#eval do assert! units.length = 10

def teens := [
  "ten", "eleven", "twelve", "thirteen", "forteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen"
]

#eval do assert! teens.length = 10

def tens := [
  "zero", "ten", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"
]

#eval do assert! tens.length = 10

#check Nat.mod_lt
-- Nat.mod_lt (x : ℕ) {y : ℕ} (hy : 0 < y) : x % y < y

def convertUnits (n : Nat) : String :=
  let n := n % 10
  have : n < units.length := by
    apply Nat.mod_lt
    decide
  units[n]

#eval do assert! convertUnits 1 = "one"
#eval do assert! convertUnits 9 = "nine"
#eval do assert! convertUnits 456 = "six"

#check Nat.div_lt_iff_lt_mul
-- Nat.div_lt_iff_lt_mul {k x y : ℕ} (Hk : 0 < k) : x / k < y ↔ x < y * k

def convertTens (n : Nat) : String :=
  let n := (n % 100) / 10
  have h : n < tens.length := by
    rename_i n'
    have h': n' % 100 < 100 := by
      apply Nat.mod_lt; decide
    set p := n' % 100 with hp
    show n' % 100 / 10 < tens.length
    rw [<- hp]
    clear n
    rw [show tens.length = 10 from by decide]
    clear hp
    generalize p = p' at *
    clear p n'
    rw [Nat.div_lt_iff_lt_mul]
    . simp
      assumption
    . decide
  tens[n]

#eval do assert! convertTens 60 = "sixty"
#eval do assert! convertTens 78 = "seventy"
#eval do assert! convertTens 1000092 ="ninety"

#check pow_succ
-- pow_succ.{u_2} {M : Type u_2} [Monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a

-- For fun, a general version
theorem theo (b k n : Nat) : (0 < b) -> n % b ^ (k + 1) / b ^ k < b := by
  intro b_pos
  have l₁ : n % b ^ (k + 1) / b ^ k < b ↔ n % b ^ (k + 1) < b * b ^ k :=
    have b_k_pos := Nat.pow_pos (n := k) b_pos
    Nat.div_lt_iff_lt_mul b_k_pos (k := b ^ k) (x := n % b ^ (k + 1)) (y := b)
  apply l₁.mpr
  clear l₁
  have l₂ : n % b^(k + 1) < b^(k + 1) := by
    apply Nat.mod_lt
    apply Nat.pow_pos
    exact b_pos
  rw [mul_comm, <- pow_succ]
  exact l₂

def convertHundred (n : Nat) : String :=
  let hundreds := n % 1000 / 100
  have : hundreds < 10 := by
    simp only [hundreds]
    have h := theo 10 2 n (show 0 < 10 from by decide)
    simp only [Nat.reduceAdd, Nat.reducePow] at h
    exact h
  s!"{convertUnits hundreds} hundred"

def convertUpTo999 (n : Nat) : String :=
  sorry

def convert := convertUpTo999

/-
Tests
-/


/--
three hundred and eight thousand
-/
#guard_msgs in
#eval convert 308000

/--
three hundred and sixty-nine thousand and ninety-seven
-/
#guard_msgs in
#eval convert 369697

/--
three hundred and seventy-nine thousand four hundred and one
-/
#guard_msgs in
#eval convert 379401
