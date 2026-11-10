import Mathlib

/-!
# The Natural Number Game, without the game

All the levels of the Natural Number Game, as plain Lean exercises: replace each
`sorry` by a proof, with any tactic you like.

Statements and level titles come from https://github.com/leanprover-community/NNG4
(Apache-2.0), commit 09e8c33. Two differences with the original:

- addition, multiplication and power are real recursive definitions, not opaque
  functions with axioms, so `rfl`, `simp`, `decide`, etc. all work as usual;
- no tactic or lemma is locked: use whatever you want.

Named exercises are `theorem`s, so that later ones can use them.
-/

universe u

/-!
Definitions and given facts
--------------------------------------------------------------------------------
This is what the game gives you for free. Not exercises.
-/

/-- Our copy of the natural numbers. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving DecidableEq

attribute [pp_nodot] MyNat.succ

@[inherit_doc] local notation (priority := high) "ℕ" => MyNat

namespace MyNat

def ofNat : Nat → ℕ
  | .zero => zero
  | .succ n => succ (ofNat n)

instance {n : Nat} : OfNat ℕ n := ⟨ofNat n⟩

instance : Inhabited ℕ := ⟨0⟩

/-- Induction, with goals stated with `0` rather than `MyNat.zero`. -/
@[elab_as_elim, induction_eliminator]
protected def recAux {motive : ℕ → Sort u}
    (zero : motive 0)
    (succ : ∀ n, motive n → motive (MyNat.succ n)) : ∀ t, motive t
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

/-- Case analysis, with goals stated with `0` rather than `MyNat.zero`. -/
@[elab_as_elim, cases_eliminator]
protected def casesAux {motive : ℕ → Sort u}
    (zero : motive 0)
    (succ : ∀ n, motive (MyNat.succ n)) : ∀ t, motive t
  | .zero => zero
  | .succ n => succ n

theorem zero_eq_0 : MyNat.zero = 0 := rfl

theorem one_eq_succ_zero : (1 : ℕ) = succ 0 := rfl
theorem two_eq_succ_one : (2 : ℕ) = succ 1 := rfl
theorem three_eq_succ_two : (3 : ℕ) = succ 2 := rfl
theorem four_eq_succ_three : (4 : ℕ) = succ 3 := rfl

def add : ℕ → ℕ → ℕ
  | a, zero => a
  | a, succ d => succ (add a d)

instance : Add ℕ := ⟨add⟩

theorem add_zero (a : ℕ) : a + 0 = a := rfl
theorem add_succ (a d : ℕ) : a + succ d = succ (a + d) := rfl

def mul : ℕ → ℕ → ℕ
  | _, zero => 0
  | a, succ b => mul a b + a

instance : Mul ℕ := ⟨mul⟩

theorem mul_zero (a : ℕ) : a * 0 = 0 := rfl
theorem mul_succ (a b : ℕ) : a * succ b = a * b + a := rfl

def pow : ℕ → ℕ → ℕ
  | _, zero => 1
  | m, succ n => pow m n * m

instance : Pow ℕ ℕ := ⟨pow⟩

-- Exponents are `MyNat`s too.
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : MyNat) ($y : MyNat))

theorem pow_zero (m : ℕ) : m ^ 0 = 1 := rfl
theorem pow_succ (m n : ℕ) : m ^ succ n = m ^ n * m := rfl

/-- `a ≤ b` means that `b = a + c` for some `c`. -/
def le (a b : ℕ) : Prop := ∃ c : ℕ, b = a + c

instance : LE ℕ := ⟨le⟩

theorem succ_inj (a b : ℕ) (h : succ a = succ b) : a = b := MyNat.succ.inj h

theorem zero_ne_succ (a : ℕ) : 0 ≠ succ a := MyNat.noConfusion

def pred : ℕ → ℕ
  | zero => 37
  | succ n => n

theorem pred_succ (n : ℕ) : pred (succ n) = n := rfl

def is_zero : ℕ → Prop
  | zero => True
  | succ _ => False

theorem is_zero_zero : is_zero 0 = True := rfl
theorem is_zero_succ (n : ℕ) : is_zero (succ n) = False := rfl

/-!
Tutorial World
--------------------------------------------------------------------------------
-/

-- Level 1: The rfl tactic
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  sorry

-- Level 2: the rw tactic
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  sorry

-- Level 3: Numbers
example : 2 = succ (succ 0) := by
  sorry

-- Level 4: rewriting backwards
example : 2 = succ (succ 0) := by
  sorry

-- Level 5: Adding zero
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  sorry

-- Level 6: Precision rewriting
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  sorry

-- Level 7: add_succ
theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 := by
  sorry

-- Level 8: 2+2=4
example : (2 : ℕ) + 2 = 4 := by
  sorry

/-!
Addition World
--------------------------------------------------------------------------------
-/

-- Level 1: zero_add
theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry

-- Level 2: succ_add
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  sorry

-- Level 3: add_comm (level boss)
theorem add_comm (a b : ℕ) : a + b = b + a := by
  sorry

-- Level 4: add_assoc (associativity of addition)
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  sorry

-- Level 5: add_right_comm
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  sorry

/-!
Multiplication World
--------------------------------------------------------------------------------
-/

-- Level 1: mul_one
theorem mul_one (m : ℕ) : m * 1 = m := by
  sorry

-- Level 2: zero_mul
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  sorry

-- Level 3: succ_mul
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry

-- Level 4: mul_comm
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  sorry

-- Level 5: one_mul
theorem one_mul (m : ℕ) : 1 * m = m := by
  sorry

-- Level 6: two_mul
theorem two_mul (m : ℕ) : 2 * m = m + m := by
  sorry

-- Level 7: mul_add
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  sorry

-- Level 8: add_mul
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

-- Level 9: mul_assoc
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  sorry

/-!
Power World
--------------------------------------------------------------------------------
-/

-- Level 1: zero_pow_zero
theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  sorry

-- Level 2: zero_pow_succ
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  sorry

-- Level 3: pow_one
theorem pow_one (a : ℕ) : a ^ 1 = a := by
  sorry

-- Level 4: one_pow
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  sorry

-- Level 5: pow_two
theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  sorry

-- Level 6: pow_add
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry

-- Level 7: mul_pow
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  sorry

-- Level 8: pow_pow
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  sorry

-- Level 9: add_sq
theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  sorry

-- Level 10: Fermat's Last Theorem (true, but the game only offers it as a joke)
example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry

/-!
Implication World
--------------------------------------------------------------------------------
-/

-- Level 1: The `exact` tactic
example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  sorry

-- Level 2: `exact` practice.
example (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  sorry

-- Level 3: The `apply` tactic.
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  sorry

-- Level 4: succ_inj : the successor function is injective
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  sorry

-- Level 5: Arguing backwards
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  sorry

-- Level 6: intro
example (x : ℕ) : x = 37 → x = 37 := by
  sorry

-- Level 7: intro practice
example (x y : ℕ) : x + 1 = y + 1 → x = y := by
  sorry

-- Level 8: ≠
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  sorry

-- Level 9: zero_ne_succ
theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  sorry

-- Level 10: 1 ≠ 0
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  sorry

-- Level 11: 2 + 2 ≠ 5
example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  sorry

/-!
Advanced Addition World
--------------------------------------------------------------------------------
-/

-- Level 1: add_right_cancel
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  sorry

-- Level 2: add_left_cancel
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  sorry

-- Level 3: add_left_eq_self
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  sorry

-- Level 4: add_right_eq_self
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  sorry

-- Level 5: add_right_eq_zero
theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  sorry

-- Level 6: add_left_eq_zero
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  sorry

/-!
≤ World
--------------------------------------------------------------------------------
-/

-- Level 1: The `use` tactic
theorem le_refl (x : ℕ) : x ≤ x := by
  sorry

-- Level 2: 0 ≤ x
theorem zero_le (x : ℕ) : 0 ≤ x := by
  sorry

-- Level 3: x ≤ succ x
theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  sorry

-- Level 4: x ≤ y and y ≤ z implies x ≤ z
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  sorry

-- Level 5: x ≤ 0 → x = 0
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  sorry

-- Level 6: x ≤ y and y ≤ x implies x = y
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry

-- Level 7: Dealing with `or`
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  sorry

-- Level 8: x ≤ y or y ≤ x
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  sorry

-- Level 9: succ x ≤ succ y → x ≤ y
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  sorry

-- Level 10: x ≤ 1
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  sorry

-- Level 11: le_two
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  sorry

/-!
Advanced Multiplication World
--------------------------------------------------------------------------------
-/

-- Level 1: mul_le_mul_right
theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  sorry

-- Level 2: mul_left_ne_zero
theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  sorry

-- Level 3: eq_succ_of_ne_zero
theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  sorry

-- Level 4: one_le_of_ne_zero
theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  sorry

-- Level 5: le_mul_right
theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  sorry

-- Level 6: mul_right_eq_one
theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  sorry

-- Level 7: mul_ne_zero
theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  sorry

-- Level 8: mul_eq_zero
theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  sorry

-- Level 9: mul_left_cancel
theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

-- Level 10: mul_right_eq_self
theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  sorry

/-!
Algorithm World
--------------------------------------------------------------------------------
-/

-- Level 1: add_left_comm
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  sorry

-- Level 2: making life easier
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  sorry

-- Level 3: making life simple
example (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry

-- Level 4: the simplest approach
example (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry

-- Level 5: pred
example (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry

-- Level 6: is_zero
theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  sorry

-- Level 7: An algorithm for equality
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  sorry

-- Level 8: decide
example : (20 : ℕ) + 20 = 40 := by
  sorry

-- Level 9: decide again
example : (2 : ℕ) + 2 ≠ 5 := by
  sorry

end MyNat
