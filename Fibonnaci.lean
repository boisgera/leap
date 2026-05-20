import Mathlib

namespace Sandbox

def fib (n : ℕ) : ℕ :=
  match n with
  | 0 | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 0
-- 1

#eval fib 1
-- 1

#eval fib 2
-- 2

#eval fib 3
-- 3

#eval fib 4
-- 5

#eval fib 5
-- 8

#eval fib 6
-- 13

/-!
The parity stuff in Mathlib: present, but quite abstract.
-/

#print Even
-- def Even.{u_2} : {α : Type u_2} → [Add α] → α → Prop :=
-- fun {α} [Add α] a => ∃ r, a = r + r

#check Nat.even_iff
-- Nat.even_iff {n : ℕ} : Even n ↔ n % 2 = 0

#check even_iff_two_dvd
-- even_iff_two_dvd.{u_2} {α : Type u_2} [Semiring α] {a : α} :
-- Even a ↔ 2 ∣ a

#check Dvd
-- Dvd.{u_1} (α : Type u_1) : Type u_1

#print Nat.instDvd
-- @[implicit_reducible] def Nat.instDvd : Dvd ℕ :=
-- { dvd := fun a b => ∃ c, b = a * c }

#print Odd
-- def Odd.{u_2} : {α : Type u_2} → [Semiring α] → α → Prop :=
-- fun {α} [Semiring α] a => ∃ k, a = 2 * k + 1

/-!
Our simplified parity layer
-/

def Even (n : ℕ) := ∃ (k : ℕ), n = 2 * k
def Odd (n : ℕ) := ∃ (k : ℕ), n = 2 * k + 1

theorem even_iff_not_odd (n : ℕ) : Even n ↔ ¬ Odd n := by
  apply Iff.intro
  . intro even_n
    rw [Not]
    intro odd_n
    rw [Even] at even_n
    rw [Odd] at odd_n
    let ⟨k1, h1⟩ := even_n
    let ⟨k2, h2⟩ := odd_n
    -- Fuck, we need to cast that in ℤ or to match wrt k1 <= k2 ...
    admit
  . admit

theorem fib_parity (n : ℕ) : (n ≥ 4) →
  (Even n → Odd (fib n)) ∧ (Odd n → Even (fib n)) := by admit

end Sandbox
