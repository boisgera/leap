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

#check congrArg
-- congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α}
--     (f : α → β) (h : a₁ = a₂) :
--     f a₁ = f a₂

lemma not_twice_eq_one {k : ℤ} : ¬ (2 * k = 1) := by
  intro h
  have eq_mod_two : (2 * k) % 2 = 1 % 2 := congrArg (· % 2) h
  have twice_mod_two : (2 * k) % 2 = 0 := by
    simp only [EuclideanDomain.mod_eq_zero]
    -- ⊢ 2 ∣ 2 * k
    simp only [Dvd.dvd]
    -- ⊢ ∃ c, 2 * k = 2 * c
    use k
  have one_mod_two : (1 % 2) = (1 : ℤ) := by norm_num
  rw [twice_mod_two, one_mod_two] at eq_mod_two
  -- eq_mod_two : 0 = 1
  norm_num at eq_mod_two

lemma mod_two (k : ℤ) : k % 2 = 0 ∨ k % 2 = 1 := by grind

theorem even_iff_not_odd (n : ℕ) : Even n ↔ ¬ Odd n := by
  apply Iff.intro
  . intro even_n
    rw [Not]
    intro odd_n
    rw [Even] at even_n
    rw [Odd] at odd_n
    let ⟨k1, h1⟩ := even_n
    let ⟨k2, h2⟩ := odd_n
    have : 2 * k1 = 2 * k2 + 1 := by grind
    have : 2 * (k1 : ℤ) = 2 * (k2 : ℤ) + 1 := by grind
    have : 2 * ((k1 : ℤ) - (k2 : ℤ)) = 1 := by grind
    let k := (k1 : ℤ) - (k2 : ℤ)
    have : 2 * k = 1 := by grind
    exact not_twice_eq_one this
  . intro not_odd_n
    rw [Even, Odd] at *
    by_contra
    cases mod_two n with
    | inl h => admit
    | inr h => admit


-- and then a recursion is necessary...
theorem fib_parity (n : ℕ) : (n ≥ 4) →
  (Even n → Odd (fib n)) ∧ (Odd n → Even (fib n)) := by admit

end Sandbox
