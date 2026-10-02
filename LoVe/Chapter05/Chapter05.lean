import Mathlib

/-!
---
title: "❤️ LoVe Notes – Chapter 5"
author:
- Sébastien Boisgérault
lang: en
---
-/

/-!
# 5.2 Structural induction
-/

#print Nat
-- inductive Nat : Type
-- number of parameters: 0
-- constructors:
-- Nat.zero : ℕ
-- Nat.succ : ℕ → ℕ

/-!
Every inductive type comes with a built-in recursor:
-/

#check Nat.rec
-- Nat.rec.{u} {motive : ℕ → Sort u}
-- (zero : motive Nat.zero) (succ : (n : ℕ) → motive n → motive n.succ) (t : ℕ) :
--   motive t

/-!
This recursor is the low-level construct which can be used to build data or prove
properties based on natural numbers: you can perform definition by recursion
or proof by induction. Let's give an example of each.
-/

/-!
To define the factorial function by recursion, `Nat.rec` has to produce a
function `(t : ℕ) → motive t` of type `ℕ → ℕ`, i.e. work with the constant
motive `fun (t : ℕ) => ℕ`. We also have to provide the value of `fact 0` and a
function that given `n` and `fact n` computes `fact (n + 1)`:
-/

def fact : ℕ → ℕ := Nat.rec 1 (fun n fact_n => fact_n * (n + 1))

#eval fact 5
-- 120

/-!
To prove that `∀ (n : ℕ), 0 ≤ n`, now we need the recursor to create a function
of type `(n : ℕ) → 0 ≤ n`, hence work with the motive `(n : ℕ) → 0 ≤ n`.
We also need to provide a proof that `0 ≤ 0` and given a `n` and a proof that
`0 ≤ n`, prove that `0 ≤ n + 1`. The first one can be proved by reflexivity of
`≤`, the other by transitivity of `≤` and the theorem that states that
`∀ (n : ℕ), n ≤ n + 1`.
-/

#check le_refl
-- le_refl.{u_1} {α : Type u_1} [Preorder α] (a : α) : a ≤ a

#check le_trans
-- le_trans.{u_1} {α : Type u_1} [Preorder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c

#check Nat.le_succ
-- Nat.le_succ (n : ℕ) : n ≤ n.succ

theorem Sandbox.zero_le : ∀ (n : ℕ), 0 ≤ n := Nat.rec
  (zero := le_refl 0)
  (succ := fun n zero_le_n => le_trans zero_le_n (Nat.le_succ n))

/-!
TODO:
  - "syntaxic sugar" in each case.
  - other examples (list, trees ?)
-/
