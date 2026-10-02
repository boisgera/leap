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

## Recursor
-/

#print Nat
-- inductive Nat : Type
-- number of parameters: 0
-- constructors:
-- Nat.zero : ℕ
-- Nat.succ : ℕ → ℕ

/-!
Every inductive type comes with a custom, built-in recursor:
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

#synth LE ℕ
-- instLENat

#print instLENat
-- @[instance_reducible] def instLENat : LE ℕ :=
-- { le := Nat.le }

#print Nat.le
-- protected inductive Nat.le : ℕ → ℕ → Prop
-- number of parameters: 1
-- constructors:
-- Nat.le.refl : ∀ {n : ℕ}, n.le n
-- Nat.le.step : ∀ {n m : ℕ}, n.le m → n.le m.succ

#check Nat.le_succ
-- Nat.le_succ (n : ℕ) : n ≤ n.succ

theorem Sandbox.zero_le : ∀ (n : ℕ), 0 ≤ n := Nat.rec
  (zero := le_refl 0)
  (succ := fun n zero_le_n => le_trans zero_le_n (Nat.le_succ n))

/-!
## Induction/Recursion in pratice

Let's come back to the definition of `fact` and the proof of `zero_le` but
using the more UX-friendly constructs of Lean.

To define `fact` we can use pattern matching and explicit recursive calls:
-/

def fact' (n : ℕ) : ℕ :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => (fact' n) * (n + 1)

/-!
We can even go with the terser
-/

def fact'_alt : ℕ → ℕ
  | 0 => 1
  | n + 1 => (fact'_alt n) * (n + 1)

/-!
We can do a very similar thing to prove results
-/

theorem Sandbox.zero_le' (n : ℕ) : 0 ≤ n :=
  match n with
  | 0 => le_refl 0
  | n + 1 => le_trans (zero_le' n) (Nat.le_succ n)

/-!
Alternatively, **in tactic mode**, we can use the `induction` construct, which
matches with an induction hypothesis and therefore doesn't require an
explicit recursive call from us. This is closer to the recursor syntax;
this is also arguably heavier to use to define data (by recursion) since
we need to wrap every result in `exact` and more suitable for proofs
(by induction).
-/

def fact'' (n : ℕ) : ℕ := by
  induction n with
  | zero => exact 1
  | succ n fact_n => exact fact_n * (n + 1)

theorem Sandbox.zero_le'' (n : ℕ) : 0 ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ n zero_le_n => exact le_trans zero_le_n (Nat.le_succ n)

theorem Sandbox.zero_le''' (n : ℕ) : 0 ≤ n := by
  induction n with
  | zero =>
    apply le_refl
  | succ n zero_le_n =>
    apply le_trans
    · apply zero_le_n
    · apply Nat.le_succ

/-!
## Recursion/induction beyond natural numbers
-/

inductive BTree (α : Type u) where
  | empty : BTree α
  | node (left : BTree α) (right : BTree α) : BTree α

#check BTree.rec
-- BTree.rec.{u_1, u} {α : Type u} {motive : BTree α → Sort u_1}
--   (empty : motive BTree.empty)
--   (node : (left right : BTree α)
--     → motive left
--     → motive right
--     → motive (left.node right))
--   (t : BTree α) : motive t

def BTree.depth {α} (t : BTree α) : ℕ :=
  match t with
  | empty => 0
  | node left right => (max left.depth right.depth) + 1

def BTree.size {α} (t : BTree α) : ℕ :=
  match t with
  | empty => 0
  | node left right => (left.size + right.size) + 1

lemma Nat.max_le_add (m n : ℕ) : max m n ≤ m + n := by
  apply max_le_add_of_nonneg
  · positivity
  · positivity

theorem BTree.depth_le_size {α} (t : BTree α) : t.depth ≤ t.size := by
  induction t with
  | empty =>
    rw [BTree.depth, BTree.size]
  | node left right left_ih right_ih =>
    rw [BTree.depth, BTree.size]
    have : max left.depth right.depth ≤ left.depth + right.depth := by
      apply Nat.max_le_add
    linarith


/-!

--------------------------------------------------------------------------------

TODO:
  - induction on auxiliary stuff with `using`?
  - non-structural recursion?
-/
