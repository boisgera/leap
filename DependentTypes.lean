
-- import Mathlib

/-
Dependent Types
================================================================================

Types whose definition depends on values (not merely type).

See also: <https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/#Functional-Programming-in-Lean--Programming-with-Dependent-Types>
-/



namespace Sandbox


/-
Generic stuff (not strictly dependent types)
--------------------------------------------------------------------------------
-/

def v0.singleton (n : Nat) : List Nat := [n]


/-
Generic version:
-/

def v1.singleton {α} (a : α) : List α := [a]

/-
Same generic version, expanded
-/


def v2.singleton.{u} {α : Type u} (a : α) : List α := [a]

/-
Generic version without the implicit argument (syntaxic sugar):
-/

def v3.singleton (α : Type u) (a : α) : List α := [a]

#eval v3.singleton Nat 42
-- [42]

/-
Generic functions are not a special case! They work because Lean supports:
  - implicit arguments (optional actually but nice to have)
  - types are first-class values (can be passed as parameters)
  - dependent types: the type of the 2nd argument depends
    on the value of the first (but this value is still a type)
-/



/-
Small but enlightening dependent type example
--------------------------------------------------------------------------------
-/

def answer (english : Bool := False) : if english then String else Nat :=
  match english with
  | false => (42 : Nat)
  | true => "forty-two"

#eval answer
-- 42

#eval answer (english := True)
-- "forty-two"

/-
This slight variant is actually interesting.
-/
def answer' (english : Bool := False) : if english then String else Nat :=
  if h : english then
    -- english : Bool
    -- h : english = true
    -- ⊢ if english = true then String else Nat
    have : String = (if (english = true) then String else Nat) := by
      -- elementary proof
      rw [h]
      -- at this stage, a rfl would work
      rw [ite]
      rw [instDecidableEqBool]
      rw [Bool.decEq]
    cast this "forty-two"
  else
    -- english : Bool
    -- h : ¬english = true
    -- ⊢ if english = true then String else Nat
    have : Nat = (if english = true then String else Nat) := by
      -- simp only [h] would work instead of this lemma
      have l : english = false :=
        match english with
        | false => Eq.refl false
        | true => let absurd := h (Eq.refl true); absurd.elim
      clear h
      rw [l]
      rw [ite, instDecidableEqBool, Bool.decEq.eq_def]
    cast this (42 : Nat)

/-
Lists and Vectors
--------------------------------------------------------------------------------
-/



/-
Types that depend on values
--------------------------------------------------------------------------------
-/


inductive List (α : Type u) : Type u where
| nil : List α
| cons : α -> List α -> List α

#check List.cons 1 (List.cons 2 List.nil)
-- List.cons 1 (List.cons 2 List.nil) : List ℕ

#reduce List.cons 1 (List.cons 2 List.nil)
-- List.cons (1, 3) (List.cons (2, 4) List.nil)

def List.zip {α β} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | List.cons x xs, List.cons y ys => List.cons (x, y) (List.zip xs ys)
  | _, _ => List.nil

#reduce List.zip (List.cons 1 (List.cons 2 List.nil)) (List.cons 3 (List.cons 4 List.nil))
-- List.cons (1, 3) (List.cons (2, 4) List.nil)

inductive Vec (α : Type u) : Nat -> (Type u) where
| nil : Vec α 0
| cons : {n : Nat} -> α -> Vec α n -> Vec α (n + 1)

#check Vec.nil
-- Sandbox.Vec.nil.{u} {α : Type u} : Vec α 0

#check Vec.cons 1 Vec.nil
-- Vec.cons 1 Vec.nil : Vec Nat (0 + 1)

#check Vec.cons 1 (Vec.cons 2 Vec.nil)
-- Vec.cons 1 (Vec.cons 2 Vec.nil) : Vec Nat (0 + 1 + 1)

def Vec.zip {α β} {n : Nat} (xs : Vec α n) (ys : Vec β n) : Vec (α × β) n :=
  match xs, ys with
  | Vec.cons x xs, Vec.cons y ys => Vec.cons (x, y) (Vec.zip xs ys)
  | Vec.nil, Vec.nil => Vec.nil

#check Vec.zip (Vec.cons 1 (Vec.cons 2 Vec.nil)) (Vec.cons 3 (Vec.cons 4 Vec.nil))
-- (Vec.cons 1 (Vec.cons 2 Vec.nil)).zip (Vec.cons 3 (Vec.cons 4 Vec.nil)) : Vec (Nat × Nat) (0 + 1 + 1)
#reduce Vec.zip (Vec.cons 1 (Vec.cons 2 Vec.nil)) (Vec.cons 3 (Vec.cons 4 Vec.nil))
-- Vec.cons (1, 3) (Vec.cons (2, 4) Vec.nil)

/-
TODO: matrix & matrix product (see Mathlib)
-/

/-
Type-safe Formatter
--------------------------------------------------------------------------------
-/

/-
Typed Queries
--------------------------------------------------------------------------------

See <https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/#Functional-Programming-in-Lean--Programming-with-Dependent-Types--Worked-Example___-Typed-Queries>
-/

/-
Predicate Calculus
--------------------------------------------------------------------------------
-/


end Sandbox
