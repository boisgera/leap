import Mathlib

inductive L (α : Type) where
| nil : L α
| cons : α -> L α -> L α

def oneTwoThree : L Nat := (L.cons 1 (L.cons 2 (L.cons 3 L.nil)))

def L.length {α} (l : L α) : Nat :=
  match l with
  | nil => 0
  | cons _ l => (L.length l) + 1

def L.concat {α} (l : L α) (a : α) : L α :=
   match l with
   | nil => cons a nil
   | cons b l => cons b (L.concat l a)

#eval oneTwoThree

inductive NEL (α : Type) where
| sing : α -> NEL α
| cons : α -> NEL α -> NEL α

def ott : NEL Nat := NEL.cons 1 (NEL.cons 2 (NEL.sing 3))

#eval ott

inductive NEL' (α : Type) where
| mk : (list : L α) -> (0 < list.length) -> NEL' α

structure NEL'' (α : Type) where
  list : L α
  non_empty : 0 < list.length

theorem ott_non_empty : 0 < oneTwoThree.length := by
  rw [oneTwoThree]
  rw [L.length]
  set n := (L.cons 2 (L.cons 3 L.nil)).length
  generalize h : n = m
  clear n h
  apply Nat.zero_lt_succ

def ott' := NEL''.mk oneTwoThree ott_non_empty

def NEL''.concat {α} (l : L α) (a : α) : NEL'' α :=
  {
    list := L.concat l a
    non_empty := sorry -- TODO!
  }
