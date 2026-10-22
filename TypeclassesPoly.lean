
-- import Mathlib

def polyFloat (x : Float) : Float :=
  x * x + x + 1

#eval polyFloat 3.14
-- 13.999600

def polyInt (i : Int) : Int :=
  i * i + i + 1

#eval polyInt 3
-- 12

def poly' {α} [Mul α] [Add α] [One α] (a : α) : α :=
  a * a + a + 1

def poly {α} [Mul α] [Add α] [One α] (a : α) : α :=
  Add.add
    (Add.add
      (Mul.mul a a)
      a)
    One.one

#eval poly 3.14
-- 13.999600

#eval poly 3
-- 13

#eval poly true

#print Mul
-- class Mul.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   Mul.mul : α → α → α
-- constructor:
--   Mul.mk.{u} {α : Type u} (mul : α → α → α) : Mul α

#print Add
-- class Add.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   Add.add : α → α → α
-- constructor:
--   Add.mk.{u} {α : Type u} (add : α → α → α) : Add α

#print One
-- class One.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   One.one : α
-- constructor:
--   One.mk.{u} {α : Type u} (one : α) : One α

instance instMulBool : Mul Bool where
  mul
  | false, false => false
  | false, true => false
  | true, false => false
  | true, true => true

instance instAddBool : Add Bool where
  add
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

instance instOneBool: One Bool where
  one := true

#eval poly false
-- true

#eval @poly Bool instMulBool instAddBool instOneBool false
-- true
