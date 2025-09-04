
inductive ABC where
| a
| b
| c

def ABC.f (abc : ABC) : Nat :=
  match abc with
  | a => 1
  | b => 2
  | c => 3

#eval ABC.f ABC.c
-- 1

#eval ABC.c.f
-- 3

def ABC.g : Nat -> ABC -> Nat :=
  fun n abc =>
    n + abc.f

#eval ABC.g 7 ABC.c
-- 10

#eval ABC.c.g 7
-- 10
