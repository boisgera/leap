
#eval [4, 2, 1]
-- [4, 2, 1]

#eval [4, 2, 1].length
-- 3


-- This works, but the length is a compile-time quantity.
-- I don't see ATM the limitations that entails.

inductive LenList (α : Type u) : Nat → Type (u + 1) where
| nil : LenList α 0
| cons {n : Nat} (a : α) (l : LenList α n) : LenList α (n + 1)

namespace LenList

def length {α n} (_ : LenList α n) : Nat := n

end LenList

#eval LenList.cons 2 (LenList.cons 1 (LenList.nil : LenList Nat 0))
-- LenList.cons 2 (LenList.cons 1 (LenList.nil))

-- The "same thing" at runtime, but we not guarantee that the length
-- is valid. We don't have correctness by construction.

inductive LenList' (α : Type u) where
| nil (n : Nat) : LenList' α
| cons (n : Nat) (a : α) (l : LenList' α) : LenList' α

namespace LenList'

def length {α} (l : LenList' α) : Nat :=
  match l with
  | nil n => n
  | cons n _ _ => n

end LenList'

#eval LenList'.cons 2 9 (LenList'.cons 1 9 (LenList'.nil 0 : LenList' Nat))
-- LenList.cons 2 (LenList.cons 1 (LenList.nil))
