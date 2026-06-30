
#eval [4, 2, 1]
-- [4, 2, 1]

#eval [4, 2, 1].length
-- 3

inductive ListWithLength (α : Type u) where
| nil : ListWithLength α (0 : Nat)
| cons (a : α) (l : ListWithLength α n) : (ListWithLength α (n+1))

-- TODO:

-- structure LenList (α : Type u) where
--   data : List α
--   len : Nat
--   len_eq : data.length = len := by rfl

-- def LenList.cons (a : α) (l : LenList α) : LenList α :=
--   ⟨a :: l.data, l.len + 1, by simp [l.len_eq]⟩

-- def LenList.nil : LenList α := ⟨[], 0, rfl⟩
