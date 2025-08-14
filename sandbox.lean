
def f (n : Nat) : Nat :=
  let list := List.range (n + 1)
  have h : n / 2 < list.length := by
    rw [List.length_range] -- n : Nat ⊢ n / 2 < n + 1
    apply Nat.lt_succ_of_le -- n : Nat ⊢ n / 2 ≤ n
    exact Nat.div_le_self n 2
  list[n / 2]

#eval f 0
-- 0
#eval f 1
-- 0
#eval f 2
-- 1
#eval f 3
-- 1
#eval f 4
-- 2
