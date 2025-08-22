def sum (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

#eval sum [1, 1, 2, 3, 5, 8, 13, 21]
-- 54

·
