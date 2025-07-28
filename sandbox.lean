
def getCoords' (string : String) : Option (Nat × Nat) := do
  let parts := string.splitOn " "
  let x_str <- parts[0]?
  let y_str <- parts[1]?
  let x <- x_str.toNat?
  let y <- y_str.toNat?
  return (x, y)

#eval getCoords' "3 4"
-- some (3, 4)

#eval getCoords' "douze quarante-deux"
-- none

def a := [1, 2, 3]

#eval a[42]!

#eval getElem! a 42

#print instMonadOption
