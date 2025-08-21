
def rollDie : IO Nat := do
  IO.rand 1 6

def rollDie'' : IO Nat := do
  let die <- rollDie
  IO.println s!"🎲: {die}"
  return die

#eval rollDie''
-- 🎲: 2
-- 2
