
def rollUntil3x1 : IO (List Nat) := do
    let rollDie := IO.rand 1 6
    let mut dices := []
    let mut count := 0
    while count < 3 do
      let die <- rollDie
      dices := dices ++ [die]
      if die == 1 then
        count := count + 1
      else
        count := 0 -- reset
    return dices

#eval rollUntil3x1
-- [6, 2, 4, 4, 2, 6, 2, 5, 1]
