def pred? (n : Nat) : Option Nat :=
  if n > 0 then
    some (n - 1)
  else
    none

def showPred (n : Nat) : IO Unit :=
  match pred? n with
  | some m => IO.println s!"pred {n} = {m}"
  | none => IO.println s!"error: {n} has no predecessor"

#eval showPred 7
-- pred 7 = 6

#eval showPred 0
-- error: 0 has no predecessor

def pred?' (n : Nat) : Option Nat :=
  if n > 0 then
    some (n - 1)
  else
    failure

#eval pred?' 7

#eval pred?' 0

def readFalse (s : String) : Option Bool :=
  if s == "false" || s == "0" || s == "⊥" then
    return false
  else
    none

def readTrue (s : String) : Option Bool :=
  if s == "true" || s == "1" || s == "⊤" then
    return true
  else
    none

def readBool (s : String) := readFalse s <|> readTrue s


#eval readBool "true"
-- some true

#eval readBool "0"
-- some false

#eval readBool "maybe?"
-- none
