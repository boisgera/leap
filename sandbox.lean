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

def __readBool (s : String) : Option Bool := do
  match readFalse s with
  | some b => some b
  | none   =>
    match readTrue s with
    | some b => some b
    | none => failure

def readBool (s : String) : Option Bool :=
  try
    readFalse s
  catch _ =>
    try
      readTrue s
    catch _ =>
      throw ()

#eval readBool "true"
-- some true

#eval readBool "0"
-- some false

#eval readBool "maybe?"
-- none


inductive NucleotideBase where
| adenine : NucleotideBase
| cytosine : NucleotideBase
| guanine: NucleotideBase
| thymine: NucleotideBase

structure DecodeError where
  position : Nat

abbrev Result := Except DecodeError (List NucleotideBase)

def decodeDNA (s : String) : Result := do
  let mut bases : List NucleotideBase := []
  for (c, i) in s.toList.zipIdx do
    match c with
    | 'A' => bases := bases ++ [.adenine]
    | 'C' => bases := bases ++ [.cytosine]
    | 'G' => bases := bases ++ [.guanine]
    | 'T' => bases := bases ++ [.thymine]
    | _   => throw { position := i }
  return bases
