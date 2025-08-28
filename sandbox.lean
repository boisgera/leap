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
  pos : Nat
  char : Char

abbrev Result := Except DecodeError (List NucleotideBase)

def decodeDNA (dna : String) : Result := do
  let mut bases : List NucleotideBase := []
  for (c, i) in dna.toList.zipIdx do
    match c with
    | 'A' => bases := bases ++ [.adenine]
    | 'C' => bases := bases ++ [.cytosine]
    | 'G' => bases := bases ++ [.guanine]
    | 'T' => bases := bases ++ [.thymine]
    | _   => throw { pos := i , char := c}
  return bases

def report (dna : String) : String :=
  match decodeDNA dna with
  | .ok l => s!"✅ decoded sequence of length {l.length}"
  | .error e => s!"❌ invalid character '{e.char}' at position {e.pos}"

#eval report "GATTACA"
-- "✅ decoded sequence of length 7"

#eval report "TARATATA"
-- "❌ invalid character 'R' at position 2"

-- Simpler test of the try/catch issue
inductive E where
| main (n : Nat) : E
| alt : E

def f (e : E) (h : ∃ (n : Nat), e = .main n) : Nat :=
  -- I can't extract n from h since I am not in a proof. Joy...
  match e with
  | .main m => m
  | .alt =>
      have absurd : False := by { have ⟨_, eq⟩ := h; nomatch eq }
      nomatch absurd


-- Leans knows in the second clause that h : ∃ n, E.alt = E.main n
-- let's assume for a moment that I can turn this into an absurd stuff.
-- How can I say "I don't need to pattern match that clause?".
-- Ah, ok, I think I know: nomatch k where k : False does work for
-- example.

-- A general result would be: if an exception-throwing value is a top-level
-- try catch and I can prove that the alternate clause is ok, then the whole
-- stuff is also ok, AND therefore, I can safely extract the value (make
-- a generic extractor), so that the final user never has to consider a
-- pattern matching that cannot happen.

-- -----------------------------------------------------------------------------

def reportAux (dna : String) : Except DecodeError String := do
    try
      let l <- decodeDNA dna
      return s!"✅ decoded sequence of length {l.length}"
    catch e =>
      return s!"❌ invalid character '{e.char}' at position {e.pos}"

theorem safe_try_except {ε α} (body : Except ε α) (handler : ε -> Except ε α) :
  (∀ (e : ε), (handler e).isOk = true) -> (tryCatch body handler).isOk = true
  := by
  intro h_ok
  rw [tryCatch]
  rw [instMonadExceptOfMonadExceptOf]
  simp [tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
  cases body with
  | ok a =>
    rw [Except.isOk, Except.toBool]
  | error e =>
    simp
    rw [h_ok e]

theorem reportAuxCantFail : ∀ (dna : String), (reportAux dna).isOk = true := by
  intro dna
  simp [reportAux]
  apply safe_try_except
  simp [Except.isOk, Except.toBool, pure, Except.pure]

def Except.get {ε α} (except : Except ε α) : except.isOk = true -> α :=
  fun ex_ok =>
    match except with
    | ok a => a
    | error _ => nomatch ex_ok

def report' := fun (dna : String) =>
  Except.get (reportAux dna) (reportAuxCantFail dna)


-- -----------------------------------------------------------------------------


def report'' (dna : String) : String :=
  let message? := reportAux dna
  match message? with
  | .ok message => message
  | .error _ => panic! "unreachable!"

#eval report'' "GATTACA"
-- "✅ decoded sequence of length 7"

#eval report'' "TARATATA"
-- "❌ invalid character 'R' at position 2"
