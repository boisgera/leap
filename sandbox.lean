inductive NucleotideBase where
| adenine : NucleotideBase
| cytosine : NucleotideBase
| guanine: NucleotideBase
| thymine: NucleotideBase
deriving Repr

structure DecodeError where
  decoded : List NucleotideBase
  pos : Nat
  char : Char
deriving Repr

def Result := Except DecodeError (List NucleotideBase) deriving Repr

def decodeDNA (dna : String) : Result := do
  let mut bases : List NucleotideBase := []
  for (c, i) in dna.toList.zipIdx do
    match c with
    | 'A' => bases := bases ++ [.adenine]
    | 'C' => bases := bases ++ [.cytosine]
    | 'G' => bases := bases ++ [.guanine]
    | 'T' => bases := bases ++ [.thymine]
    | _   => throw { decoded := bases, pos := i, char := c }
  return bases

#eval decodeDNA "GATTACA"
-- Except.ok [
--   NucleotideBase.guanine,
--   NucleotideBase.adenine,
--   NucleotideBase.thymine,
--   NucleotideBase.thymine,
--   NucleotideBase.adenine,
--   NucleotideBase.cytosine,
--   NucleotideBase.adenine
-- ]

#eval decodeDNA "TARATATA"
-- Except.error {
--   decoded := [NucleotideBase.thymine, NucleotideBase.adenine],
--   pos := 2,
--   char := 'R'
-- }

def decodeDNA' (dna : String) : Result := do
  let mut bases : List NucleotideBase := []
  let mut dna := dna
  while dna != "" do
    try
      bases := bases ++ (<- decodeDNA dna)
      dna := ""
    catch decodeError =>
      bases := bases ++ decodeError.decoded
      dna := dna.drop (decodeError.pos + 1)
  return bases

#eval decodeDNA' "GATTACA"
-- Except.ok [
--   NucleotideBase.guanine,
--   NucleotideBase.adenine,
--   NucleotideBase.thymine,
--   NucleotideBase.thymine,
--   NucleotideBase.adenine,
--   NucleotideBase.cytosine,
--   NucleotideBase.adenine
-- ]

#eval decodeDNA' "TARATATA"
-- Except.ok [
--  NucleotideBase.thymine,
--  NucleotideBase.adenine,
--  NucleotideBase.adenine,
--  NucleotideBase.thymine,
--  NucleotideBase.adenine,
--  NucleotideBase.thymine,
--  NucleotideBase.adenine
--  ]

-- TODO: report sucks but adapt decodeDNA' in this role, with the easy way to
-- get the info out (define a get! ?) and the "proper version" (with a get
-- to define that uses a proof)

-- def report (dna : String) : String :=
--   match decodeDNA dna with
--   | .ok l => s!"✅ decoded sequence of length {l.length}"
--   | .error e => s!"❌ invalid character '{e.char}' at position {e.pos}"

-- #eval report "GATTACA"
-- -- "✅ decoded sequence of length 7"

-- #eval report "TARATATA"
-- -- "❌ invalid character 'R' at position 2"

-- -- Simpler test of the try/catch issue
-- inductive E where
-- | main (n : Nat) : E
-- | alt : E

-- def f (e : E) (h : ∃ (n : Nat), e = .main n) : Nat :=
--   -- I can't extract n from h since I am not in a proof. Joy...
--   match e with
--   | .main m => m
--   | .alt =>
--       have absurd : False := by { have ⟨_, eq⟩ := h; nomatch eq }
--       nomatch absurd


-- -- Leans knows in the second clause that h : ∃ n, E.alt = E.main n
-- -- let's assume for a moment that I can turn this into an absurd stuff.
-- -- How can I say "I don't need to pattern match that clause?".
-- -- Ah, ok, I think I know: nomatch k where k : False does work for
-- -- example.

-- -- A general result would be: if an exception-throwing value is a top-level
-- -- try catch and I can prove that the alternate clause is ok, then the whole
-- -- stuff is also ok, AND therefore, I can safely extract the value (make
-- -- a generic extractor), so that the final user never has to consider a
-- -- pattern matching that cannot happen.

-- -- -----------------------------------------------------------------------------

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
