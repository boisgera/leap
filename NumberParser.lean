/-!
Reference: JSON number (https://www.json.org/json-en.html)

We will "relax" the spec a bit for the sake of simplicity
(wrt +, leading zeros, etc.)

For example, we accept "+007" (which should be "7" in JSON)
-/


/-!
TODO: distinguish cleanly what is mandatory and what is optional
(/has a default parsed value when the [] fallback is matched).
Given our laxity, everything is optional? Including the Nat
Nah, not the Nat... So `.1` won't work for us.
-/

inductive Sign where
  | pos : Sign
  | neg : Sign
deriving Repr

-- Q/W: would it work if I was matching the wrong pattern first?
-- OOH I know it can't from first principles but OTOH I was
-- kind of expecting the PEG stuff to automatically "come back"
-- to the other branch.
-- My feeling is that here I don't get the benefit since I am
-- preparing a left-fold scheme when right fold should actually
-- be used to get some feedback from what happens after
-- (so that we can fail the `Sign.pos` parsing if that doesn't work
-- with what happens after)
--
-- Nota: we decide to be lax here and accept '+' here (simpler).
def parseSign (cs : List Char) : Option (Sign × List Char) :=
  match cs with
  | '-' :: cs => some (Sign.neg, cs)
  | '+' :: cs => some (Sign.pos, cs)
  | cs => some (Sign.pos, cs)

#eval parseSign "+42".toList
-- some (Sign.pos, ['4', '3'])

#eval parseSign "-42".toList
-- some (Sign.neg, ['4', '3'])

#eval parseSign "42".toList
-- some (Sign.pos, ['4', '2'])

theorem parseSign_is_some : ∀ cs, (parseSign cs).isSome := by
  intro cs
  cases cs <;> simp [parseSign]
  split <;> simp

-- Hint
def parseDigit (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | c :: cs =>
    let n := Int.ofNat c.toNat - Int.ofNat '0'.toNat
    if 0 <= n && n ≤ 9 then
      some (n.natAbs, cs)
    else none
  | [] => none

#eval parseDigit "0".toList
-- some (0, [])

#eval parseDigit "9".toList
-- some (9, [])

#eval parseDigit "09".toList
-- some (0, ['9'])

#eval parseDigit "...".toList
-- none

partial def parseNatAux (cs : List Char) (nat : Nat) : Option (Nat × List Char) :=
  match parseDigit cs with
  | some (d, cs) => parseNatAux cs (nat * 10 + d)
  | none => some (nat, cs)

def parseNat (cs : List Char) : Option (Nat × List Char) :=
  match parseDigit cs with
  | some (d, cs) => parseNatAux cs d
  | none => none -- fail is there is not at least one digit

#eval parseNat "".toList
-- none

#eval parseNat "ABC".toList
-- none

#eval parseNat "1".toList
-- some (1, [])

#eval parseNat "123".toList
-- some (123, [])

#eval parseNat "123ABC".toList
-- some (123, ['A', 'B', 'C'])

#eval parseNat "007".toList
-- some (7, [])

#eval parseNat "3.14".toList
-- some (3, ['.', '1', '4']) -- OUCH!

-- WONTFIX
-- Strict Nat parser: if you start with a 0, that's it, you are zero.
-- All non-zero number start with a non-zero digit.
-- def parseStrictNat (cs : List Char) : Option (Nat × List Char) :=
--   sorry

-- ## Fractional part

-- def isDigit (c : Char) : Bool :=
--   let n := c.toNat - '0'.toNat
--   0 ≤ n && n ≤ 9

def parseFractionAux (cs : List Char) (nat_leadingZeros : Nat × Nat) :
    (Nat × Nat) × List Char :=
  let (nat, leadingZeros) := nat_leadingZeros
  match cs with
  | '0' :: cs =>
    parseFractionAux cs (nat, leadingZeros + 1)
  | c :: cs =>
    let d := Int.ofNat c.toNat - Int.ofNat '0'.toNat
    if 1 ≤ d && d ≤ 9 then
      parseFractionAux cs (10 * nat + d.natAbs, leadingZeros)
    else
      (nat_leadingZeros, c :: cs)
  | [] => (nat_leadingZeros, cs)

-- Note: 'Nat' in the return type won't cut it: when we have 1.007, the
-- matched fraction would be 7, we forget the "shift". So we go for
-- Nat × Nat where the second Nat is the number of leading zeros.

-- Bug: we forget if the 0's are leading or not, so .700 would display two
-- leading zeros. We need to split the parsing into zeros first, then the
-- rest.
def parseFraction (cs : List Char) : Option ((Nat × Nat) × List Char) :=
  match cs with
  | '.' :: cs => some (parseFractionAux cs (0, 0)) -- Nota: a bare "." works
  | _ => some ((0, 0), cs)

#eval parseFraction ".14159265359".toList
-- some ((14159265359, 0), [])

#eval parseFraction ".007".toList
-- some ((7, 2), [])

#eval parseFraction "42".toList
-- none

#eval parseFraction ".66e+2".toList
-- some ((66, 0), ['e', '+', '2'])

def parseExponent (cs : List Char) : Option (Int × List Char) :=
  match cs with
  | 'e' :: cs | 'E' :: cs =>
    match parseSign cs with
    | some (Sign.pos, cs) =>
      match parseNat cs with
      | some (n, cs) => some (Int.ofNat n, cs)
      | none => none
    | some (Sign.neg, cs) =>
      match parseNat cs with
      | some (n, cs) => some (-Int.ofNat n, cs)
      | none => none
    | none => panic! "unreachable"
  | _ => some (0, cs)

#eval parseExponent "e+0".toList
-- some (0, [])

#eval parseExponent "e+007".toList
-- some (7, [])

#eval parseExponent "e-007".toList
-- some (-7, [])

#eval parseExponent "E-007".toList
-- some (-7, [])

#eval parseExponent "E-007EOS".toList
-- some (-7, ['E', 'O', 'S'])

#eval parseExponent "e+2".toList
-- some (2, [])

-- # Assembly

structure Number where
  sign : Sign
  nat : Nat
  frac : Nat × Nat
  exp : Int
deriving Repr

def v0.parseNumber (cs : List Char) : Option (Number × (List Char)) :=
  -- Hard to read, very nested, action at a distance, context unclear, etc.
  -- And not DRY at all of course. That's probably the first thing we can/should
  -- tackle, with auxilary functions. And see how good the code can become
  -- with only these auxiliary functions.
  -- The other way of course is to consider "composition" aka parser combinators
  -- Here, its the monadic bind that works extremely well!
  match parseSign cs with
  | some (Sign.pos, cs) =>
    let sign := Sign.pos
    match parseNat cs with
    | some (nat, cs) =>
      match parseFraction cs with
      | some (frac, cs) =>
        match parseExponent cs with
        | some (exp, cs) =>
          dbg_trace "*"
          some ({ sign, nat, frac, exp }, cs) -- (maximally) happy path!
        | none =>
          some ({ sign, nat, frac, exp := 0 }, cs)
      | none =>
        match parseExponent cs with
        | some (exp, cs) =>
          some ({ sign, nat, frac := (0, 0), exp }, cs)
        | none => some ({ sign, nat, frac := (0, 0), exp := 0 }, cs)
    | none => none
  | some (Sign.neg, cs) =>
    let sign := Sign.neg
    match parseNat cs with
    | some (nat, cs) =>
      match parseFraction cs with
      | some (frac, cs) =>
        match parseExponent cs with
        | some (exp, cs) => some ({ sign, nat, frac, exp }, cs)
        | none => some ({ sign, nat, frac, exp := 0 }, cs)
      | none =>
        match parseExponent cs with
        | some (exp, cs) => some ({ sign, nat, frac := (0, 0), exp }, cs)
        | none => some ({ sign, nat, frac := (0, 0), exp := 0 }, cs)
    | none => none
  | none => panic! "unreachable"

def parseNumber := v0.parseNumber

#eval parseNumber "42".toList
-- some ({ sign := Sign.pos, nat := 42, frac := (0, 0), exp := 0 }, [])

#eval parseNumber "3.14".toList
-- some ({ sign := Sign.pos, nat := 3014, frac := (14, 0), exp := 0 }, [])

#eval parseNumber "6.66e+2".toList
-- some ({ sign := Sign.pos, nat := 6, frac := (66, 0), exp := 2 }, [])

#eval parseNumber "-007.700e-100".toList -- BUGGY so far.
-- some ({ sign := Sign.neg, nat := 7, frac := (7, 2), exp := -100 }, [])

/-!
## Parser combinators / higher-order programming.
-/

namespace v1

def Parser.{u} (α : Type u) := List Char → Option (α × List Char)

def Parser.andThen {α β} (p : Parser α) (q : Parser β) : Parser (α × β) :=
  fun (cs : List Char) => match p cs with
    | some (a, cs) => match q cs with
      | some (b, cs) => some ((a, b), cs)
      | none => none
    | none => none

-- Right associativity generates Parser α × (β × γ) which is the same as
-- Parser α × β × γ since × is right associate (and so that's typically
-- what we expect). Try infixl and hover on the def of parseNumber and
-- see what the signature is.
scoped infixr:60 " ⊗ " => Parser.andThen

def parseNumber : Parser Number := fun (cs : List Char) =>
  let rawParseNumber := parseSign ⊗ parseNat ⊗ parseFraction ⊗ parseExponent
  -- We could stop right now actually, there is nothing wrong with parsing
  -- a number as a 4-uple.
  match rawParseNumber cs with
  | some ((sign, nat, frac, exp), cs) => some ({ sign, nat, frac, exp }, cs)
  | none => none

#eval parseNumber "42".toList -- BUGGY!
-- some ({ sign := Sign.pos, nat := 42, frac := (0, 0), exp := 0 }, [])

#eval parseNumber "3.14".toList -- BUGGY!
-- some ({ sign := Sign.pos, nat := 3, frac := (14, 0), exp := 0 }, [])

#eval parseNumber "6.66e+2".toList
-- some ({ sign := Sign.pos, nat := 6, frac := (66, 0), exp := 2 }, [])

#eval parseNumber ".1".toList
-- none

#eval parseNumber "-007.700e-100".toList -- BUGGY so far.
-- some ({ sign := Sign.neg, nat := 7, frac := (7, 2), exp := -100 }, [])

end v1

namespace v2
/-!
TODO: parser from symbol (char)
TODO: optional with default parsed value (ah, require Inhabited to the explicit default?).
TODO: loop with wire in the feedback loop? Aka ZeroOrMore combinator.
-/

def Parser.{u} (α : Type u) := List Char → Option (α × List Char)

def Parser.andThen {α β} (p : Parser α) (q : Parser β) : Parser (α × β) :=
  fun (cs : List Char) => match p cs with
    | some (a, cs) => match q cs with
      | some (b, cs) => some ((a, b), cs)
      | none => none
    | none => none

scoped infixr:60 " ⊗ " => v2.Parser.andThen

def optionally {α} [Inhabited α] (p : Parser α) : Parser α :=
  fun (cs : List Char) =>
    match p cs with
    | none => some (default, cs)
    | other => other

postfix:max "?" => optionally

inductive Sign where
  | pos : Sign
  | neg : Sign
deriving Inhabited, Repr

def parseSign (cs : List Char) : Option (Sign × List Char) :=
  match cs with
  | '+' :: cs => some (Sign.pos, cs)
  | '-' :: cs => some (Sign.neg, cs)
  | _ => none

/-!
This is equivalent to

-/

def parseSign' : Parser Sign :=
  fun cs =>
    match cs with
    | '+' :: cs => some (Sign.pos, cs)
    | '-' :: cs => some (Sign.neg, cs)
    | _ => none

/-!
which can itself be compacted to the super-nice:
-/

def parseSign'' : Parser Sign
  | '+' :: cs => some (Sign.pos, cs)
  | '-' :: cs => some (Sign.neg, cs)
  | _ => none

#eval (parseSign)? "+42".toList
-- some (v2.Sign.pos, ['4', '3'])

#eval (parseSign)? "-42".toList
-- some (v2.Sign.neg, ['4', '3'])

#eval (parseSign)? "42".toList
-- some (v2.Sign.pos, ['4', '2'])

partial def manyAux {α} (p : Parser α) (cs : List Char) (ras : List α) :
    Option (List α × List Char) :=
  match (p cs) with
  | none => some (ras.reverse, cs)
  | some (a, cs) => manyAux p cs (a :: ras)

def many {α} : Parser α -> Parser (List α) := manyAux (ras := [])

postfix:max "*" => many

def parseDigits := (parseDigit)*

def parseE : Parser Unit := fun cs =>
  match cs with
  | 'e' :: cs | 'E' :: cs => some (.unit, cs)
  | _ => none

def Nat.ofDigits (digits : List Nat) : Nat :=
  match digits with
  | [] => 0
  | d :: digits => d * 10^ digits.length + (Nat.ofDigits digits)

/-!
Arf, some of this is wrong, I need "+"" instead of "*"?
I need at least one digit?
-/

def parseExponent (cs : List Char) : Option (Int × List Char) :=
  let rawParseExponent := (parseE ⊗ (parseSign)? ⊗ (parseDigit)*)
  let parseResult := rawParseExponent cs
  match parseResult with
  | none => none
  | some ((_, .pos, digits), cs) =>
    some (digits |> Nat.ofDigits |> Int.ofNat, cs)
  | some ((_, .neg, digits), cs) =>
    some (digits |> Nat.ofDigits |> Int.ofNat |> (-·), cs)

#eval parseExponent "e+42".toList
-- some (42, [])

#eval parseExponent "E-60".toList
-- some (-60, [])

#eval parseExponent "999".toList
-- none

#eval parseExponent "e+100zzz".toList
-- some (100, ['z', 'z', 'z'])

/-!
TODO:

- <|> stuff
-/

end v2

namespace v3

/-! Monads -/

/-! TODO: bind in the Option + State monad and syntactic sugar.

Given the context, that provides:

  - "linear" sequencing of actions

  - decoupling of returning the result of the parse and
    getting/setting/modifying the token stream.

  - automatic do-bloc level fail on any local <- fail.

Redo some elementary constructs with these tools ;
then redo some combinators?

-/
end v3
