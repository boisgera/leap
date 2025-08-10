import Lean
import Std

open Std (HashMap)
open Lean (AssocList)

namespace v0
/-

  - Objective: parse "null" as a JSON data structure.

  - Use an inductive type to represent
    the JSON data structure

  - deriving repr for convenience.

  - Come up with the idea of using an option type to represent results
    or failure to parse when needed.

-/

inductive Json
| null : Json
deriving Repr

def parseNull (input : String): Option Json :=
  if input == "null" then
    some Json.null
  else
    none

def Json.parse := parseNull

#eval Json.parse "null"
-- some (v0.Json.null)

#eval Json.parse "true"
-- none

#eval Json.parse "null null"
-- none

#eval Json.parse "  null"
-- none

end v0

namespace v1

inductive Json
| null : Json
| bool (b : Bool) : Json
deriving Repr

def parseNull (input : String): Option Json :=
  if input == "null" then
    some Json.null
  else
    none

def parseBool (input : String): Option Json :=
  if input.startsWith "true" then
    some (Json.bool true)
  else if input.startsWith "false" then
    some (Json.bool false)
  else
    none

def Json.parse (input : String): Option Json :=
  match parseNull input with
  | some json => some json
  | none => parseBool input

-- We see the beginning of a nesting pattern here that we'd like a solution
-- to but it's not the usual "return none as soon as you get one" that is
-- nicely encapsulated in the do notation. This is a "try this and if it
-- fails, try that" pattern.

#eval Json.parse "null"
-- some (v1.Json.null)


#eval Json.parse "false"
-- some (v1.Json.bool false)

#eval Json.parse "true"
-- some (v1.Json.bool true)

#eval Json.parse "null null"
-- none

#eval Json.parse "  null"
-- none

end v1


namespace v2

inductive Json
| null : Json
| bool (b : Bool) : Json
deriving Repr

def parseNull (input : String): Option Json :=
  if input == "null" then
    some Json.null
  else
    none

def parseBool (input : String): Option Json :=
  if input.startsWith "true" then
    some (Json.bool true)
  else if input.startsWith "false" then
    some (Json.bool false)
  else
    none

def Json.parse (input : String) : Option Json := -- orElse pattern
   parseNull input <|> parseBool input

#eval Json.parse "null"
-- some (v2.Json.null)


#eval Json.parse "false"
-- some (v2.Json.bool false)

#eval Json.parse "true"
-- some (v2.Json.bool true)

#eval Json.parse "null null"
-- none

#eval Json.parse "  null"
-- none

end v2


namespace v3

/-
Preparing the introduction of arrays and/or whitespace;
facing the issue that we need to change the signature
of our parser to account for some *partial* success in the
parsing of the input string.

Not a big deal since we can generically build a "total parser" on top of
a partial one if needed.

-/

inductive Json
| null : Json
| bool (b : Bool) : Json
deriving Repr

def parseNull (input : String): Option (Json × String) :=
  if input.startsWith "null" then
    some (Json.null, input.drop 4)
  else
    none

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

def Json.parse (input : String) : Option (Json × String) :=
   parseNull input <|> parseBool input

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval Json.parse "null"
-- some (v3.Json.null, "")

#eval parseEverything Json.parse "null"
-- some (v3.Json.null)

#eval Json.parse "null and more"
-- some (v3.Json.null, " and more")

#eval parseEverything Json.parse "null and more"
-- none

#eval Json.parse "false"
-- some (v3.Json.bool false, "")

#eval Json.parse "true"
-- some (v3.Json.bool true, "")

#eval Json.parse "null null"
-- some (v3.Json.null, " null")

#eval Json.parse "  null"
-- none

end v3

namespace v4
/-
Introduction of arrays (without whitespace). -> Need for mutually recursive
functions!
-/

inductive Json
| null : Json
| bool (b : Bool) : Json
| array (elements : List Json) : Json
deriving Repr

def parseNull (input : String): Option (Json × String) :=
  if input.startsWith "null" then
    some (Json.null, input.drop 4)
  else
    none

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

mutual

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) :=
    match Json.parse input with
    | none => none
    | some (json, rest) =>
      if rest.startsWith "," then
        match parseValues (rest.drop 1) with
        | none => none
        | some (elements, rest) => some (json :: elements, rest)
      else
        some ([json], rest)

  -- TODO: again here we kinda see some "monadic" pattern emerge...

  -- TODO: don't we have higher order patterns that could come in handy here?
  -- Like I want that, then that then that? (or I fail). That should be
  -- (almost?) exactly the monadic stuff on options (?)
  partial def parseArray (input : String) : Option (Json × String) :=
    if input.startsWith "[" then
      let rest := input.drop 1
      if rest.startsWith "]" then
          pure (Json.array [], rest.drop 1)
      else
        match parseValues rest with
        | none => none
        | some (elements, rest) =>
          if rest.startsWith "]" then
            pure (Json.array elements, rest.drop 1)
          else
            none
    else
      none

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input <|> parseBool input <|> parseArray input

end

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval Json.parse "[null]"
-- some (v4.Json.array [v4.Json.null], "")

#eval Json.parse "[null,null]"
-- some (v4.Json.array [v4.Json.null, v4.Json.null], "")

#eval Json.parse "true"
-- some (v4.Json.bool true, "")

#eval Json.parse "[true]"
-- some (v4.Json.array [v4.Json.bool true], "")

#eval Json.parse "[]"
-- some (v4.Json.array [], "")

#eval Json.parse "[null,false,true]"
-- some (v4.Json.array [v4.Json.null, v4.Json.bool false, v4.Json.bool true], "")

end v4


namespace v5
/-
Introduction of arrays (without whitespace). -> Need for mutually recursive
functions!
-/

inductive Json
| null : Json
| bool (b : Bool) : Json
| array (elements : List Json) : Json
deriving Repr

def parseNull (input : String): Option (Json × String) :=
  if input.startsWith "null" then
    some (Json.null, input.drop 4)
  else
    none

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

mutual

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) := do
    let (json, input') <- Json.parse input
    if input'.startsWith "," then
      let (elements, input'') <- parseValues (input'.drop 1)
      return (json :: elements, input'')
    else
      return ([json], input')

  -- Is there no way to get rid of the "else none" here? If the actual type
  -- was m Unit that would work ... YES! See the guarded version below.
  partial def parseArray₀ (input : String) : Option (Json × String) := do
    if input.startsWith "[" then
      let input' := input.drop 1
      if input'.startsWith "]" then
          return (Json.array [], input'.drop 1)
      let (elements, input'') <- parseValues input'
      if input''.startsWith "]" then
        return (Json.array elements, input''.drop 1)
      else
        none
    else
      none

  partial def parseArray₁ (input : String) : Option (Json × String) := do
    guard (input.startsWith "[")
    let input' := input.drop 1
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseValues input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def parseArray := parseArray₁

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input <|> parseBool input <|> parseArray input

end

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval Json.parse "[null]"
-- some (v5.Json.array [v5.Json.null], "")

#eval Json.parse "[null,null]"
-- some (v5.Json.array [v5.Json.null, v5.Json.null], "")

#eval Json.parse "true"
-- some (v5.Json.bool true, "")

#eval Json.parse "[true]"
-- some (v5.Json.array [v5.Json.bool true], "")

#eval Json.parse "[]"
-- some (v5.Json.array [], "")

#eval Json.parse "[null,false,true]"
-- some (v5.Json.array [v5.Json.null, v5.Json.bool false, v5.Json.bool true], "")

#eval Json.parse "[[],[],[[null]]]"

end v5






namespace v6

/-
Parse whitespace. Two important concept here:
  - in the JSON spec, whitespace is actually *optional* whitespace :
    "" is some whitespace
  - we need our whitespace to match as much as possible (greedyness)

Arf, fuck our whitespace is not represented in the Json structure,
it needs a different signature. Actually can we just use trimLeft?
Does it match the JSON spec? Apparenrtly, yes.

But's that's a bit hackish/ugly since it does not really give to WhiteSpace
the same parser status than the other blocks ... Make a real parser out of
Whitespace in the sequel?

We *could* introduce some

-- TODO: understand that like in the JSON spec, that's OPTIONAL whitespace
def parseWhitespace (input : String) : Option (Unit × String) :=
  return ((), input.trimLeft)

but AFAICT, it is not worth it unless we manage to get a proper parser
combinator framework on top of all this (later?).
-/

inductive Json
| null : Json
| bool (b : Bool) : Json
| array (elements : List Json) : Json
deriving Repr

-- Not used. trimLeft is all we need ATM
def String.isWhiteSpace (s : String) : Bool :=
  s |>.toList |>.all Char.isWhitespace


def parseNull (input : String): Option (Json × String) := do
  guard (input.startsWith "null")
  return (Json.null, input.drop 4)

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

mutual

  partial def parseValue (input : String) : Option (Json × String) := do
    let input' := input.trimLeft
    let (json, input'') <-
      parseNull input'
      <|> parseBool input'
      <|> parseNumber input'
      <|> parseArray input'
    return (json, input''.trimLeft)

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) := do
    let (json, input) <- Json.parse input.trimLeft
    let input := input.trimLeft
    if input.startsWith "," then
      let (elements, input) <- parseValues (input.drop 1)
      return (json :: elements, input.trimLeft)
    else
      return ([json], input)

  partial def parseArray (input : String) : Option (Json × String) := do
    guard (input.startsWith "[")
    let input' := (input.drop 1).trimLeft
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseValues input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input <|> parseBool input <|> parseArray input

end

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval parseValue "  [null, [true\n, \n false, [ ] ]   ]   "
-- some (v6.Json.array [v6.Json.null, v6.Json.array [v6.Json.bool true, v6.Json.bool false, v6.Json.array []]], "")


end v6


namespace v7

/-
Parse numbers (as Float or as a custom structure? Let's say Float for now).
-/


inductive Json
| null : Json
| bool (b : Bool) : Json
| number (n : Float) : Json
| array (elements : List Json) : Json
deriving Repr


def parseNull (input : String): Option (Json × String) := do
  guard (input.startsWith "null")
  return (Json.null, input.drop 4)

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

def parseSign (input : String) : Option (Float × String) :=
  if input.startsWith "-" then
    some (-1.0, input.drop 1)
  else
    some (1.0, input)

def parseDigit (input : String) : Option (Nat × String) := do
  let char <- input.get? 0
  guard char.isDigit
  let digit := char.toNat - '0'.toNat
  return (digit, input.drop 1)

def parseInteger (input : String) : Option (Float × String) := do
  let (first, input) <- parseDigit input
  if first == 0 then
    return (0, input)
  else
    let mut current := first.toFloat
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current * 10 + digit.toFloat
        input := input_
      | none => break
    return (current, input)

#eval parseInteger "123"
-- some (123, "")

#eval parseInteger "-123"
-- some (-123, "")

#eval parseInteger "0123"
-- some (0, "123")

def parseFraction (input : String) : Option (Float × String) := do
  if input.startsWith "." then
    let input := input.drop 1
    let mut current := 0.0
    let mut factor := 0.1
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current + factor * digit.toFloat
        factor := factor / 10.0
        input := input_
      | none => break
    return (current, input)
  else
    return (0.0, input)

#eval parseFraction ".123"
-- some (0.123000, "")

-- TODO: + is allowed in sign there, need to adapt.
def parseExponent (input : String) : Option (Float × String) := do
  if (input.startsWith "e" || input.startsWith "E") then
    let input := input.drop 1
    let (sign, input) <- parseSign input
    let mut (integer, input) <- parseInteger input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        integer := integer * 10 + digit.toFloat
        input := input_
      | none => break
    return (10.0 ^ (sign * integer), input)
  else
    return (1.0, input)

def parseNumber (input : String) : Option (Json × String) := do
  let (sign, input) <- parseSign input
  let (integer, input) <- parseInteger input
  let (fraction, input) <- parseFraction input
  let (exponent, input) <- parseExponent input
  return (Json.number (sign * (integer + fraction) * exponent), input)

#eval parseNumber "123.456e-2"
-- some (1.234560, "")

#eval parseNumber "123.456"
-- some (123.456000, "")

#eval parseNumber "-123.456e2"
-- some (-12345.6000000, "")

#eval parseNumber "-123.456e007"
-- some (-1234560000.000000, "")


mutual

  partial def parseValue (input : String) : Option (Json × String) := do
    let input' := input.trimLeft
    let (json, input'') <- parseNull input' <|> parseBool input' <|> parseArray input'
    return (json, input''.trimLeft)

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) := do
    let (json, input) <- Json.parse input.trimLeft
    let input := input.trimLeft
    if input.startsWith "," then
      let (elements, input) <- parseValues (input.drop 1)
      return (json :: elements, input.trimLeft)
    else
      return ([json], input)

  partial def parseArray (input : String) : Option (Json × String) := do
    guard (input.startsWith "[")
    let input' := (input.drop 1).trimLeft
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseValues input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input
    <|> parseBool input
    <|> parseNumber input
    <|> parseArray input

end

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval parseValue "[1.0, 3.14, null, true, 1e-3]"

end v7

namespace v8


inductive Json
| null : Json
| bool (b : Bool) : Json
| number (n : Float) : Json
| string (s : String) : Json
| array (elements : List Json) : Json
deriving Repr

def parseNull (input : String): Option (Json × String) := do
  guard (input.startsWith "null")
  return (Json.null, input.drop 4)

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

def parseSign (input : String) : Option (Float × String) :=
  if input.startsWith "-" then
    some (-1.0, input.drop 1)
  else
    some (1.0, input)

def parseDigit (input : String) : Option (Nat × String) := do
  let char <- input.get? 0
  guard char.isDigit
  let digit := char.toNat - '0'.toNat
  return (digit, input.drop 1)

def parseInteger (input : String) : Option (Float × String) := do
  let (first, input) <- parseDigit input
  if first == 0 then
    return (0, input)
  else
    let mut current := first.toFloat
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current * 10 + digit.toFloat
        input := input_
      | none => break
    return (current, input)

def parseFraction (input : String) : Option (Float × String) := do
  if input.startsWith "." then
    let input := input.drop 1
    let mut current := 0.0
    let mut factor := 0.1
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current + factor * digit.toFloat
        factor := factor / 10.0
        input := input_
      | none => break
    return (current, input)
  else
    return (0.0, input)

-- TODO: + is allowed in sign there, need to adapt.
def parseExponent (input : String) : Option (Float × String) := do
  if (input.startsWith "e" || input.startsWith "E") then
    let input := input.drop 1
    let (sign, input) <- parseSign input
    let mut (integer, input) <- parseInteger input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        integer := integer * 10 + digit.toFloat
        input := input_
      | none => break
    return (10.0 ^ (sign * integer), input)
  else
    return (1.0, input)

def parseNumber (input : String) : Option (Json × String) := do
  let (sign, input) <- parseSign input
  let (integer, input) <- parseInteger input
  let (fraction, input) <- parseFraction input
  let (exponent, input) <- parseExponent input
  return (Json.number (sign * (integer + fraction) * exponent), input)

def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c ∧ c ≤ '9') ∨
  ('a' ≤ c ∧ c ≤ 'f') ∨
  ('A' ≤ c ∧ c ≤ 'F')

def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    10 + (c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    10 + (c.toNat - 'A'.toNat)
  else
    panic! s!"Invalid hex character: {c}"

def hexStringToNat (s : String) : Nat :=
  s.foldl (init := 0) fun acc c =>
    let d := hexCharToNat c
    acc * 16 + d

#eval hexStringToNat "0041"
-- 65

-- TODO: deal with surrogate pairs???
def parseString (input : String) : Option (Json × String) := do
  guard (input.startsWith "\"")
  let mut input := input.drop 1
  let mut string := ""
  repeat
    let char <- input.get? 0
    input := input.drop 1
    match char with
    | '"' =>
      --input := input.drop 1
      break
    | '\\' =>
      let next <- input.get? 0
      match next with
      | '"' => input := input.drop 1; string := string ++ "\""
      | '\\' => input := input.drop 1; string := string ++ "\\"
      | '/' => input := input.drop 1; string := string ++ "/"
      | 'b' => input := input.drop 1; string := string ++ "\u232B"
      | 'f' => input := input.drop 1; string := string ++ "\u240C"
      | 'n' => input := input.drop 1; string := string ++ "\n"
      | 'r' => input := input.drop 1; string := string ++ "\r"
      | 't' => input := input.drop 1; string := string ++ "\t"
      | 'u' =>
        input := input.drop 1
        let hex := input.take 4
        if hex.length == 4 && hex.all isHexDigit then
          input := input.drop 4
          string := string ++ (hex |> hexStringToNat |> Char.ofNat |>.toString)
        else
          none -- failure
      | _ => none -- failure
    | _ => string := string ++ char.toString
  return (Json.string string, input)

#eval parseString r#""Hello!""#
-- some (v8.Json.string "Hello!", "")

#eval parseString r#""😊""#
-- some (v8.Json.string "😊", "")

#eval parseString r#""\n\r\t""#
-- some (v8.Json.string "\n\x0d\t", "")

#eval parseString r#""\u0041""#
-- some (v8.Json.string "A", "")

mutual

  partial def parseValue (input : String) : Option (Json × String) := do
    let input' := input.trimLeft
    let (json, input'') <- Json.parse input'
    return (json, input''.trimLeft)

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) := do
    let (json, input) <- Json.parse input.trimLeft
    let input := input.trimLeft
    if input.startsWith "," then
      let (elements, input) <- parseValues (input.drop 1)
      return (json :: elements, input.trimLeft)
    else
      return ([json], input)

  partial def parseArray (input : String) : Option (Json × String) := do
    guard (input.startsWith "[")
    let input' := (input.drop 1).trimLeft
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseValues input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input
    <|> parseBool input
    <|> parseNumber input
    <|> parseString input
    <|> parseArray input
end

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval parseValue r#"[1.0, 3.14, null, true, 1e-3, "Hello!"]"#
-- some (v8.Json.array
--    [v8.Json.number 1.000000,
--     v8.Json.number 3.140000,
--     v8.Json.null,
--     v8.Json.bool true,
--     v8.Json.number 0.001000,
--     v8.Json.string "Hello!"],
--  "")
end v8


namespace v9
-- Objects!

-- TODO: the list for object is not really nice, but HashMap
--       won't work for positivity reasons (???) and AssocList
--       is from Lean, not std, has no repr, etc.
--       Let's use the list first and later come with my own
--       "Object" custom type (?) for a better API.


inductive Json
| null : Json
| bool (b : Bool) : Json
| number (n : Float) : Json
| string (s : String) : Json
| array (elements : List Json) : Json
| object (members : HashMap.Raw String Json) : Json
deriving Repr

def parseNull (input : String): Option (Json × String) := do
  guard (input.startsWith "null")
  return (Json.null, input.drop 4)

def parseBool (input : String): Option (Json × String) :=
  if input.startsWith "true" then
    some (Json.bool true, input.drop 4)
  else if input.startsWith "false" then
    some (Json.bool false, input.drop 5)
  else
    none

def parseSign (input : String) : Option (Float × String) :=
  if input.startsWith "-" then
    some (-1.0, input.drop 1)
  else
    some (1.0, input)

def parseDigit (input : String) : Option (Nat × String) := do
  let char <- input.get? 0
  guard char.isDigit
  let digit := char.toNat - '0'.toNat
  return (digit, input.drop 1)

def parseInteger (input : String) : Option (Float × String) := do
  let (first, input) <- parseDigit input
  if first == 0 then
    return (0, input)
  else
    let mut current := first.toFloat
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current * 10 + digit.toFloat
        input := input_
      | none => break
    return (current, input)

def parseFraction (input : String) : Option (Float × String) := do
  if input.startsWith "." then
    let input := input.drop 1
    let mut current := 0.0
    let mut factor := 0.1
    let mut input := input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        current := current + factor * digit.toFloat
        factor := factor / 10.0
        input := input_
      | none => break
    return (current, input)
  else
    return (0.0, input)

-- TODO: + is allowed in sign there, need to adapt.
def parseExponent (input : String) : Option (Float × String) := do
  if (input.startsWith "e" || input.startsWith "E") then
    let input := input.drop 1
    let (sign, input) <- parseSign input
    let mut (integer, input) <- parseInteger input
    repeat
      let next? := parseDigit input
      match next? with
      | some (digit, input_) =>
        integer := integer * 10 + digit.toFloat
        input := input_
      | none => break
    return (10.0 ^ (sign * integer), input)
  else
    return (1.0, input)

def parseNumber (input : String) : Option (Json × String) := do
  let (sign, input) <- parseSign input
  let (integer, input) <- parseInteger input
  let (fraction, input) <- parseFraction input
  let (exponent, input) <- parseExponent input
  return (Json.number (sign * (integer + fraction) * exponent), input)

def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c ∧ c ≤ '9') ∨
  ('a' ≤ c ∧ c ≤ 'f') ∨
  ('A' ≤ c ∧ c ≤ 'F')

def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    10 + (c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    10 + (c.toNat - 'A'.toNat)
  else
    panic! s!"Invalid hex character: {c}"

def hexStringToNat (s : String) : Nat :=
  s.foldl (init := 0) fun acc c =>
    let d := hexCharToNat c
    acc * 16 + d

#eval hexStringToNat "0041"
-- 65

-- TODO: deal with surrogate pairs???
def parseString (input : String) : Option (Json × String) := do
  guard (input.startsWith "\"")
  let mut input := input.drop 1
  let mut string := ""
  repeat
    let char <- input.get? 0
    input := input.drop 1
    match char with
    | '"' =>
      --input := input.drop 1
      break
    | '\\' =>
      let next <- input.get? 0
      match next with
      | '"' => input := input.drop 1; string := string ++ "\""
      | '\\' => input := input.drop 1; string := string ++ "\\"
      | '/' => input := input.drop 1; string := string ++ "/"
      | 'b' => input := input.drop 1; string := string ++ "\u232B"
      | 'f' => input := input.drop 1; string := string ++ "\u240C"
      | 'n' => input := input.drop 1; string := string ++ "\n"
      | 'r' => input := input.drop 1; string := string ++ "\r"
      | 't' => input := input.drop 1; string := string ++ "\t"
      | 'u' =>
        input := input.drop 1
        let hex := input.take 4
        if hex.length == 4 && hex.all isHexDigit then
          input := input.drop 4
          string := string ++ (hex |> hexStringToNat |> Char.ofNat |>.toString)
        else
          none -- failure
      | _ => none -- failure
    | _ => string := string ++ char.toString
  return (Json.string string, input)

#eval parseString r#""Hello!""#
-- some (v9.Json.string "Hello!", "")

#eval parseString r#""😊""#
-- some (v9.Json.string "😊", "")

#eval parseString r#""\n\r\t""#
-- some (v9.Json.string "\n\x0d\t", "")

#eval parseString r#""\u0041""#
-- some (v9.Json.string "A", "")

mutual

  partial def parseValue (input : String) : Option (Json × String) := do
    let input' := input.trimLeft
    let (json, input'') <- Json.parse input'
    return (json, input''.trimLeft)

  -- one or more, comma-separated values (greedy)
  partial def parseValues (input : String) : Option (List Json × String) := do
    let (json, input) <- Json.parse input.trimLeft
    let input := input.trimLeft
    if input.startsWith "," then
      let (elements, input) <- parseValues (input.drop 1)
      return (json :: elements, input.trimLeft)
    else
      return ([json], input)

  partial def parseArray (input : String) : Option (Json × String) := do
    guard (input.startsWith "[")
    let input' := (input.drop 1).trimLeft
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseValues input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def parseMembers (input : String) : Option (List (String × Json) × String) := do
    let mut members := []
    let mut input := input.trimLeft
    repeat
      let (key_json, input') <- parseString input
      let key <- match key_json with
        | Json.string s => some s
        | _ => none -- failure
      input := input'.trimLeft
      guard (input.startsWith ":")
      input := (input.drop 1).trimLeft
      let (value, input') <- Json.parse input
      input := input'.trimLeft
      members := (key, value) :: members
      if !input.startsWith "," then
        break
      input := (input.drop 1).trimLeft
    return (members.reverse, input)

  partial def parseObject (input : String) : Option (Json × String) := do
    guard (input.startsWith "{")
    let input := (input.drop 1).trimLeft
    if input.startsWith "}" then
      return (Json.object [], input.drop 1)
    let (members, input) <- parseMembers input
    guard (input.startsWith "}")
    return (Json.object members, input.drop 1)

  partial def Json.parse (input : String) : Option (Json × String) :=
    parseNull input
    <|> parseBool input
    <|> parseNumber input
    <|> parseString input
    <|> parseArray input
    <|> parseObject input
end

#eval parseMembers r#""a": 1, "b": 2, "c": 3"#
-- some ([("a", v9.Json.number 1.000000), ("b", v9.Json.number 2.000000), ("c", v9.Json.number 3.000000)], "")

def parseEverything (parser : String → Option (Json × String)) (input : String) : Option Json :=
  match parser input with
  | some (json, rest) => if rest == "" then some json else none
  | none => none

#eval parseValue r#"{"a": 1}"#
-- some (v9.Json.object [("a", v9.Json.number 1.000000)], "")

#eval parseValue r#"{"a": 1, "b": 2}"#
-- some (v9.Json.object [("a", v9.Json.number 1.000000), ("b", v9.Json.number 2.000000)], "")

#eval parseValue r#"{"a": 1, "b": 2, "c": 3}"#
-- some (v9.Json.object [("a", v9.Json.number 1.000000), ("b", v9.Json.number 2.000000), ("c", v9.Json.number 3.000000)], "")

#eval parseValue r#"{"a": 1, "b": "Hello!", "c": true, "d": {}}"#
-- some (v9.Json.object
--    [("a", v9.Json.number 1.000000), ("b", v9.Json.string "Hello!"), ("c", v9.Json.bool true), ("d", v9.Json.object [])],
--  "")

end v9
