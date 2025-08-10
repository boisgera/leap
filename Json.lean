import Lean
import Std

open Std (HashMap)

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

def parseLiteral (literal : String) (input : String) : Option (String × String) := do
  guard (input.startsWith literal)
  return (literal, input.drop literal.length)

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

mutual

  partial def parseElement (input : String) : Option (Json × String) := do
    let input' := input.trimLeft
    let (json, input'') <- parseValue input'
    return (json, input''.trimLeft)

  partial def parseValue (input : String) : Option (Json × String) :=
    parseNull input
    <|> parseBool input
    <|> parseString input
    <|> parseArray input
    <|> parseObject input

  -- one or more, comma-separated values (greedy)
  partial def parseElements (input : String) : Option (List Json × String) := do
    let (json, input) <- parseElement input.trimLeft
    let input := input.trimLeft
    if input.startsWith "," then
      let (elements, input) <- parseElements (input.drop 1)
      return (json :: elements, input.trimLeft)
    else
      return ([json], input)

  partial def parseArray (input : String) : Option (Json × String) := do
    let (_, input) <- parseLiteral "[" input
    let input := input.trimLeft
    if input'.startsWith "]" then
        return (Json.array [], input'.drop 1)
    let (elements, input'') <- parseElements input'
    guard (input''.startsWith "]")
    return (Json.array elements, input''.drop 1)

  partial def parseMember (input : String) : Option ((String × Json) × String) := do
    let (key_json, input) <- parseString input.trimLeft
    let key <- match key_json with
      | Json.string s => some s
      | _ => none -- failure
    let input := input.trimLeft
    let (_, input) <- parseLiteral ":" input
    let input := input.trimLeft
    let (value, input) <- parseElement input
    return ((key, value), input.trimLeft)

  partial def parseMembers (input : String) : Option (List (String × Json) × String) := do
    let mut (member, input) <- parseMember input
    let mut members := [member]
    repeat
      (member, input) <- parseMember input
      members := members ++ [member]
    return (members, input)

  partial def parseObject (input : String) : Option (Json × String) := do
    let (_, input) <- parseLiteral "{" input
    let input := input.trimLeft
    match parseLiteral "}" input with
    | some (_, input) =>
      return ([] |> HashMap.Raw.ofList |> Json.object, input)
    | none =>
      let (members, input) <- parseMembers input
      let (_, input) <- parseLiteral "}" input
      return (members |> HashMap.Raw.ofList |> Json.object, input)

end

def Json.parse (input : String) : Option Json := do
  let (json, input) <- parseElement input
  guard input.isEmpty -- input fully consumed
  return json
