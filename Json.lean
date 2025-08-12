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
deriving Repr, Inhabited

abbrev Parser := StateT String Option

def parseLiteral (literal : String) : Parser String := do
  let input <- get
  guard (input.startsWith literal)
  set (input.drop literal.length)
  return literal

#eval parseLiteral "hello" "hello world"
-- some ("hello", " world")

#eval parseLiteral "hello" "world"
-- none

def parseNull : Parser Json := do
  _ <- parseLiteral "null"
  return Json.null

#eval parseNull "null" -- some Json.null
#eval parseNull "nullabc" -- some Json.null
#eval parseNull "abc" -- none

def parseBool : Parser Json := do
  let keyword <- (parseLiteral "true") <|> (parseLiteral "false")
  match keyword with
  | "true" => return Json.bool true
  | "false" => return Json.bool false
  | _ => return panic! "unreachable"

def parseSign : Parser Float := do
  let signStr <- (parseLiteral "-") <|> (parseLiteral "")
  match signStr with
  | "-" => return -1.0
  | "" => return 1.0
  | _ => return panic! "unreachable"

def parseDigit : Parser Nat := do
  let input <- get
  let char <- input.get? 0
  guard char.isDigit
  set (input.drop 1)
  let digit := char.toNat - '0'.toNat
  return digit


-- TODO: generalize with prefix, postfix and separator
-- (and a trailing sep option?) to help parse arrays and
-- objects. Adapt oneOrMore afterwards.
def zeroOrMore {α : Type} (p : Parser α) : Parser (List α) := do
  let mut out : List α := []
  repeat
    let input <- get
      match p input with
      | none => break
      | some (a, input) =>
        set input
        out := a :: out
  return out.reverse

-- TODO: test with more abstract version where we try to parse directly
--       if the none appears, do we get out of the function of the repeat
--       block? Can we avoid that with an extra "do"?

#eval zeroOrMore (parseLiteral "a") "aaabbb"
-- some (["a", "a", "a"], "bbb")
#eval zeroOrMore (parseLiteral "a") "bbb"
-- some ([], "bbb")

def oneOrMore {α : Type} (p : Parser α) : Parser (List α) := do
  let head <- p
  let tail <- zeroOrMore p
  return head :: tail

#eval zeroOrMore (parseLiteral "a") "aaabbb"
-- some (["a", "a", "a"], "bbb")
#eval zeroOrMore (parseLiteral "a") "bbb"
-- some ([], "bbb")

def parseInteger : Parser Float := do
  let first <- parseDigit
  if first == 0 then
    return 0.0
  else
    let digits <- oneOrMore parseDigit
    return digits |> List.foldl (· * 10 + ·) first |>.toFloat

#eval parseInteger "123abc"
-- some (123.0, "abc")
#eval parseInteger "0abc"
-- some (0.0, "abc")
#eval parseInteger "0123abc"
-- some (123.0, "abc")

def Optional {α} (p : Parser α) : Parser (Option α) := do
  let input <- get
  match p input with
  | none => return none
  | some (a, input) =>
    set input
    return some a

def parseFraction : Parser Float := do
  match (<- Optional (parseLiteral ".")) with
  | none => return 0.0
  | some _ =>
    let digits <- zeroOrMore parseDigit
    return digits |> List.foldr (·.toFloat / 10.0 + · / 10.0) 0.0

-- TODO: + is allowed in sign there, need to adapt / generalize parseSign
def parseExponent : Parser Float := do
  match <- Optional (parseLiteral "e" <|> parseLiteral "E") with
  | none => return 1.0
  | some _ =>
    let sign <- parseSign
    let digits <- oneOrMore parseDigit
    return sign * (digits |> List.foldl (· * 10 + ·) 0 |>.toFloat)

def parseNumber : Parser Json := do
  let sign <- parseSign
  let integer <- parseInteger
  let fraction <- parseFraction
  let exponent  <- parseExponent
  let number := sign * (integer + fraction) * (10.0 ^ exponent)
  return Json.number number

def Char.isHexDigit (c : Char) : Bool :=
  ('0' ≤ c ∧ c ≤ '9') ∨
  ('a' ≤ c ∧ c ≤ 'f') ∨
  ('A' ≤ c ∧ c ≤ 'F')

def hexCharToNat? (c : Char) : Option Nat := do
  if '0' ≤ c ∧ c ≤ '9' then
    return c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    return 10 + (c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    return 10 + (c.toNat - 'A'.toNat)
  else
    none

partial def hexStringToNat? (s : String) : Option Nat :=
  List.foldl (do
    let a <- ·
    let n <- hexCharToNat? ·
    return a * 16 + n
  ) (some 0) s.toList

def hexStringToNat! (s : String) : Nat :=
  match hexStringToNat? s with
  | some n => n
  | none => panic! "Invalid hex string: " ++ s

#eval hexStringToNat! "0041"

#eval hexStringToNat! "ff"

#eval hexStringToNat! "100"

def parseHexDigit : Parser Char := do
  let input <- get
  let char <- input.get? 0
  guard (char.isHexDigit)
  set (input.drop 1)
  return char

def exactly {α} (n : Nat) (p : Parser α) : Parser (List α) := do
  let mut result := []
  for _ in [0:n] do
    let elt <- p
    result := result ++ [elt]
  return result

def parse4HexDigits : Parser String := do
  let hexDigits <- exactly 4 parseHexDigit
  return String.mk hexDigits

-- TODO: handle surrogate pairs
def parseUnicodeCharacter : Parser Char := do
  _ <- parseLiteral "\\u"
  let hex <- parse4HexDigits
  return (hex |> hexStringToNat! |> Char.ofNat)

def parseEscapedCharacter : Parser Char := do
  _ <- parseLiteral "\\"
  let input <- get
  let char <- input.get? 0
  match char with
  | '"' => set (input.drop 1); return '"'
  | '\\' => set (input.drop 1); return '\\'
  | '/' => set (input.drop 1); return '/'
  | 'b' => set (input.drop 1); return '\u232B' -- backspace
  | 'f' => set (input.drop 1); return '\u240C' -- form feed
  | 'n' => set (input.drop 1); return '\n'
  | 'r' => set (input.drop 1); return '\r'
  | 't' => set (input.drop 1); return '\t'
  | _ => none

def parseAnyCharacter : Parser Char := do
  let input <- get
  let char <- input.get? 0
  guard (char != '"' && char != '\\')
  set (input.drop 1)
  return char

def parseCharacter : Parser Char :=
  parseEscapedCharacter <|> parseUnicodeCharacter <|> parseAnyCharacter

def parseString : Parser Json := do
  _ <- parseLiteral "\""
  let chars <- zeroOrMore parseCharacter
  _ <- parseLiteral "\""
  return Json.string (String.mk chars)

-- Should I return the whitespace string instead of ()?
partial def parseWhitespace : Parser Unit := do
  modify (·.trimLeft)

mutual

  partial def parseElement : Parser Json := do
    parseWhitespace
    let json <- parseValue
    parseWhitespace
    return json

  partial def parseValue : Parser Json := do
    (
      parseNull
      <|> parseBool
      <|> parseNumber
      <|> parseString
      <|> parseArray
      <|> parseObject
    )

  -- one or more, comma-separated values (greedy)
  partial def parseElements : Parser (List Json) := do
    let json <- parseElement
    let input <- get
    if input.startsWith "," then
      let elements <- parseElements
      parseWhitespace
      return json :: elements
    else
      parseWhitespace
      return json :: []

  -- BUG: we did not handle the case where the array is empty
  partial def parseArray : Parser Json := do
    _ <- parseLiteral "["
    let elements <- parseElements
    _ <- parseLiteral "]"
    return Json.array elements

  partial def parseMember : Parser (String × Json) := do
    parseWhitespace
    let key_json <- parseString
    let key <- match key_json with
      | Json.string s => some s
      | _ => none -- failure
    parseWhitespace
    _ <- parseLiteral ":"
    parseWhitespace
    let value <- parseElement
    return (key, value)

  partial def parseCommaMember : Parser (String × Json) := do
    _ <- parseLiteral ","
    let member <- parseMember
    return member

  partial def parseMembers : Parser (List (String × Json)) := do
    let member <- parseMember
    let members <- zeroOrMore parseCommaMember
    return member :: members

  partial def parseEmptyObjectAsList : Parser (List (String × Json)) := do
    _ <- parseLiteral "{"
    parseWhitespace
    _ <- parseLiteral "}"
    return []

  partial def parseNonEmptyObjectAsList : Parser (List (String × Json)) := do
    _ <- parseLiteral "{"
    let members <- parseMembers
    _ <- parseLiteral "}"
    return members

  partial def parseObject : Parser Json := do
    let list <- parseEmptyObjectAsList <|> parseNonEmptyObjectAsList
    return (list |> HashMap.Raw.ofList |> Json.object)

end

-- We use parseElement rather than parseValue (trimmed string)
-- That's probably more convenient for the end user
def Json.parse? (input : String) : Option Json := do
  let (json, input) <- parseElement input
  guard input.isEmpty -- input fully consumed
  return json

#eval Json.parse? r#"
{
  "iss_position": {
    "latitude": "38.9459",
    "longitude": "-96.0481"
  },
  "message": "success",
  "timestamp": 1754944042
}
"#

#eval parseValue r#"{
"iss_position": {"latitude": "38.9459", "longitude": "-96.0481"}, "message": "success", "timestamp": 1754944042}"#

#eval Json.parse? r#"{"iss_position": null, "message": "success", "timestamp": 1}"#

#eval Json.parse? "1"

#eval Json.parse? r#"{"latitude": "38.9459", "longitude": "-96.0481"}"#

#eval parseObject r#"{"latitude": "38.9459", "longitude": "-96.0481"}"#

#eval parseMembers r#""latitude": "38.9459", "longitude": "-96.0481""#

#eval parseCommaMember r#", "longitude": "-96.0481""#

#eval parseMember r#"  "longitude": "-96.0481"        "#
