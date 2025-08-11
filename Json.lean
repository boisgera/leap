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
  return (hex |> hexStringToNat |> Char.ofNat)

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

  partial def parseArray : Parser Json := do
    _ <- parseLiteral "["
    let elements <- parseElements
    _ <- parseLiteral "]"
    return Json.array elements

  partial def parseMember : Parser (String × Json) := do
    let key_json <- parseString
    let key <- match key_json with
      | Json.string s => some s
      | _ => none -- failure
    parseWhitespace
    _ <- parseLiteral ":"
    parseWhitespace
    let value <- parseElement
    return (key, value)

  partial def parseMembers : Parser (List (String × Json)) := do
    let mut members : List (String × Json) := []
    repeat
      match (parseMember) with
      | none => break
      | some member => members := members ++ [member]
    return members

  partial def parseObject : Parser Json := do
    _ <- parseLiteral "{"
    parseWhitespace
    let members <- parseMembers
    _ <- parseLiteral "}"
    return members |> HashMap.Raw.ofList |> Json.object

end

def Json.parse (input : String) : Option Json := do
  let (json, input) <- parseValue input
  guard input.isEmpty -- input fully consumed
  return json
