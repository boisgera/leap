


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
  if input == "true" then
    some (Json.bool true)
  else if input == "false" then
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
  if input == "true" then
    some (Json.bool true)
  else if input == "false" then
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
  if input == "true" then
    some (Json.bool true, input.drop 4)
  else if input == "false" then
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
  if input == "true" then
    some (Json.bool true, input.drop 4)
  else if input == "false" then
    some (Json.bool false, input.drop 5)
  else
    none

-- -- We need a more generic version of parseEverything
-- def parseEverything (parser : String → Option (α × String)) (input : String) : Option α :=
--   match parser input with
--   | some (json, rest) => if rest == "" then some json else none
--   | none => none

mutual

  partial def parseValues (input : String) : Option (List Json × String) :=
  sorry -- we need that to be greedy too, right?

  partial def parseArray (input : String) : Option (Json × String) :=
    if input.startsWith "[" then
      match parseValues (input.drop 1) with
      | none => none
      | some (elements, rest) =>
        if rest.startsWith "]" then
          return (Json.array elements, rest.drop 1)
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

#eval Json.parse "null"
-- some (v4.Json.null, "")

#eval parseEverything Json.parse "null"
-- some (v4.Json.null)

#eval Json.parse "null and more"
-- some (v4.Json.null, " and more")

#eval parseEverything Json.parse "null and more"
-- none

#eval Json.parse "false"
-- some (v4.Json.bool false, "")

#eval Json.parse "true"
-- some (v4.Json.bool true, "")

#eval Json.parse "null null"
-- some (v4.Json.null, " null")

#eval Json.parse "  null"
-- none

end v4

namespace v5
/-
Parse whitespace. Two important concept here:
  - in the JSON spec, whitespace is actually *optional* whitespace :
    "" is some whitespace
  - we need our whitespace to match as much as possible (greedyness)

Arf, fuck our whitespace is not represented in the Json structure,
it needs a different signature. Actually can we just use trimLeft?
Does it match the JSON spec?
-/
end v5
