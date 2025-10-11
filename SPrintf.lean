
/-
Do a function that (type-)*safely* associate to a format string a concatenation
function?

E.g.
  - "Hello!" -> "Hello!"
  - "Hello ·!" -> ("Hello " ++ ·)
  - "(·, ·)" -> ("(" ++ · ++ ", " ++ · ")")

TODO: escape

-/


/-
TODO:
  - parse string into format
  - fun that maps format into appropriate function type
  - implementation
-/

/- Random idea : do everything in one step ? Mmm hard wrt to the
type-dependent return type afaict -/

/-
Note: the parser is super easy right, it's a splitOn !!!
-/

namespace v0

def Format := List String /- The holes are between the strings -/


def Formatter (format : Format) : Type :=
  match format with
  | [] => String
  | [_] => String
  | _ :: format => String -> Formatter format

def formatter (format : List String) : Formatter format :=
  match format with
  | [] => ""
  | s :: [] => s
  | s :: s' :: format =>
    fun h => formatter  ((s ++ h ++ s') :: format)

-- Type mismatch
--   formatter ((s ++ h ++ s') :: format)
-- has type
--   Formatter ((s ++ h ++ s') :: format)
-- but is expected to have type
--   Formatter (s' :: format)


end v0

namespace v1


def Format := List String /- The holes are between the strings -/

def Formatter (n : Nat) : Type :=
  match n with
  | 0 | 1 => String
  | n + 2 => String -> Formatter (n + 1)

def formatter (format : List String) : Formatter format.length :=
  match format with
  | [] => ""
  | [s] => s
  | s :: s' :: format =>
    fun h => formatter  ((s ++ h ++ s') :: format)
termination_by format.length

#eval formatter ["A"]
-- "A"

#eval formatter ["A", "B"] "C"
-- "ACB"

#eval formatter ["A ", " B ", " C"] "D" "E"
-- "A D B E C"

#check formatter ["A ", " B ", " C"]
-- formatter ["A ", " B ", " C"] : Formatter ["A ", " B ", " C"].length


#eval formatter ["Hello ", "! ", ""] "world" "👋"
-- "Hello world! 👋"


def format (formatString : String) :=
  formatter (formatString.splitOn "·")

#check cast
-- cast.{u} {α β : Sort u} (h : α = β) (a : α) : β

-- I have some proof + cast to do here AFAICT.
-- The issue is that I have to distinguish if we do have a fun type.
-- (it depends in the fact that there are holes or not ...)
-- do theorems about that!

#eval format "I can't · my ·!" "feel" "legs"
-- Function expected at
--   format "I can't · my ·!"
-- but this term has type
--   Formatter ("I can't · my ·!".splitOn "·").length

def f : Formatter 3 := format "I can't · my ·!"
-- Type mismatch
--   format "I can't · my ·!"
-- has type
--   Formatter ("I can't · my ·!".splitOn "·").length
-- but is expected to have type
--   Formatter 3

-- Ideas; prove equality ("I can't · my ·!".splitOn "·").length = 3,
-- use a cast afterwards to get format "I can't · my ·!" as a
-- Formatter 3? (cast is a macro)

#eval format "Hello ·! ·" "world" "👋"
-- Function expected at
--   format "Hello ·! ·"
-- but this term has type
--   Formatter ("Hello ·! ·".splitOn "·").length

-- Note: Expected a function because this term is being applied to the argument
--   "world"

end v1

namespace v2

def Format := List String /- The holes are between the strings -/

def Formatter (n : Nat) : Type :=
  match n with
  | 0 => String
  | 1 => String
  | n + 2 => String -> Formatter (n + 1)

def formatter (format : List String) : Formatter format.length :=
  match format with
  | [] => ""
  | [s] => s
  | s :: s' :: format =>
    fun h => formatter  ((s ++ h ++ s') :: format)
termination_by format.length

def format (formatString : String) : Σ n, Formatter n :=
  let parts := formatString.splitOn "·"
  ⟨parts.length, formatter parts⟩

#eval (format "I can't · my ·!").2 "feel" "legs"
-- Function expected at
--   (format "I can't · my ·!").snd
-- but this term has type
--   Formatter (format "I can't · my ·!").fst

#eval
  let ⟨_, f⟩ := format "I can't · my ·!"
  f "feel" "legs"

end v2

namespace v3

def Format := List String /- The holes are between the strings -/

def Formatter (n : Nat) : Type :=
  match n with
  | 0 => String
  | 1 => String
  | n + 2 => String -> Formatter (n + 1)

def formatter (format : List String) : Formatter format.length :=
  match format with
  | [] => ""
  | [s] => s
  | s :: s' :: format =>
    fun h => formatter  ((s ++ h ++ s') :: format)
termination_by format.length

def Char.splitOnDot (chars : List Char) : List (List Char) :=
  let rec split (chars acc : List Char) : List (List Char) :=
    match chars  with
    | []           => [acc]
    | '·' :: chars => acc :: (split chars [])
    | c :: chars   => split chars (acc ++ [c])
  split chars []

def _root_.String.splitOnDot (string : String) : List String :=
  string |>.toList |> Char.splitOnDot |>.map String.mk

#eval "Hello ·! ·".splitOnDot
-- ["Hello ", "! ", ""]

def format (formatString : String) :=
  formatter (formatString.splitOnDot)

#eval format "Hello ·! ·" "world" "👋"
-- "Hello world! 👋"

end v3
