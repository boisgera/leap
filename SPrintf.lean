
/-
Do a function that (type-)*safely* associate to a format string a concatenation
function?

E.g.
  - "Hello!" -> "Hello!"
  - "Hello ·!" -> ("Hello " ++ ·)
  - "(·, ·)" -> ("(" ++ · ++ ", " ++ · ")")

TODO: escape

-/

def Format := List String /- The holes are between the strings -/

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

def FormatterType (format : Format) : Type :=
  match format with
  | [] => String
  | [_] => String
  | _ :: format => String -> FormatterType format

def formatter (format : List String) : FormatterType format :=
  match format with
  | [] => ""
  | [s] => s
  | s :: format =>
    (fun s' => s ++ _)

/- Need to "push-right" the  s ++. Is that a foldr scheme ?
Display the tree transformation !-/
