open Std (Format)

inductive TrafficLight where
  | green
  | orange
  | red

open TrafficLight

#eval [green, orange, red]
-- could not synthesize a `Repr` or `ToString` instance for type
--   List TrafficLight

def TrafficLight.toString (tl : TrafficLight) : String :=
  match tl with
  | green => "🟢"
  | orange => "🟠"
  | red => "🔴"

instance : ToString TrafficLight where
  toString := TrafficLight.toString

/-!
That triggers the definition of an instance of `List TrafficLight`.
The corresponding `Repr` instance is not available (yet), thus
`#eval` will use `toString` (which calls `toString` on the items).
-/

#eval [green, orange, red]
-- [🟢, 🟠, 🔴]

def TrafficLight.repr (tl : TrafficLight) : Format :=
  match tl with
  | green => Format.text "green"
  | orange => Format.text "orange"
  | red => Format.text "red"

instance : Repr TrafficLight where
  reprPrec (tl : TrafficLight) (_prec : Nat) := tl.repr

#eval [green, orange, red]
-- [green, orange, red]

inductive Point where
  | mk (x y : Float)

#eval Point.mk 1 2
-- Point.mk 1.000000 2.000000

#eval some (Point.mk 1 2)
-- Unable to synthesize `MonadEval` instance to adapt
--   Option Point
-- to `IO` or `Lean.Elab.Command.CommandElabM`.

def Point.reprPrec_v1 (p : Point) (_prec : Nat): Format :=
  match p with
  | Point.mk x y => Format.text s!"Point.mk {x} {y}"

instance : Repr Point where
  reprPrec := Point.reprPrec_v1

#eval Point.mk 1 2
-- Point.mk 1.000000 2.000000

#eval some (Point.mk 1 2)
-- some Point.mk 1.000000 2.000000

def Point.reprPrec_v2 (p : Point) (prec : Nat): Format :=
  match p with
  | Point.mk x y =>
    let s := s!"Point.mk {x} {y}"
    if prec < max_prec then
      Format.text s
    else
      Format.text s!"({s})"

instance : Repr Point where
  reprPrec := Point.reprPrec_v2

#eval Point.mk 1 2
-- Point.mk 1.000000 2.000000

#eval some (Point.mk 1 2)
-- some (Point.mk 1.000000 2.000000)

inductive Expr where
  | num : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr

def Expr.reprPrec_v1 (e : Expr) (prec : Nat) : Format :=
  match e with
  | num n =>
    let s : String := s!"num {toString n}"
    if prec < max_prec then
      Format.text s
    else
      Format.text s!"({s})"
  | add e1 e2 =>
    let s : String := s!"add {reprPrec_v1 e1 max_prec} {reprPrec_v1 e2 max_prec}"
    if prec < max_prec then
      Format.text s
    else
      Format.text s!"({s})"
  | mul e1 e2 =>
    let s : String := s!"mul {reprPrec_v1 e1 max_prec} {reprPrec_v1 e2 max_prec}"
    if prec < max_prec then
      Format.text s
    else
      Format.text s!"({s})"

instance : Repr Expr where
  reprPrec := Expr.reprPrec_v1

open Expr (num add mul)

def expr := add (mul (num 1) (num 2)) (num 3)

#eval expr
-- add (mul (num 1) (num 2)) (num 3)

#eval (repr expr).pretty 80
-- "add (mul (num 1) (num 2)) (num 3)"

#eval (repr expr).pretty 20
-- "add (mul (num 1) (num 2)) (num 3)"

#print Format
-- inductive Std.Format : Type
-- number of parameters: 0
-- constructors:
-- Std.Format.nil : Format
-- Std.Format.line : Format
-- Std.Format.align : Bool → Format
-- Std.Format.text : String → Format
-- Std.Format.nest : Int → Format → Format
-- Std.Format.append : Format → Format → Format
-- Std.Format.group : Format → optParam Format.FlattenBehavior Format.FlattenBehavior.allOrNone → Format
-- Std.Format.tag : Nat → Format → Format

def Expr.reprPrec_v2 (e : Expr) (prec : Nat) : Format :=
  match e with
  | num n =>
    let f : Format :=
      Format.group (
        s!"num" ++
        Format.nest 2 (
          Format.line ++ s!"{n}"
        )
      )
    if prec < max_prec then
      f
    else
      "(" ++ f ++ ")"
  | add e1 e2 =>
    let f : Format :=
      Format.group (
        Format.text "add" ++
        Format.nest 2 (
          Format.line ++
          Expr.reprPrec_v2 e1 max_prec ++
          Format.line ++
          Expr.reprPrec_v2 e2 max_prec
        )
      )
    if prec < max_prec then
      f
    else
      "(" ++ f ++ ")"
  | mul e1 e2 =>
    let f : Format :=
      Format.group (
        Format.text "mul" ++
        Format.nest 2 (
          Format.line ++
          Expr.reprPrec_v2 e1 max_prec ++
          Format.line ++
          Expr.reprPrec_v2 e2 max_prec
        )
      )
    if prec < max_prec then
      f
    else
       "(" ++ f ++ ")"


instance : Repr Expr where
  reprPrec := Expr.reprPrec_v2

#eval expr
-- add (mul (num 1) (num 2)) (num 3)

#eval (repr expr).pretty 80 |> IO.println
-- add (mul (num 1) (num 2)) (num 3)

#eval (repr expr).pretty 20 |> IO.println
-- add
--   (mul
--     (num 1)
--     (num 2))
--   (num 3)

#eval (repr expr).pretty 5 |> IO.println
-- add
--   (mul
--     (num
--       1)
--     (num
--       2))
--   (num
--     3)
