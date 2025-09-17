inductive Expr : Type -> Type where
  | bool : Bool -> Expr Bool
  | nat : Nat -> Expr Nat
  | not : Expr Bool -> Expr Bool
  | and : Expr Bool -> Expr Bool -> Expr Bool
  | add : Expr Nat -> Expr Nat -> Expr Nat
  | eq : Expr Nat -> Expr Nat -> Expr Bool
  | ite : Expr Bool -> Expr Nat -> Expr Nat -> Expr Nat
deriving Repr

def Expr.toString {α} (expr : Expr α) : String :=
  match expr with
    | bool b => ToString.toString b
    | nat n => ToString.toString n
    | not e => s!"(not {e.toString})"
    | and e f => s!"({e.toString} and {f.toString})"
    | add m n => s!"({m.toString} + {n.toString})"
    | eq m n => s!"({m.toString} == {n.toString})"
    | ite b e f => s!"(if {b.toString} then {e.toString} else {f.toString})"

#eval Expr.not (Expr.and (Expr.bool false) (Expr.bool true)) |>.toString
-- "(not (false and true))"

#eval Expr.ite (Expr.eq (Expr.add (Expr.nat 1) (Expr.nat 1)) (Expr.nat 2)) (Expr.nat 1) (Expr.nat 0) |>.toString
-- "(if ((1 + 1) == 2) then 1 else 0)"

def Expr.eval {α} (expr : Expr α) : α :=
  match expr with
    | bool b => b
    | nat n => n
    | not e => Bool.not e.eval
    | and e f => Bool.and e.eval f.eval
    | add m n => Nat.add m.eval n.eval
    | eq m n => m.eval == n.eval
    | ite b e f => if b.eval then e.eval else f.eval

#eval Expr.not (Expr.and (Expr.bool false) (Expr.bool true)) |>.eval
-- true

#eval Expr.ite (Expr.eq (Expr.add (Expr.nat 1) (Expr.nat 1)) (Expr.nat 2)) (Expr.nat 1) (Expr.nat 0) |>.eval
-- 1

abbrev Parser := StateT String Option

-- TODO
--   - space
--   - literal
--   - seq (? nor sure)

namespace Parser


def space : Parser Unit :=
  modify (·.trimLeft)

#eval space ""
-- some ((), "")

#eval space "    "
-- some ((), "")

#eval space "     AAA"
-- some ((), "AAA")

def literal (literal : String) : Parser String := do
  let input <- get
  guard (input.startsWith literal)
  set (input.drop literal.length)
  return literal

#eval literal "(" "("
-- some ((), "(")

#eval literal "AAA" "AAABBB"
-- some ("AAA", "BBB")

#eval literal "ZZZ" "KKKZZZ"
-- none

partial def zeroOrMore {α} (p : Parser α) : Parser (List α) := do
  (do let a <- p; return a :: (<- zeroOrMore p))
  <|>
  return []

def false : Parser (Expr Bool) := do
  space
  _ <- literal "false"
  return Expr.bool Bool.false

def true : Parser (Expr Bool) := do
  space
  _ <- literal "true"
  return Expr.bool Bool.true

def bool : Parser (Expr Bool) := do
  false <|> true

#eval bool "false"
-- some (Expr.bool false, "")

#eval bool "true"
-- some (Expr.bool true, "")

#eval bool "0"
-- none

def digit : Parser Nat := do
  let digitStr <- literal "0"
    <|> literal "1"
    <|> literal "2"
    <|> literal "3"
    <|> literal "4"
    <|> literal "5"
    <|> literal "6"
    <|> literal "7"
    <|> literal "8"
    <|> literal "9"
  let char := digitStr.get! 0
  let digit := char.toNat - '0'.toNat
  return digit

#eval digit "123"
-- some (1, "23")



def nat : Parser (Expr Nat) := do
  let firstDigit <- digit
  let digits <- (zeroOrMore digit)
  let number := digits.foldl (· * 10 + ·) firstDigit
  return Expr.nat number

#eval nat "123"
-- some (Expr.nat 123, "")


mutual

partial def not : Parser (Expr Bool) := do
  _ <- literal "("
  space
  _ <- literal "not"
  space
  let expr <- boolExpr
  space
  _ <- literal ")"
  return Expr.not expr


partial def and : Parser (Expr Bool) := do
  _ <- literal "("
  space
  let expr1 <- boolExpr
  space
  _ <- literal "and"
  space
  let expr2 <- boolExpr
  space
  _ <- literal ")"
  return Expr.and expr1 expr2

partial def add : Parser (Expr Nat) := do
  _ <- literal "("
  space
  let expr1 <- natExpr
  space
  _ <- literal "+"
  space
  let expr2 <- natExpr
  space
  _ <- literal ")"
  return Expr.add expr1 expr2


partial def eq : Parser (Expr Bool) := do
  _ <- literal "("
  space
  let expr1 <- natExpr
  space
  _ <- literal "=="
  space
  let expr2 <- natExpr
  space
  _ <- literal ")"
  return Expr.eq expr1 expr2


partial def ite : Parser (Expr Nat) := do
  _ <- literal "("
  space
  _ <- literal "if"
  space
  let cond <- boolExpr
  space
  _ <- literal "then"
  space
  let expr1 <- natExpr
  space
  _ <- literal "else"
  space
  let expr2 <- natExpr
  space
  _ <- literal ")"
  return Expr.ite cond expr1 expr2


partial def boolExpr := bool <|> not <|> and <|> eq
partial def natExpr := nat <|> add <|> ite

end

#eval not "(not true)"
-- some (Expr.not (Expr.bool true), "")

#eval and "(true and true)"
-- some (Expr.and (Expr.bool true) (Expr.bool true), "")

#eval add "(1 + 2)"
-- some (Expr.add (Expr.nat 1) (Expr.nat 2), "")

#eval eq "(1 == 2)"
-- some (Expr.eq (Expr.nat 1) (Expr.nat 2), "")

#eval ite "(if true then 1 else 0)"
-- some (Expr.ite (Expr.bool true) (Expr.nat 1) (Expr.nat 0), "")


#eval boolExpr "(not (false and true))"
-- some (Expr.not (Expr.and (Expr.bool false) (Expr.bool true)), "")

#eval natExpr "(if ((1 + 1) == 2) then 1 else 0)"
-- some (Expr.ite (Expr.eq (Expr.add (Expr.nat 1) (Expr.nat 1)) (Expr.nat 2)) (Expr.nat 1) (Expr.nat 0), "")

end Parser
