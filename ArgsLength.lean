import Mathlib

def main (args : List String) : IO Unit := do
  if 0 < args.length then
    let name := args[0]!
    IO.println s!"Hello {name}!"
  else
    IO.println s!"Hello world!"

def main' (args : List String) : IO Unit := do
  if 0 < args.length then
    match args[0]? with
    | some name => IO.println s!"Hello {name}!"
    | none => unreachable!
  else
    IO.println s!"Hello world!"

def main'' (args : List String) : IO Unit := do
  match args with
  | [] => IO.println s!"Hello world!"
  | name :: _ => IO.println s!"Hello {name}!"

def main₄ (args : List String) : IO Unit := do
  if h : (0 < args.length) then
    let name := args[0]'h
    IO.println s!"Hello {name}!"
  else
    IO.println s!"Hello world!"

def main₅ (args : List String) : IO Unit := do
  if h : (1 < args.length) then
    have h' : 0 < args.length :=
      lt_trans zero_lt_one h
    let name := args[0]'h'
    IO.println s!"Hello {name}!"
  else
    IO.println s!"Hello world!"

def main₆ (args : List String) : IO Unit := do
  if h : (1 < args.length) then
    have h' : 0 < args.length := by
      apply lt_trans (b := 1)
      . exact zero_lt_one
      . exact h
    let name := args[0]'h'
    IO.println s!"Hello {name}!"
  else
    IO.println s!"Hello world!"

theorem wt : ∀ {m n p : ℕ},  m <= n -> n < p -> m < p := by
  apply lt_of_le_of_lt

def main₇ (args : List String) : IO Unit := do
  if h : (1 < args.length) then
    have h' := wt (by norm_num : 0 <= 1) h
    let name := args[0]'h'
    IO.println s!"Hello {name}!"
  else
    IO.println s!"Hello world!"
