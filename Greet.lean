
-- `none` or `some name` where name is a String.
def name? : Option String := none 

def greet : IO Unit := do
  match name? with
  | some name => IO.println s!"Hello {name}!"
  | none => IO.println s!"Hello Odysseus"

#eval greet

def name : String :=
  match name? with
  | some name => name
  | none => "Odysseus"

#eval name

-- Functional pure core, imperative shell
def greet' : IO Unit := do
  IO.println s!"Hello {name}!"

def nameAndGreet : IO String := do
  IO.println s!"Hello {name}"
  return name 

#eval nameAndGreet 

