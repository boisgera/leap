
def f : StateM Nat String := do
  set 42
  let x ← get
  if x > 0 then
    return "Hello, world!"
  else
    return "Goodbye, world!"

#eval f.run 0
