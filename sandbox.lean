import Python

def main : IO Unit := do
  let message : String <- Python.eval! "'Hello world!'"
  IO.println message

#eval main
-- Hello world!
