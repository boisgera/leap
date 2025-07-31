import Init.System.IO

namespace Python

def eval (code : String) : IO String := do
    IO.FS.writeFile "input" code
    IO.FS.readFile "output"

def exec (code : String) : IO Unit := do
    let data <- eval code
    if data != "None" then
        panic! s!"Expected 'None' but got: {data}"

end Python
