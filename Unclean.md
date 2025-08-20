
Cheatsheet for Lean imperative, impure & unsafe code
================================================================================

Use Python
--------------------------------------------------------------------------------

To get access to functionalities not available in Lean, call Python:
start a [toupie] server, `import Python` in Lean then use

  - `Python.exec!` to execute Python code

    ⚠️ The code is executed *server-side*. 
    Do not expect a `Python.exec! "print('Hello world!')"`
    to provide a message in your Lean session.

  - `Python. eval!` to evaluate Python expressions. 

    ⚠️ The returned value is always a Lean `String` (even if the Python
    value is not). 

    
## Examples

```lean
import Python

def main : IO Unit := do
  let message : String <- Python.eval! "'Hello world!'"
  IO.println message

#eval main
-- Hello world!
```

```lean
import Python

def main : IO Unit := do
  let sum : String <- Python.eval! "1+1"
  IO.println s!"1 + 1 = {sum}"

#eval main
-- 1 + 1 = 2
```


**TODO**: example with conversion from str to what you want (ex : Nat)
```lean
import Python

def main : IO Unit := do
    Python.exec! "import math"
    let pi_str <- Python.eval! "sum_integers_up_to(10)"
    let pi := pi_str.
    IO.println s!"1 + 2 + ... + 10 = {sum}"

#eval main
-- 1 + 2 + ... + 10 = 55
```


```lean
import Python

def pythonDef := "
def sum_integers_up_to(n):
    return n * (n + 1) // 2
"

def main : IO Unit := do
    Python.exec! pythonDef
    let sum : String <- Python.eval! "sum_integers_up_to(10)"
    IO.println s!"1 + 2 + ... + 10 = {sum}"

#eval main
-- 1 + 2 + ... + 10 = 55
```