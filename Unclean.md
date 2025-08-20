
Cheatsheet for Lean imperative, impure & unsafe code
================================================================================

Use Python
--------------------------------------------------------------------------------

To get access to functionalities not available in Lean, call Python:
start a [toupie] server, import `Python` in Lean then use

  - `Python.exec!` to execute Python code
    ⚠️ The code is executed *server-side*.

  - `Python. eval!` to evaluate Python expressions. 
    ⚠️ The returned value is always a Lean `String`.
    
## Examples

```lean
import Python

def main : IO Unit :=
  -- Print a message in the toupie terminal
  Python.exec! "print('🐍 Hello world from Python!')"
```

```lean
import Python

def main : IO Unit := 
  let sum : String := Python.eval! "1+1"
  IO.println s!"1+1 = {sum}"
```

```lean
import Python

def pythonDef := "
def sum_integers_up_to(n):
    return n * (n + 1) // 2
"

def main : IO Unit:
    Python.exec! pythonDef
    let sum : String := Python.eval! "sum_integers_up_to(10)"
    IO.println s!"1 + 2 +... + 10 = {sum}"