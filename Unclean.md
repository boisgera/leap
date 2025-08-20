
Cheatsheet for Lean imperative, impure & unsafe code
================================================================================

TODO:

  - impure functions ...

  - Imperative style, do, let mut, <-, := etc. loops, etc (control flow)

  - errors: use ! variants, panic, use POSIX-like errors?





Use ! variants

🐍 Use Python from Lean
--------------------------------------------------------------------------------

Lean has a very limited standard library. 
In this respect, that's the complete opposite of Python, which comes
"batteries included"! 

So when you need a functionality that Lean lacks, call Python:

To get access to functionalities not available in Lean, call Python:

  - start a [toupie] server, 
  
  - `import Python` in your lean code, then

  - use `Python.exec!` to execute Python code

  - use `Python. eval!` to evaluate Python expressions. 

### ⚠️ Warnings

  - The code is executed *server-side*;
    `Python.exec! "print('Hello world!')"`
    *will not* display a message in your Lean session.

  - The returned value is always a Lean `String` 
    (even if the Python value is not). 

    
### 🔍 Examples

```lean
import Python

def main : IO Unit := do
  let message <- Python.eval! "'Hello world!'"
  IO.println message

#eval main
-- Hello world!
```

```lean
import Python

def main : IO Unit := do
  let sum : String <- Python.eval! "1 + 1"
  IO.println s!"1 + 1 = {sum}"

#eval main
-- 1 + 1 = 2
```

You can use `Python.exec!` to define Python constants and/or functions before
calling `Python.eval!`:

```lean
import Python

def pythonCode := "
def sum_integers_up_to(n):
    return n * (n + 1) // 2
"

def main : IO Unit := do
    Python.exec! pythonCode
    let sum : String <- Python.eval! "sum_integers_up_to(10)"
    IO.println s!"1 + 2 + ... + 10 = {sum}"

#eval main
-- 1 + 2 + ... + 10 = 55
```

Convert strings that represent Python objects to native Lean types when needed:

```lean
import Python

def fact (n : Nat) : IO Nat := do
  Python.exec! "import math"
  let factString <- Python.eval! s!"math.factorial({n})"
  return factString.toNat!

def binomial (n k : Nat) : IO Nat := do
  let fact_n <- fact n
  let fact_k <- fact k
  let fact_n_k <- fact (n - k)
  return fact_n / fact_k / fact_n_k

#eval binomial 6 3
-- 20
```

Spin a toupie server with extra Python libraries when you need them;
the `requests` library is required for the next example:

```bash
uvx --with requests --from git+https://github.com/boisgera/toupie toupie
```

Note that Lean 4 [raw string literals] 
– especially the hash mark variant – 
are very handy to define Python code without worrying 
about escaping backslashes and quotes.

[raw string literals]: https://lean-lang.org/doc/reference/latest//Basic-Types/Strings/#raw-string-literals


```lean
import Python

def pythonCode := r#"
import requests

URL = "https://api.chucknorris.io/jokes/random"

def get_joke():
  joke_info = requests.get(URL).json()
  return joke_info["value"]
"#

def randomJoke : IO String := do
  Python.exec! pythonCode
  let joke <- Python.eval! "get_joke()"
  return joke

#eval do
  let joke <- randomJoke
  IO.println joke
-- "Everybody Hates Chris" was originally called "Chuck Norris Hates Chris" but 
-- Chris Rock didn't want to make a series just about how he survive Chuck 
-- Norris round house kicking him EVERYDAY
```



[toupie]: https://github.com/boisgera/toupie