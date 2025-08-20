UncLean
================================================================================

🗑️ Embrace impurity
--------------------------------------------------------------------------------

In most programming languages, functions can take inputs, process them, and
return ouputs. But they can also have various kind of side-effects: 
print messages in you terminal, send e-mails, search the Internet ... 
even order lunch!

![The Enunciation Apocalypse]

[The Enunciation Apocalypse]: https://scontent-cdg4-3.xx.fbcdn.net/v/t39.30808-6/532953901_24490135003936932_7732910830382145601_n.jpg?_nc_cat=110&ccb=1-7&_nc_sid=aa7b47&_nc_ohc=qjzUJrpukJYQ7kNvwFyHj2L&_nc_oc=AdluCJNAJctXdZR9pSI6o8UviHpup3a8cBaudmzpIp5UrLly8vwdyhOj37x-lpcAuAI&_nc_zt=23&_nc_ht=scontent-cdg4-3.xx&_nc_gid=_6IzYZREoGtgmSuKScPszA&oh=00_AfWoe-jWnl7kXSuU5NDTSQjnETbPMptTujsfGxe1OWvhOw&oe=68ABE55A

These functions with potential side-effects are called impure in Lean 
and are carefully tracked by its type system; 





Use an Imperative Style
--------------------------------------------------------------------------------

  - Imperative style, do, let mut, <-, := etc. loops, etc (control flow)

Live dangerously
--------------------------------------------------------------------------------



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