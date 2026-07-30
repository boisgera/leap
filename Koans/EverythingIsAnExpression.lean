
/-!
TODO:
  - typed expression to be exact, but delay
  - compare with Python
  - compare with ts
  - simple, then inc complicated patterns taht are expression
  - let are for convenience, change nothing
  - concept of reduction (link to purity) of expressions
  -> Computation is reduction of expression (mostly)

-/


/-!

```python
def greet(name=None):
    # `if-then-else` statement
    if name != None:
        print(f"Hello {name}!")
    else:
        print("Hello Nobody!")

greet("Odysseus")
# Hello Odysseus!

greet()
# Hello Nobody!
```

```python
def greet(name=None):
    # `if-then-else` conditional expression
    name = name if name != None else "Nobody"
    print(f"Hello {name}!)
```
-/

/-!
```ts
function greet(name = undefined)
  if name? then
    console.log `Hello ${name}!`
  else
    console.log "Hello Noman!"

greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Noman!

```

```ts
function greet(name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`


greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Noman!

```

```ts
function greet(name = undefined)
  name =
    if name? then
      name
    else
      "Noman"
  console.log `Hello ${name}!`

greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Noman!

```

```ts
function greet(name = undefined)
  let result = if name? then
    console.log `Hello ${name}!`
  else
    console.log "Hello Noman!"
  console.debug value

greet("Odysseus")
// Hello Odysseus!
// undefined

greet()
// Hello Noman!
// undefined

```

```ts
function greet(name = undefined)
  name = if name? then
    console.debug "✅"
    name
  else
    console.debug "❌"
    "Noman"
  console.log `Hello ${name}!`

greet("Odysseus")
// ✅
// Hello Odysseus!

greet()
// ❌
// Hello Noman!
```

Now the declaration of the `greet` function in Civet is itself an expression.
The code

```ts
function greet(name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`
```

is actually a shortcut for:

```ts
let greet = function greet(name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`
```

On the right-hand side of `=` we define the function and give it the name
`greet`. On the left-hand side we declare a variable named `greet` that refers
to this function.

This decomposition is actually conceptually much cleaner. In particular, we
can decouple the name of the function and the name of the variable:

```ts
g := function greet(name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`

console.log g.name
// greet

g("Odysseus")
// ✅
// Hello Odysseus!

g()
// ❌
// Hello Noman!
```

Now you totally can avoid naming the function explicitly and assign an
anonymous function to a variable:

```ts
let greet = function (name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`

greet("Odysseus")
// ✅
// Hello Odysseus!

greet()
// ❌
// Hello Noman!
```

(In this particular use case Civet will actually infer the name of the function
from the name of the variable it is assigned to, thus `greet.name` is `'greet'`
and your function is not truly anonymous. But if you don't assign your function
at once, its `name` field is `undefined`.)

Of course, you don't have to name a function if you plan to use it immediately
and once only
(this pattern is called IIFE, for *Immediately Invoked Function Expression*).

```ts
(function (name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`
) "Odysseus"
// Hello Odysseus!
```

The declaration of a function in Python is not an expression.
Python has actually some support for anonymous function (called *lambdas*),
but there expressivety is limited with respect to the classic functions.

-/

/-!
Note: `let a = ...` are statements in Civet, not expressions.
-/



/-!
Even pseudo-imperative code (sequencing of actions/functions that may have
side-effects) can be desugared into an expression. Here the key is the
*monadic bind* operator `>>=`.
-/

/-! `App.lean`:-/
def main : IO Unit := do
  IO.print "Enter your name: "
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trimAscii}"

/-!
Test with `lean --run App.lean
-/

/-!
Equivalent lean code:
-/

def mainDesugared: IO Unit :=
  IO.print "Enter your name: "
    >>= fun _ => IO.getStdin
    >>= fun stdin => (stdin.getLine)
    >>= fun name => IO.println s!"Hello, {name.trimAscii}"

def mainDesugaredVerbose : IO Unit :=
  let prompt : IO Unit :=
    IO.print "Enter your name: "
  let getStdin : IO IO.FS.Stream :=
    IO.getStdin
  let getName (stdin : IO.FS.Stream) : IO String :=
    stdin.getLine
  let greet (name : String): IO Unit :=
    IO.println s!"Hello, {name.trimAscii}"
  prompt
    -- we don't actually use the (non-informative) out of prompt
    >>= fun (_ : Unit) => getStdin
    >>= getName
    >>= greet

def mainDesugaredWithSeqRight : IO Unit :=
  IO.print "Enter your name: "
    *>  IO.getStdin
    >>= fun stdin => (stdin.getLine)
    >>= fun name => IO.println s!"Hello, {name.trimAscii}"
