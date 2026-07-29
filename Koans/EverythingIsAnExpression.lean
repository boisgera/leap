
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
  result := if name? then
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
