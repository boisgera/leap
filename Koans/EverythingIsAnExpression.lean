
/-!
Alternative koan name: Expression over Statement
-/

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
Didactic idea: since Python and Lean are very different and there are a lot
of bagage associated to Lean, make a first comparison between Python and
Civet first, which has only static type system and the purity constraints.
-/

/-!

## Python: if-then-else

The following Python function greets a person using its name if it is given,
or greets "Nobody" otherwise:

```python
def greet(maybe_name=None):
    # `if-then-else` statement
    if maybe_name is not None:
        name = maybe_name
        print(f"Hello {name}!")
    else:
        print("Hello Nobody!")

greet("Odysseus")
# Hello Odysseus!

greet()
# Hello Nobody!
```

The repetition in the code could be considered a code smell. Instead we could
implement `greet` by:

```python
def greet(maybe_name=None):
    # `if-then-else` statement again
    if maybe_name is not None:
        name = maybe_name
    else:
        name = "Nobody"
    print(f"Hello {name}!")
```

That works but at this stage the only thing that both clauses of the
if-then-else statement are doing is assigning a value to the variable
`name`. And for this, there is the `if-then-else` expression,
which does not execute statements but computes a value instead.

```python
def greet(maybe_name=None):
    # `if-then-else` expression
    name = maybe_name if maybe_name is not None else "Nobody"
    print(f"Hello {name}!")
```
-/

/-
## Python: function declaration

The function declaration is itself a statement. It does not return a function
that I can for example bind to a variable myself. Instead it has a side-effect:
it creates a variable named `greet` and assign the function to it.

```python
def greet(maybe_name=None):
    # `if-then-else` expression
    name = maybe_name if maybe_name is not None else "Nobody"
    print(f"Hello {name}!")

print(greet)
<function greet at 0x79ed03b837e0>
```

There is a way to have function definition expression instead, with the
keyword `lambda`, for example:

```python
greet = lambda maybe_name=None : print(f'Hello {maybe_name if maybe_name is not None else "Nobody"}!')
```

This construct is, at least apparently, severely constrained: its body is made
of a single expression, which is implicitly returned, so we add the get rid
of the temporary variable `name`. There is no indentation either, so we add to
put everything on one line.

We can "fix" these issues with some tricks since we too clever for our own good,
but it's difficult to argue that this solution is great.

```python
greet = lambda maybe_name: print(
    (
        name := maybe_name if maybe_name is not None else "Nobody",
        f"Hello {name}"
    )[1]
)
```

Don't spend too much time understanding what this code snippet does...

-/


/-!
## Python: for loops

**TODO** for loop statements and list comprehensions.

-/


/-!

Civet:

```ts
function greet(name = undefined)
  if name? then
    console.log `Hello ${name}!`
  else
    console.log "Hello Nobody"

greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Nobody

```

```ts
function greet(name = undefined)
  name = if name? then name else "Noman"
  console.log `Hello ${name}!`


greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Nobody

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
// Hello Nobody

```

```ts
function greet(name = undefined)
  let result = if name? then
    console.log `Hello ${name}!`
  else
    console.log "Hello Nobody"
  console.debug value

greet("Odysseus")
// Hello Odysseus!
// undefined

greet()
// Hello Nobody
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
// Hello Nobody
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
// Hello Nobody
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
// Hello Nobody
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
Mention relationship between Civet and Typescript.
Mention Hy, a LISP language for the Python platform that has the same
kind of relationship and interoperate seamlessly with Python libraries.
-/

/-!
In Lean:

-/

def v0.greet (name? : Option String := none) : IO Unit := do
    match name? with
    | some name => IO.println s!"Hello {name}!"
    | none => IO.println "Hello Nobody!"

#eval v0.greet "Odysseus"
-- Hello Odysseus

#eval v0.greet
-- Hello Nobody

def v1.greet (name? : Option String := none) : IO Unit := do
    let name := match name? with
      | some name => name
      | none => "Nobody"
    IO.println s!"Hello {name}!"

#eval v1.greet "Odysseus"
-- Hello Odysseus

#eval v1.greet
-- Hello Nobody

def v2.greet (name? : Option String := none) : IO Unit :=
    pure (match name? with
      | some name => name
      | none => "Nobody"
    )
    >>= fun (x : String) => pure s!"Hello {x}!"
    >>= IO.println

#eval v2.greet "Odysseus"
-- Hello Odysseus!

#eval v2.greet
-- Hello Nobody!


/-!
--------------------------------------------------------------------------------
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
