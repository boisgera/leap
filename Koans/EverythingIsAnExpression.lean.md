
Alternative koan name: Expression over Statement

TODO:
  - typed expression to be exact, but delay
  - compare with Python
  - compare with ts
  - simple, then inc complicated patterns taht are expression
  - let are for convenience, change nothing
  - concept of reduction (link to purity) of expressions
  -> Computation is reduction of expression (mostly)


Didactic idea: since Python and Lean are very different and there are a lot
of bagage associated to Lean, make a first comparison between Python and
Civet first, which has only static type system and the purity constraints.


## Python: if-then-else

The following Python function greets a person using its name if it is given,
or greets "Nobody" otherwise:

```python
def greet(optional_name=None):
    # `if-then-else` statement
    if optional_name is not None:
        name = optional_name
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
def greet(optional_name=None):
    # `if-then-else` statement again
    if optional_name is not None:
        name = optional_name
    else:
        name = "Nobody"
    print(f"Hello {name}!")
```

That works but at this stage the only thing that both clauses of the
if-then-else statement are doing is assigning a value to the variable
`name`. And for this, there is the `if-then-else` expression,
which does not execute statements but computes a value instead.

```python
def greet(optional_name=None):
    # `if-then-else` expression
    name = optional_name if optional_name is not None else "Nobody"
    print(f"Hello {name}!")
```

```lean4
/-
## Python: function declaration

The function declaration is itself a statement. It does not return a function
that I can for example bind to a variable myself. Instead it has a side-effect:
it creates a variable named `greet` and assign the function to it.

```python
def greet(optional_name=None):
    # `if-then-else` expression
    name = optional_name if optional_name is not None else "Nobody"
    print(f"Hello {name}!")

print(greet)
<function greet at 0x79ed03b837e0>
```

There is a way to have function definition expression instead, with the
keyword `lambda`, for example:

```python
greet = lambda optional_name=None : print(f'Hello {optional_name if optional_name is not None else "Nobody"}!')
```

This construct is, at least apparently, severely constrained: its body is made
of a single expression, which is implicitly returned, so we add the get rid
of the temporary variable `name`. There is no indentation either, so we add to
put everything on one line.

We can "fix" these issues with some tricks, but our final solution is not
that great:

```python
greet = lambda optional_name: print(
    (
        name := optional_name if optional_name is not None else "Nobody",
        f"Hello {name}"
    )[1]
)
```

The moral of the story is that "function definition as an expression" is
only meant for really simple cases in Python (single, short expression)
and is not ergonomic beyond that, despite the potential.

-/
```

## Python: for loops


Let's use greet several persons using a for loop statement:

```python

names = ["Penelope", "Telemachus", "Odysseus"]

def greeting(optional_name=None):
    name = optional_name if optional_name is not None else "Nobody"
    return f"Hello {name}!"

def greet(optional_name=None):
    print(greeting(optional_name))

for name in names:
  greet(name)
# Hello Penelope!
# Hello Telemachus!
# Hello Odysseus!
```

Alternatively, we can also collect the greeting messages and use them afterwards:

```python

greetings = []

for name in names:
  message = greeting(name)
  greetings.append(message)

print(greetings)
# ['Hello Penelope!', 'Hello Telemachus!', 'Hello Odysseus!']

for message in greetings:
  print(message)
# Hello Penelope!
# Hello Telemachus!
# Hello Odysseus!
```

If you want to do that, the first for loop statement is probably not the best
construct. Instead, you can use a list comprehension, which is an expression.

```python
greetings = [greeting(name) for name in names]

print(greetings)
# ['Hello Penelope!', 'Hello Telemachus!', 'Hello Odysseus!']

for message in greetings:
  print(message)
# Hello Penelope!
# Hello Telemachus!
# Hello Odysseus!


```lean4
## Civet: if-then-else

Let's write the Civet equivalent of our two first versions of `greet` in Python.

```ts
function greet(optional_name = undefined)
  if optional_name then
    console.log `Hello ${optional_name}!`
  else
    console.log "Hello Nobody"

greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Nobody

```

```ts
function greet(name = undefined)
  name = if optional_name then optional_name else "Nobody"
  console.log `Hello ${name}!`


greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Nobody

```

We could think at this stage that Civet also has a if-then-else statement and
an if-then-else expression, but this is actually the same construct. For
example, we could write the second version as:


```ts
function greet(name = undefined)
  name =
    if optional_name then
      optional_name
    else
      "Nobody"
  console.log `Hello ${name}!`

greet("Odysseus")
// Hello Odysseus!

greet()
// Hello Nobody

```

and the first version also produces a value, which can be collected!
Here it's `undefined` since what matters in this version is the s
display of the message and not the computation of a value.

```ts
function greet(name = undefined)
  let result = if optional_name then
    console.log `Hello ${optional_name}!`
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

Of course we are free not to collect this value and then the if-then-else
expression looks exactly like a statement.

We can also mix and match in each clause (pseudo-)statements, used for their
side-effects, whose value will be ignored and the last expression in the
clause will be the returned value.

```ts
function greet(optional_name = undefined)
  name = if optional_name then
    console.debug "✅"
    optional_name
  else
    console.debug "❌"
    "Nobody"
  console.log `Hello ${name}!`

greet("Odysseus")
// ✅
// Hello Odysseus!

greet()
// ❌
// Hello Nobody
```

## Civet: function declaration

Now the declaration of the `greet` function in Civet is itself an expression.
The code

```ts
function greet(optional_name = undefined)
  name = if optional_name then optional_name else "Nobody"
  console.log `Hello ${name}!`
```

is actually a shortcut for:

```ts
let greet = function greet(optional_name = undefined)
  name = if optional_name then optional_name else "Nobody"
  console.log `Hello ${name}!`
```

On the right-hand side of `=` we define the function and give it the name
`greet`. On the left-hand side we declare a variable named `greet` that refers
to this function.

This decomposition is actually conceptually much cleaner. In particular, we
can decouple the name of the function and the name of the variable:

```ts
g := function greet(optional_name = undefined)
  name = if optional_name then optional_name else "Nobody"
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
let greet = function (optional_name = undefined)
  name = if optional_name then optional_name else "Nobody"
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
  name = if optional_name then optional_name else "Nobody"
  console.log `Hello ${name}!`
) "Odysseus"
// Hello Odysseus!
```

These anonymous functions are equally as expressive as the named only,
not limited like Python lambdas.
```

## Civet: for loops


Let's use greet several persons using a for loop statement:

```ts
names = ["Penelope", "Telemachus", "Odysseus"]

function greeting(optional_name = undefined)
  name = if optional_name then optional_name else "Nobody"
  `Hello ${name}!`

function greet(optional_name = undefined)
  console.log greeting(optional_name)

for name of names
  greet(name)
// Hello Penelope!
// Hello Telemachus!
// Hello Odysseus!
```

Like before, we can also collect the greeting messages and use them afterwards.
The equivalent of the list comprehension of Python in Civet ... is the same
for loop we used before, since it collects the values

```ts
greetings =
  for names of names
    greeting(name)

console.log greetings
// ['Hello Penelope!', 'Hello Telemachus!', 'Hello Odysseus!']

for message of greetings
  console.log message
// Hello Penelope!
// Hello Telemachus!
// Hello Odysseus!
```

```lean4
/!-
--------------------------------------------------------------------------------
-/
```

In Lean:


```lean4
def v0.greet (optional_name : Option String := none) : IO Unit := do
    match optional_name with
    | some name => IO.println s!"Hello {name}!"
    | none => IO.println "Hello Nobody!"

#eval v0.greet "Odysseus"
-- Hello Odysseus

#eval v0.greet
-- Hello Nobody

def v1.greet (optional_name : Option String := none) : IO Unit := do
    let name := match optional_name with
      | some name => name
      | none => "Nobody"
    IO.println s!"Hello {name}!"

#eval v1.greet "Odysseus"
-- Hello Odysseus

#eval v1.greet
-- Hello Nobody

def v2.greet (optional_name : Option String := none) : IO Unit :=
    pure (match optional_name with
      | some name => name
      | none => "Nobody"
    )
    >>= fun (x : String) => pure s!"Hello {x}!"
    >>= IO.println

#eval v2.greet "Odysseus"
-- Hello Odysseus!

#eval v2.greet
-- Hello Nobody!
```

--------------------------------------------------------------------------------

Even pseudo-imperative code (sequencing of actions/functions that may have
side-effects) can be desugared into an expression. Here the key is the
*monadic bind* operator `>>=`.

```lean4
/-! `App.lean`:-/
def main : IO Unit := do
  IO.print "Enter your name: "
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trimAscii}"
```

Test with `lean --run App.lean

Equivalent lean code:

```lean4
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
```
