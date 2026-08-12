
In Python, most data is *mutable*: you can change the content of an object
after it has been created, without creating a new object. Lists are the
classic example. `Lean`, on the other hand, has no mutable data at all:
every value, once built, stays exactly as it is forever.

This sounds like a small technical detail, but it has deep consequences on
how you reason about programs. Let's look at mutability in Python first,
then see what changes when there is none.

--------------------------------------------------------------------------------

### Two ways to prepend

Python lists have (at least) two APIs to put an element in front of a list:
an *in-place* one, that mutates the list, and a "functional" one, that
builds a new list and leaves the original untouched.

```python
# in-place API: mutates the list, returns nothing
xs = [1, 2, 3]
ys = xs           # ys and xs refer to the *same* list object
ys.insert(0, 0)
print(xs)          # [0, 1, 2, 3]  <- xs changed too!
print(ys)          # [0, 1, 2, 3]
print(xs is ys)    # True: same object
```

```python
# functional API: builds a brand new list
xs = [1, 2, 3]
ys = [0] + xs      # a new list is created
print(xs)          # [1, 2, 3]  unchanged
print(ys)          # [0, 1, 2, 3]
print(xs is ys)    # False: two different objects
```

`is` tests *identity*: whether two names refer to the exact same object in
memory. `id(x)` returns a number that identifies this location. Identity is
a notion that only makes sense because Python values live *somewhere* and
can be pointed to from several places at once.

--------------------------------------------------------------------------------

### In-place mutation is dangerous

Sharing a mutable object is fine as long as nobody mutates it. But as soon
as one piece of code mutates a list that another piece of code also holds a
reference to, surprises happen. A classic beginner trap: a mutable default
argument.

```python
def prepend_zero(xs=[]):
    xs.insert(0, 0)
    return xs

a = prepend_zero()
print(a)  # [0]
b = prepend_zero()
print(b)  # [0, 0]   <- the default list survived and grew across calls!
```

The default value `[]` is created *once*, when the function is defined, not
on every call. Since `insert` mutates it in place, every call that relies on
the default shares -- and corrupts -- the same list.

### A "snake" that doesn't actually move

Here is a more insidious version of the same bug: recording the complete
trail of a snake that moves on a grid, one point at a time.

```python
LEFT  = (-1,  0)
RIGHT = (+1,  0)
UP    = ( 0, -1)  # canvas convention: the y-axis points downwards.
DOWN  = ( 0, +1)

snake = [(0, 0), (1, 0), (2, 0)]  # from tail to head

def move_snake(snake, direction):
    head = snake[-1]
    new_head = (head[0] + direction[0], head[1] + direction[1])
    snake.append(new_head)
    snake.pop(0)  # get rid of the old tail

trail = snake  # record the initial serpent geometry in the trail.

for direction in [DOWN, DOWN, DOWN]:
    move_snake(snake, direction)
    head = snake[-1]
    trail.append(head)
```

What we are expecting at the end:

```pycon
>>> snake
[(2, 1), (2, 2), (2, 3)]
>>> trail
[(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (2, 3)]
```

What we get instead is:

```pycon
>>> snake
[(2, 1), (2, 1), (2, 2), (2, 2), (2, 3), (2, 3)]
>>> trail
[(2, 1), (2, 1), (2, 2), (2, 2), (2, 3), (2, 3)]
```

The culprit is a single line: `trail = snake` does not make a copy, it just
gives the same list a second name.

```pycon
>>> snake is trail
True
```

From then on, `move` mutates that one shared list (`append` then `pop`),
and `trail.append(head)` mutates it *again* right after -- both names are
watching the same object being rewritten underneath them, three times over.
There never was a separate history being built at all.

The fix doesn't need to touch `move`, or the loop, or anything inside it:
just give `trail` its own, independent copy of the initial geometry.

```python
trail = list(snake)   # an independent copy, not another name for `snake`

for direction in [DOWN, DOWN, DOWN]:
    move_snake(snake, direction)
    head = snake[-1]
    trail.append(head)
```

```pycon
>>> snake
[(2, 1), (2, 2), (2, 3)]
>>> trail
[(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (2, 3)]
>>> snake is trail
False
```

Everything *inside* the loop was already correct: `head` is a tuple, an
immutable value, so `trail.append(head)` was always safe on its own. The
only actual bug was reusing `snake`'s identity for `trail` instead of
giving it one of its own.


Another option, more disciplined, that does not require a detailed analysis
to work: use functions that never mutate/reuse their arguments and return
brand new objects instead.

```python
LEFT  = (-1,  0)
RIGHT = (+1,  0)
UP    = ( 0, -1)  # canvas convention: the y-axis points downwards.
DOWN  = ( 0, +1)

snake = [(0, 0), (1, 0), (2, 0)]  # from tail to head

def move_snake(snake, direction):
    head = snake[-1]
    new_head = (head[0] + direction[0], head[1] + direction[1])
    new_snake = snake[1:] + [new_head]
    return new_snake

def update_trail(trail, new_head):
    new_trail = trail + [new_head]
    return new_trail

trail = snake  # record the initial serpent geometry in the trail.

for direction in [DOWN, DOWN, DOWN]:
    snake = move_snake(snake, direction)
    head = snake[-1]
    trail = update_trail(trail, head)
```

`trail` is never mutated: `update_trail` always builds and returns a brand
new list, so there is no in-place `.append` left anywhere to accidentally
reach for. The initial `trail = snake` aliasing is now completely harmless,
for the same reason the earlier fix was: nothing ever mutates either name
again, so having them briefly point at the same object changes nothing
observable.

--------------------------------------------------------------------------------

### A classic immutable type: strings

Python strings, unlike lists, are immutable: there is no in-place API for
them at all. Every operation that looks like it "changes" a string actually
builds a new one.

```python
s = "hello"
print(s.upper())  # "HELLO"
print(s)          # "hello", unchanged: `upper` returns a new string

t = s
t += "!"
print(s)          # "hello"
print(t)          # "hello!"
print(s is t)      # False: `+=` rebound `t` to a freshly built string
```

No method on `str` can mutate the object it is called on. This is exactly
the property Lean gives to *every* value, not just strings.

--------------------------------------------------------------------------------

### A mixed case: tuples

Tuples look immutable: there is no method to insert, remove or reassign an
element.

```python
t = (1, 2, 3)
t[0] = 99
# TypeError: 'tuple' object does not support item assignment
```

But a tuple can hold a *mutable* object, such as a list. And then:

```python
t = ([1, 2], 3)
print(t)          # ([1, 2], 3)
t[0].append(4)
print(t)          # ([1, 2, 4], 3)   <- t "changed", even though we never
                   #                    assigned anything to t!
```

Is `t` really immutable? Yes and no. As an object, `t` is a small structure
holding two *pointers*: one to a list object, one to the integer `3`. Those
two pointers never change -- `t` always points to the very same list and the
very same integer, for its whole life. In that sense `t` is immutable.

But pointers are exactly what characterizes an object's identity in Python
(recall `is` and `id` above). To turn `t` into readable text, `repr` has to
*dereference* those pointers: it has to go and read whatever currently lives
at the addresses `t` points to. So `repr` is not really a pure function of
`t` alone -- it silently takes the whole memory state as a second, implicit
argument. When that memory state changes (because someone mutated the list
`t` points to), `repr t` can change too, even though `t` itself never moved.

Note that in the last version of our snake example, we have created new
lists, but reused the pairs of integers they contained.
This is fine, we didn't need to copy those beforehand because
integers are immutable hence pairs of integers are immutable in the
strongest interpretation of the term.

--------------------------------------------------------------------------------

### In Lean, everything is immutable

Lean has no mutation API whatsoever. Strings behave the way Python strings
do -- but now *every* type does.

```lean4
def s : String := "hello"

#eval s.push '!'
-- "hello!"

#eval s
-- "hello"
```

There is no operation, anywhere in the language, that could make the second
`#eval` print anything other than `"hello"`. `s` is not a location whose
content might have been overwritten; `s` *is* the value `"hello"`.

The same holds for lists. Prepending an element does not touch the original
list, it builds a new one:

```lean4
def xs : List Nat := [1, 2, 3]
def ys : List Nat := 0 :: xs

#eval xs
-- [1, 2, 3]

#eval ys
-- [0, 1, 2, 3]
```

This is exactly the "functional" API on the Python side (`[0] + xs`) -- Lean
simply doesn't offer the other one.

--------------------------------------------------------------------------------

### No identity, no problem

Under the hood, `ys` is very likely represented as a small cell pointing to
`0` and to the *very same* list structure as `xs` -- exactly the kind of
sharing that caused all the trouble in the Python snake example. So why is
it never a problem here?

Because there is no notion of identity or location in the language you can
observe. Lean has no `is` operator, no `id` function, nothing that lets a
program ask "are these two values the same object in memory?". The only
question you can ask is whether two values are *equal*, i.e. whether they
have the same content:

```lean4
#eval xs == ys.tail
-- true
```

Values can be shared -- passed around, stored in several places, reused by
several pieces of code at once -- completely for free. Since no piece of
code can ever mutate a shared value, sharing is entirely invisible: nothing
that observes a value can tell whether it is "the" value or "a copy of" it,
because there is no difference. Let's translate the last version of the
Python snake example, line for line, and see what happens to its bug:

```lean4
def LEFT  : Int × Int := (-1,  0)
def RIGHT : Int × Int := ( 1,  0)
def UP    : Int × Int := ( 0, -1)
def DOWN  : Int × Int := ( 0,  1)

def moveSnake (snake : List (Int × Int)) (direction : Int × Int) : List (Int × Int) :=
  let head := snake.getLast!
  let newHead := (head.1 + direction.1, head.2 + direction.2)
  snake.tail ++ [newHead]

def updateTrail (trail : List (Int × Int)) (head : Int × Int) : List (Int × Int) :=
  trail ++ [head]

#eval Id.run do
  let mut snake : List (Int × Int) := [(0, 0), (1, 0), (2, 0)]  -- from tail to head
  let mut trail := snake                                        -- record the geometry
  for direction in [DOWN, DOWN, DOWN] do
    snake := moveSnake snake direction
    let head := snake.getLast!
    trail := updateTrail trail head
  return (snake, trail)
-- ([(2, 1), (2, 2), (2, 3)], [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (2, 3)])
```

`trail := snake` is not aliasing, it is just giving the current value of
`snake` a second name. There is nothing to alias: neither `moveSnake` nor
`updateTrail` has any way to mutate its arguments, so `snake := moveSnake
snake direction` and `trail := updateTrail trail head` only ever rebind
names to brand new lists. `trail` never notices what happens to `snake`
afterwards.

The result above is exactly the "expected" column from the Python version,
never the "got" one -- and unlike the Python `update_trail`, there is no
in-place `.append` left anywhere to sneak back in by accident. The bug is
not avoided here by discipline or a defensive copy, it is simply not a
sentence you can write.
