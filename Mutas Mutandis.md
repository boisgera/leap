Mutas Mutandis
================================================================================

TODO: Harry Potter image?

Memory
--------------------------------------------------------------------------------

Arena, Pointers, etc.

Python
--------------------------------------------------------------------------------

  - every variable is a "pointer", refers to an object in memory

  - `a = ...` creates a new binding, the data is actually somewhere else;
    there is no copy involved

  - see that with `id`

  - one has to distinguish equality `==` and identity `is`

  - some data type are mutable, some are immutable. Ask/demo

    - mutable: lists, dicts, sets, ...

    - immutable: bool, int, float, str, ...
      See the pattern (and GOTCHA!) with strings when for example doing a
      `replace` operation: it returns a new string, it does not modify the
      original string. If you forget to assign the result to a variable,
      you lose the result of the operation.

    - immutable (sort of): tuple (explain that the data structure is immutable,
      but the elements pointed to can be modified)
      **BUT** that lose definition of immutability would break referential
      transparency, so it's almost useless. Let's say that this structure is
      read-only, or has shallow immutability if you wish (vs deep immutability).

  - Talk about referential transparency immutable structures and pure functions.

  - Concrete example of why immutability and pure function are VERY handy.
    Two examples in Python on stuff that would "break".

    ```python
    import math

    def exp(x):
        ...


    def sigmoid(x):
        return exp(x) / (exp(x) + 1)
    ```

    Now consider the following:

    ```python
    def exp(x : float) -> float:
        import random
        roll = random.rand(1, 6)
        if roll =! 1:
            return math.exp(x)
        else:
            return math.nan
    ```

    This is a non-deterministic function, it does not always return the same
    result for the same input. Good luck testing it as a black block!
    The Python typing system will NOT help you there ... Mypy is perfectly 
    happy with this code, it will not complain about the non-determinism
    (which is a special kind of impurity)

    Interestingly, even if we add infinite precision on the computation,
    we cannot assume that the result is equal to `1.0 / (1.0 + exp(-x))`, 
    because the two calls to `exp` with the same value 
    may return different results.

  - Another (accordingly worse) example: what if Python add mutable floats?

    ```python
    class Float:
        def __init__(self, value=0.0):
            if isinstance(value, Float):
                value = value.value
            self.value = value

        def __add__(self, other):
            other = Float(other)
            return Float(value + other.value)

        __radd__ = __add__

        def __repr__(self):
            return f"{self.value}"

    def exp(x : Float) -> Float:
        return Float(math.exp(x.value))

    def sigmoid(x : Float) -> Float:
        return exp(x) / (exp(x) + Float(1.0))
    ```

    Everything's fine, right? But now consider the following implementation of `exp`:

    ```python
    def exp(x : Float) -> Float:
        y = Float(x) # copy of x
        x.value = math.nan # mutation of x
        return Float(math.exp(y.value))
    ```

    With the same implementation of `sigmoid`, we now have a problem:

    ```pycon
    >>> x = Float(0.0)
    >>> sigmoid(x)
    0.5
    >>> x
    nan
    ```

    The Python typing system will NOT help you there either, it will not
    complain about the mutation of `x` in the `exp` function. But the
    immutability of the builtin `float` class does actually prevented this 
    class of problems.

    Reference to: "we are all consenting adults here" 
    (see <https://mail.python.org/pipermail/tutor/2003-October/025932.html>) 
    and the Python philosophy.

TODO: a word about C or Zig, where variables are not pointers, 
but "memory slots"? And you have "const" and stuff and explicit pointers?


"Variables"
--------------------------------------------------------------------------------

TODO: let, x and x', shadowing, let mut (do block only) that can't be shadowed.

  - `let` is a binding, not a variable, it cannot be changed
  - `x` and `x'` are different bindings, they can refer to the same object
  - shadowing: `let x = ...` in a nested scope shadows the outer `x`
  - `let mut x = ...` is a mutable binding, it can be changed, but it cannot
    be shadowed (it can only be reassigned)
  - `let mut x = ...; x = ...` is a reassignment, not a mutation

How are "variables" called in the FP literature? OK, "variables", because the
rhs my be the argument of a function, so they effectively can refer to different
values.

Copilot : In functional programming, "variables" are often referred to as "bindings" or "names". This is because they are not mutable in the same way as in imperative programming. Once a binding is established, it cannot be changed to refer to a different value.

Warning: names denotes data **in a given context**.

Nota: at first sight you may assume that immutable variables and shadowing are
good enough to emulate directly all imperatives patterns, but consider:

```lean
def f (n : Nat) : Nat := Id.run do
  if n % 2 == 0 then
    let m := n / 2
  else
    let m := 3 * n + 1
  return m
```

It doesn't work! Because the scoping of the variable `m` is limited to the
if branch ... So either you can go functional (if is an expression):

```lean
def f (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1
```

or you embrace mutable variables:


```lean
def f (n : Nat) : Nat := Id.run do
  let mut n := 0
  if n % 2 == 0 then
    m := n / 2
  else
    m := 3 * n + 1
  return m
```

The same issue happens for for loops.



Immutable Data Structures
--------------------------------------------------------------------------------

  - The easy way to have immutable data structures: have mutable data structures
    and copy them before any operation, then don't forget to also return the
    new state.

    Example: an immutable list in Python? (TODO)  

  - NOT efficient. Classic data structures (and corresponding algorithms that
    assume mutability, e.g. some sorting algorithms) are not efficient if
    we do that. We *may* have to rethink everything and introduce new data
    structures that are designed for immutability and the corresponding algorithms.

    - Example: `List` is the best example of that.

      - Say a word about the implementation of `List`

      - Play with the API of List

      - "Performance" gotchas

      - Implement List in Lean on top of a memory pool (implemented as an array).

    - Extra references: example: Huet Zipper, 
      <https://en.wikipedia.org/wiki/Functional_data_structure#Persistent_data_structures>

  - However we are only talking algorithmic performance, not real-world performance
    which is often dominated by the memory access patterns and cache misses and
    where data locality is of utmost importance.

    => Introduce arrays in Lean

    Now this structure is mutable so it seems that copy is going to cost us
    a lot. But actually only the interface to arrays from Lean has to be
    immutable, the underlying data structure can be mutable. 

    Through its ref-counted garbage collector, Lean is able to detect when
    there is a single "owner" of the data structure, and then it can
    mutate it in place without copying it. This is a very smart way to
    implement immutable data structures in a language with garbage collection.

    Reference to the array paper in Lean