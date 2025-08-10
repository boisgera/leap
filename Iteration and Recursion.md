

TODO:

   - consider factorial, collatz and fibonacci as example?

   - start with the imperative version with the for loop.

And then if you can't/don't want to use monads & for loops:
 
   - consider the manual recursive versions? See the issue with the naive
     versions (factorial: not tail-recursive, burns memory, fibonnaci:
     not tail-recursive, recomputes values => explosion ; collatz is fine? 
     (kinda))

```lean
def collatz (x0 n : Nat) : Nat :=
  match n with 
  | 0 => x0
  | 1 => if (x0 % 2) == 0 then x0 / 2 else 3 * x0 + 1
  | n + 1 => collatz (collatz x0 1) n 
  -- better than collatz (collatz x0 n) 1? Why? More friendly to the call stack!
```

TODO: illustrate stack recursion limit in Python (which is NOT tail-recursive).

```lean
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
```

```lean
def fibonacci (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => (fibonacci n) + (fibonacci (n + 1))
```

Let's improve factorial first with an auxilary function:

(Nota: `List.prod` is from mathlib ; defined as:

`def List.prod : (List Nat) -> Nat := List.foldr (· * ·) 1`

Why `foldr`? It may blow up the stack (since Lean is eager ; Haskell may not
have this issue in practice) but it follows more the "grain" or
recursive definition of data structures such as list.

For example, what happens when we try to add 1 to each element in a List in
Lean, using foldl and foldr? **TODO**

Note: <https://news.ycombinator.com/item?id=22625957>

> The standard libraries of strict languages agree. 
> Python's `functools.reduce` and JavaScript's `Array.prototype.reduce` 
> perform strict left folds equivalent to Haskell's `foldl'`.

So why was foldr selected in Mathlib for List.prod? Copy of Haskell?

See also : <https://en.wikipedia.org/wiki/Fold_(higher-order_function)>

Nota: I guess that the preservation of structure of foldr on List is clear
from the Wikipedia article. And therefore I guess that if all you want to
do is a proof (and you will use induction, you won't actually compute the
lists), foldr is nicer.

)

```lean
def factorialAux (n : Nat) (state : List Nat) :=
  match n with
  | 0 => List.prod state
  | n + 1 => factorialAux n ((n + 1) :: state)

def factorial (n : Nat) : Nat :=
  factorialAux n [1]
```

Inner function variant

```lean
def factorial (n : Nat) : Nat :=
  let rec factAux (n : Nat) (state : List Nat) :=
    match n with
    | 0 => List.prod state
    | n + 1 => factAux n ((n + 1) :: state)
  factorialAux n [1]
```

but here we can be smarter and consolidate the state we need at each step!
(and avoid `List.prod` altogether)

```lean
def factorial (n : Nat) : Nat :=
  let rec factAux (n : Nat) (prod : Nat) :=
    match n with
    | 0 => prod
    | n + 1 => factAux n (prod * (n + 1))
  factAux n 1
```

Bonus: use default arguments to avoid the inner function!

```lean
def factorial (n : Nat) (prod := 1) : Nat :=
  match n with
  | 0 => prod
  | n + 1 => factorial n (prod * (n + 1))
```

If we are nostalgic of the for loop

```lean
def factorial (n : Nat) : Nat := Id.run do
  let mut prod := 1
  for k in [1:n+1] do
    prod <- prod * k
  return prod
```

you can try `List.foldl`, defined as

```lean
def List.foldl {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α
  | a, []     => a
  | a, b :: l => List.foldl f (f a b) l
```

(note : foldl is tail-recursive!)

like that :

```lean
def factorial (n : Nat) : Nat :=
  let indices := List.range' (start := 1) (len := n)
  List.foldl (f := fun (prod i) => prod * i) (init := 1) indices
``` 

or if you like read-only terse code:

```lean
def factorial (n : Nat) : Nat :=
  n |> List.range' 1 |> List.foldl (· * ·) 1
```