

Lean
================================================================================

... with a bit of Python
--------------------------------------------------------------------------------

✉️ [Sébastien Boisgérault](mailto://Sebastien.Boisgerault@minesparis.psl.eu)

[Lean] is a pure functional programming language with a very powerful static 
type system, designed primarily for software verification 
(ensuring programs are correct) and
formalization of Mathematics (for example [Fermat's theorem]).

[Fermat's theorem]: https://lean-lang.org/use-cases/flt/
[courses]: https://leanprover-community.github.io/teaching/courses.html

And yet Lean is also a very interesting choice as a general-purpose programming
language. A considerable effort has been made to improve its learning curve.
For example, I think that you have a decent chance of guessing what this Lean program does:

```lean
-- 📄 Main.lean
def main (args : List String) : IO Unit := do
  let mut name := ""
  let mut icon := ""
  if args.length == 0 then
    name := "world"
    let worldIcons := ["🌍", "🌎", "🌏"] 
    let i <- IO.rand 0 2
    icon := worldIcons[i]!
  else
    name := args[0]!
    icon := "👋"
  IO.println s!"Hello {name}! {icon}"
```

This program in action in your terminal (you can also [try it in the Lean playground](https://live.lean-lang.org/#codez=CYUwZgBAtghglgOwgChgJwOYGcIC4IAycWALhAMolqIYCUeEAkgPIQCqCcZuAvBMAHsAUBAgAbEGSgBXMghhQQePgCIVI8ZOiyIcAMYCkvCGo1xI6bADoJCDCQAWEHnwAMERyAQbR8xcpMAdwE0MWB1UVEJMmDQ4EYDBBxjAG0VQB4NwFh9lQAaE3TAOH3c/MB4fZUAXR9NMjgIAB4AWiZmKzQYBGAIdwAmKv1DANiwhMMsFLhygEINEDEsECq/JWNLMdcpvsSAlUBeDcBpHYjmqwAHagQSMSQsSZUACVmxAQgAbyWAX0mX/oQ3w6EhADEIAAbjAxNB4EgUpVASCwRDEBBof8gaDwbBEWkCCBDOhBMUVKACQBZATSNoVIA):

```
💻  lean --run Main.lean 
Hello world! 🌏

💻  lean --run Main.lean 
Hello world! 🌍

💻  lean --run Main.lean Leonardo de Moura
Hello Leonardo! 👋
```

Not that hard right? 

However, Lean's dependent type system is also powerful enough 
to describe common mathematical statements and their proofs. 
Its logo is written L∃∀N for a reason! For example:

```lean
def collatzStep (x : ℕ) : ℕ := Id.run do
  if x % 2 == 0 then
    return x / 2
  else
    return 3 * x + 1

def collatz (x₀ : ℕ) (n : ℕ) : ℕ := Id.run do
  let mut x <- x₀
  for _ in [0:n] do
    x <- collatzStep x
  return x
```

```lean
-- Source: https://en.wikipedia.org/wiki/Collatz_conjecture
theorem collatz_conjecture :
  ∀ (x₀ : ℕ), x₀ > 0 -> ∃ (n : ℕ), collatz x₀ n = 1 := by
  admit -- 🚧 TODO, not proof yet! (💀💀💀)
```

### 🎯 Objectives 

In this course, you will

  - Learn enough of Lean to make some practical tools: command-line programs
    (e.g. file-system explorer), Lean librairies (e.g. JSON parser) and
    graphical applications (the snake game!). When it's needed, we'll 
    call Python from Lean to get access to its huge set of libraries!

  - Explore some general/fundamental programming languages concepts 
    and study how Python and Lean implement them in their own way. 
    For example: variables,(im)mutability, values vs objects, loops vs recursion, 
    currying/partial function application, uniform function call syntax,
    type classes vs object-oriented classes/interfaces, etc.  
  
### 🏆 Benefits

Let's get real! You are unlikely to use Lean as your main programming language 
in the future. But

  - You will spend some time learning some foundations of Python 
    that you are likely to reuse. 
    Moreover, since more and more programming languages borrow
    from the playbook of functional programming
    (Rust, Elixir, Scala, etc.), we expect that a lot of your newly
    earned knowledge will be reusable!

  - If you think that you *may* be interested in computer science theory
    or formalization of mathematics, Lean is a great platform for this! 
    We probably won't do much beyond working with Lean as a general-purpose
    programming language, but you will still be better off with this
    course than without if you want to test these waters.

### ⚠️ Warning

This course will be my first attempt at teaching Lean, a language which I know
very little about 😁 (don't try this at home!). Expect some rough edges if you choose to enroll!

[Lean]: https://lean-lang.org/
[Python]: https://www.python.org/

--------------------------------------------------------------------------------

This document: 🔗 <https://github.com/boisgera/leap/blob/main/Manifesto.md>

![Leap manifesto](images/leap-manifesto.svg)
