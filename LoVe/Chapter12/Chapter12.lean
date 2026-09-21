import Mathlib

/-!
---
title: "❤️ LoVe Notes – Chapter 12"
author:
- Sébastien Boisgérault
lang: en
---
-/

/-!
# 12.3 The Axiom of Choice
-/

/-!
## In set theory

The classic/default foundation for Mathematics is set theory, described by
the Zermelo-Fraenkel axioms the axiom of choice (ZF+C for the sake of brevity).

In this framework, the axiom of choice reads formally:

$$
\forall c,
\left(
\varnothing \notin c
\rightarrow
\exists f: c \rightarrow \cup c, \; \forall s \in c, \; f(s) \in s
\right)
$$

and, in my opinion, this doesn't look **at all** like the statement of the axiom
of choice in Lean that we will see shortly, which can be quite confusing.

Why the dissimilarity? Arguably, because the Lean version is much closer to an
alternate and less popular, but equivalent version of the axiom of choice in set
theory called *the axiom of global choice*.
So, in order to smooth the transition between ZF+C and Lean, in this section,

  - we will explain what the axiom of choice in ZF+C mean in plain english,

  - explain why the statement is arguably convoluted, what we'd like to state
    instead and why we can't,

  - introduce the concept of class, use it to reformulate the axiom as global
    choice.

### The axiom of choice in plain words

The axiom of choice translates informally to

> For any collection of sets, if none of the sets in the collection
> is empty, there is a function that maps each set in the collection
> to an element of this set.

Note that in this statement, the term "collection" actually means "set";
we only use the word a different term to distinguish the role of the object
that we handle.
Here, there are "items", sets that contains theses items and a "collection"
that contains these sets, but **all these things are sets**, since
in ZF+C theory, every is a set (an integer is a set, a function is a set,
etc.).

Now let's call *choice function* of a collection any function which
maps each set in the collection to an element of this set,
in other words a function which **choses** an element in each set of
the collection. Then we can state the more compact version of the axiom of choice:

> Every collection of non-empty subsets has a choice function.


### Simpler, stronger?

One issue with this statement is that we need to introduce a collection to get
the existence choice function, but it tells us nothing about the
consistency of the choice function on different collections when they
are not disjoint. A stronger and more convenient variant of the
axiom of choice would state the existence of a unique global choice function,
that can make a selection in any non-empty set:

> There is a function mapping each nonempty set to one of its elements.

That would be great in my opinion, except that **it can't work**.
No such a function exist in ZF+C. The reason is that its domain of
definition would be the set of all sets, minus the empty set and we know
is "too large" and that its existence would lead to a paradox[^RP].

[^RP]: If this set $S$ exists, you can perform the union of it with
$\{\varnothing\}$ and you get the set of all sets $V$. Now, by
the [axiom of bounded comprehension](https://en.wikipedia.org/wiki/Axiom_schema_of_specification), the set of all sets that do not belong to themselves
$\{x \in V \; | \; x \not \in x\}$ also exists and this leads to a classic
contradiction, known as [Russel's Paradox](https://plato.stanford.edu/entries/russell-paradox/).

The good news is however that we can slightly alter the statement of this
axiom to make it work, but that requires the concept of classes.

### Classes in set theory

[Classes](class) are meant to describes some collections of sets that are "too large to
be sets", such as: the collections of all sets, the collection of all vector
spaces, the collection of all sets with one element, etc.

There are two equivalent way to introduce them:

  - stay in ZF+C, and work at the syntactic level.
    Introduce for each predicate $\phi$ a symbol $C$ and interpret
    the notation "$x \in C$" as "$\phi(x)$ holds" or equivalently, denote $C$ as
    the (unbounded) comprehension $\{ x \; | \; \phi(x) \}$, (which may not exist
    as a set). For example, the class of all sets exists as
    $\{x \; | \; x = x\}$.
    Every set can be described like that however, since we may
    associate to any set $S$ the predicate $x \in S$.

  - even better, replace ZF+C with [NBG], an alternate axiomatic system
    (NBG stands or von Neuman, Bernays, Gödel), where the objects of the theory are
    not sets but classes. A class is a set if it is the element of some class,
    otherwise it is a *proper class*.

You know have at your disposal the concept of class functions,
whose domain can be either a set or a proper class. For example with $V$ as
the collection of all sets, the function that maps each set with itself.

Now interpret "function" as "class function" instead of "set function" and
you can state the axiom of global choice (GC) in NBG:

> There is a function mapping each nonempty set to one of its elements.

We are pretty confident that using this axiom won't cause a problem in NBG,
since NBG+GC and ZF+C are equiconsistent: there is a paradox in NBG with the
axiom of global choice if and only if there is a paradox in the ZF system with
the classic axiom of choice.
Additionally, NBG+GC is a conservative extension of ZF+C: a statement mentionning
only sets in NBG+GC, not classes, can be proved in NBG+GC if and only if it can
be proved in ZF+C. So both axiomatic system are **very** similar.


[class]: https://en.wikipedia.org/wiki/Class_(set_theory)

[NBG]: https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory

[Von Neumann hierarchy]: https://en.wikipedia.org/wiki/Von_Neumann_universe

-/

/-!


## The axiom of choice in Lean

In Lean, the axiom of choice states that their is a function,
named `choice`, in the namespace `Classical` which associates to any
non-empty sort (i.e. proposition or type) a term of this sort:

-/

#check Classical.choice
-- Classical.choice.{u} {α : Sort u} : Nonempty α → α

/-!
Note that this function is not built on top of other objects, its existence
is postulated: this is an axiom.
-/

#print Classical.choice
-- axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

/-!
## `Nonempty`

`Nonempty` is an inductive type with a single constructor:

-/

#print Nonempty
-- inductive Nonempty.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α

/-!
`Nonempty α` is a proposition that states that there is a term in `α`.
Here `α` can be any proposition or type.

A similar statement in set theory would be something like

$$
\exists \, a, \, a \in \alpha
$$

Of course in the Lean version, there is no "$a \in \alpha$"
since we only consider terms $a$ in $α$ to begin with.
So the equivalence we can actually prove in Lean
is between `Nonempty α` and `∃ (a: α), True`:
-/

example {α} : Nonempty α ↔ ∃ (_ : α), True := by
  constructor
  . intro nonempty
    have ⟨a⟩ := nonempty
    exact Exists.intro a trivial
  . intro exists_a
    have ⟨a, _⟩ := exists_a
    exact Nonempty.intro a

/-!
If you look at the definition of `Exists`, you can see how it is pretty
similar to `NonEmpty`, but with an extra property that needs to be fulfilled.
-/

#print Exists
-- inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop
-- number of parameters: 2
-- constructors:
-- Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p

/-!
We can probably agree that having the custom prop `Nonempty` is nicer than
dealing with an existential statement with a dummy prop attached...
-/

/-!

## `Inhabited`

Some types have a "natural" default value. In Lean, this value should be
declared as an instance of type class `Inhabited`.
-/

#print Inhabited
-- class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Inhabited.default : α
-- constructor:
--   Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α

/-!

The default value of a type can be obtained as the (polymorphic) term `Inhabited.default`.
-/

#check Inhabited.default
-- Inhabited.default.{u} {α : Sort u} [self : Inhabited α] : α

/-!
For example:
-/

#eval (Inhabited.default : ℕ)
-- 0

#eval (Inhabited.default : String)
-- ""

/-!
In both cases, we can check that the corresponding instances of
`Inhabited` have been defined with
-/

#check (inferInstance : Inhabited ℕ)
-- inferInstance : Inhabited ℕ

#check (inferInstance : Inhabited String)
-- inferInstance : Inhabited String

/-!
or equivalently with
-/

#synth Inhabited ℕ
-- instInhabitedNat

#synth Inhabited String
-- String.instInhabited


/-!
But for any inductive type with no constructor,
we cannot declare such an instance;
for example the `Empty` type there is no instance of `Inhabited`:
-/

#print Empty
-- inductive Empty : Type
-- number of parameters: 0
-- constructors:

/-!
-/

/-- error: failed to synthesize instance of type class
  Inhabited Empty

Hint: Adding the command `deriving instance Inhabited for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
#check (inferInstance : Inhabited Empty)


/-!
`Inhabited` and `Nonempty` are related but not identical. Obviously, we can
go from a term (the datum) to the proof of its existence:
-/

example {α} : Inhabited α → Nonempty α := by
  intro inhabited
  exact Nonempty.intro inhabited.default

/-!
or using the fact that `Inhabited` is a type class
-/

example {α} [Inhabited α] : Nonempty α :=
  Nonempty.intro Inhabited.default

/-!
But the converse is not true in constructively:
an instance of `Inhabited α` provides a designated value of type `α` that
we can use in our programs while `Nonempty α` merely provides the proof that
(at least) one value of type `α` exists.

This is different because

> `Prop` does not allow large elimination:
> It is generally impossible to extract information from a proof of a
> proposition and use it in a program
> (i.e., a value of a type belonging to `Type`).
>
> [@LoVe, section 12.2.3]

So basically, we can't use an instance of `Nonempty α` to provide a value
of type α in our programs.

-/

/-!
The axiom of choice however bridges the gap *non-constructively*.
If you flag your values or functions as `noncomputable`, you can use
a value of an non-empty type α inside your programs:
-/

noncomputable def a {α} [nonEmpty : Nonempty α] : α :=
  Classical.choice nonEmpty

/-!
Since this is non-constructive, don't expect to be able to evaluate such a
value!
-/

/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'a', which is 'noncomputable'
-/
#guard_msgs in
#eval a (α := ℕ)

/-!
Note that the axiom of choice is an axiom, not a rule harcoded in Lean's kernel;
you can perfectly work "choice-free" if you are willing to audit all your
dependencies to avoid any use of the axiom fo choice.
-/

/-!
Anyway, if you are ok with being non-constructive, you can now derive
`Inhabited α` from `Nonempty α`:
-/

noncomputable example {α} : Nonempty α → Inhabited α := by
  intro nonEmpty
  exact Classical.choice nonEmpty |> Inhabited.mk

/-!
or equivalently
-/

noncomputable example {α} [nonempty : Nonempty α] : Inhabited α :=
  Classical.choice nonempty |> Inhabited.mk


/-!
Note that that `Inhabited` types are registered as `Nonempty`,
thanks to the declaration:

```lean4
instance (priority := 100) instNonemptyOfInhabited [Inhabited α] : Nonempty α :=
  ⟨default⟩
```
-/

/-!

## Syntaxic sugar

In Mathlib, there is an alternative notation to invoke `Classical.choice`,
that is meant to be used as a method call (i.e. "dot syntax" or [UFCS]).

[UFCS]: https://en.wikipedia.org/wiki/Uniform_function_call_syntax
-/

#print Nonempty.some
-- @[reducible] protected def Nonempty.some.{u_3} :
--     {α : Sort u_3} → Nonempty α → α :=
--   fun {α} h => Classical.choice h

/-!
So for example, we can write
-/
noncomputable example {α} : Nonempty α → Inhabited α :=
  fun nonempty => nonempty.some |> Inhabited.mk

/-!
Another example: a version of the axiom of choice based on collections
(similar to the class version in ZF+C):
-/
theorem nonempty_pi_of_forall_nonempty {ι : Sort u} {c : ι → Sort v} :
    ((i : ι) → Nonempty (c i)) -> Nonempty ((i : ι) → c i) :=
  fun h => Nonempty.intro fun i => (h i).some

/-!
To extract some data from the proof that this example provides, we can do
-/
noncomputable def inhabited_pi_of_forall_nonempty {ι : Sort u} {c : ι → Sort v} :
    ((i : ι) → Nonempty (c i)) -> ((i : ι) → c i) :=
  fun h i => (h i).some

/-!
We can rederive the original axiom of choice from this version:
-/

noncomputable def choice' {α} : Nonempty α → α :=
  fun nonempty =>
    -- Let's build a family of one element of type α
    let ι := Unit -- index type with a single term (the unit)
    let c (_ : ι) := α -- for any index, the data is of type α
    -- Since α is non-empty, all the types in this family are non-empty
    let forall_nonempty (i : ι) : Nonempty (c i) := nonempty
    -- We can invoke the previous theorem to get a function
    -- that extracts a term of the type α for each index
    let choice := inhabited_pi_of_forall_nonempty forall_nonempty
    -- We conclude by specializing this to the unique index of the family
    choice Unit.unit


/-!
## To be or not to be

To apply the axiom of choice to existential statements, we
can use the functions `chose` and `chose_spec`.
-/

#check Classical.choose
-- Classical.choose.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : α

#check Classical.choose_spec
-- Classical.choose_spec.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : p (Classical.choose h)

/-!
Alternatively, we can use `indefiniteDescription`[^id],
which encapsulates the return values of `choose` and
`choose_spec` in a subtype:

[^id]: The terminology originates in Bertrand Russel's [Theory of descriptions].

[Theory of descriptions]: https://en.wikipedia.org/wiki/Theory_of_descriptions
-/
#check Classical.indefiniteDescription
-- Classical.indefiniteDescription.{u} {α : Sort u}
-- (p : α → Prop) (h : ∃ x, p x) : { x // p x }

/-!
The notation `{ x // p x }` is a fancy syntax for `Subtype p`, a type that
encapsulate a term `val` of type `α` and a proof `property` that the the term
satisfies the predicate `p val`.
-/

#print Subtype
-- structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
-- number of parameters: 2
-- fields:
--   Subtype.val : α
--   Subtype.property : p ↑self
-- constructor:
--   Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p


/-!
It's educational to derive these three functions from `Classical.choice`:
-/

noncomputable def indefiniteDescription.{u} {α : Sort u}
    (p : α → Prop) (h : ∃ x, p x) : { x // p x } :=
  have nonempty : Nonempty { x // p x } :=
    -- This unpacking is confined to a Prop context 👍
    let ⟨x, px⟩ : ∃ x, p x := h
    -- Repack as a subtype
    let x_px : { x // p x } := ⟨x, px⟩
    -- Return as a Nonempty prop.
    Nonempty.intro x_px
  Classical.choice nonempty

/-!
That was the most complex step, deriving `choose` and `choose_spec` is easy:
-/

noncomputable def choose.{u} {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : α :=
  indefiniteDescription p h |>.val

theorem choose_spec.{u} {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : p (choose h) :=
  indefiniteDescription p h |>.property

/-!
## Back to sets

The set-theoretic version would use the `Nonempty` method defined
for sets, not the type-theoretic version:
-/
#print Set.Nonempty
-- protected def Set.Nonempty.{u} : {α : Type u} → Set α → Prop :=
-- fun {α} s => ∃ x, x ∈ s

/-!
Note that we have the "obvious"
-/
#print Set.nonempty_iff_ne_empty
-- Set.nonempty_iff_ne_empty.{u} {α : Type u} {s : Set α} : s.Nonempty ↔ s ≠ ∅

/-!
whose proof does not explicitly requires the axiom of choice ...
but it needs contradiction which relies on em ... which is actually
a consequence of choice by Diaconescu's theorem!
-/
example {α} {s : Set α} : s.Nonempty ↔ s ≠ ∅ := by
  constructor
  . rintro ⟨x, hx⟩ s_eq_empty
    rw [Set.empty_def] at s_eq_empty
    rw [s_eq_empty] at hx
    simp only [Set.mem_setOf] at hx
  . by_contra h
    push_neg at h
    have ⟨⟨x, h_in_s⟩, s_eq_empty⟩ := h
    rw [Set.ext_iff] at s_eq_empty
    simp only [Set.mem_empty_iff_false, iff_false] at s_eq_empty
    specialize s_eq_empty x
    contradiction

/-!
The variant of choice applied to sets in Lean would be something like:
-/

noncomputable def choice_set {α} (s : Set α) : s.Nonempty → { x : α // x ∈ s } :=
  fun s_nonempty =>
      -- That line wouldn't work since we would extract type info from Prop
      -- let ⟨x, x_in_s⟩ := s_nonempty
      -- Instead:
      let x := Exists.choose s_nonempty
      let x_in_s := Exists.choose_spec s_nonempty
      ⟨x, x_in_s⟩


#print Exists.choose
-- @[reducible] def Exists.choose.{u_1} : {α : Sort u_1} → {p : α → Prop} →
--     (∃ a, p a) → α :=
-- fun {α} {p} P => Classical.choose P


/-!
## Application : Inverse Function



Note: if `f : α → β`, `g : β → α := Function.invFun f ` is always defined.

TODO: prove as an example than the `invFun` of a bijective function
is bijective, with the usual inverse equations.
-/


#check Function.invFun
-- Function.invFun.{u, u_3} {α : Sort u} {β : Sort u_3} [Nonempty α] (f : α → β) : β → α

#print Function.invFun
-- def Function.invFun.{u, u_3} : {α : Sort u} → {β : Sort u_3} → [Nonempty α] → (α → β) → β → α :=
-- fun {α} {β} [Nonempty α] f y => if h : ∃ x, f x = y then h.choose else Classical.arbitrary α

#print Classical.arbitrary
-- @[reducible] protected def Classical.arbitrary.{u_3} : (α : Sort u_3) → [h : Nonempty α] → α :=
-- fun α [h : Nonempty α] => Classical.choice h

#print Function.Bijective
-- def Function.Bijective.{u₁, u₂} : {α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop :=
-- fun {α} {β} f => Function.Injective f ∧ Function.Surjective f

/-!
## References
-/
