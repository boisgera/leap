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

## The Axiom of Choice in Set Theory

⚠️ **Warning.** Here we massage the formulation of the axiom of choice in ZFC,
until we end up with an equivalent formulation which is very similar to the
statement of the axiom of choice in a type-theoretic context.
This section is an anti-wtf for the readers who know about set theory;
skip it if you are not familiar with set theory!

The classic axiom of choice in ZFC is:

$$
\forall c,
\left(
\varnothing \notin c
\rightarrow
\exists f: c \rightarrow \cup c, \; \forall s \in c, \; f(s) \in s
\right)
$$

What bugs me in this formulation: the function $f$ depends on the collection
of non-empty sets $c$ but if two collections share some sets we don't know if
both associated choices are the same. That would be nice right?
So can we require this consistency in ZFC "for free"?
The answer is yes! (see below why).

So what? Now consider any increasing
"collection"[^cl] of sets that do no contain the empty sets
and spans the universe of all sets, minus the empty set.
With our strengthened axiom of choice we have just defined a
global choice "function"[^fcl] whose value if defined for any non-empty set of
our universe!

[^cl]: this collection is not a set technically, but a [class].

[^fcl]: technically, a [class] function.

[class]: https://en.wikipedia.org/wiki/Class_(set_theory)

Why does it work? Two possible answers:

- This work trivially in [NBG] (with global choice) and since NBG is a
  conservative extension of ZFC, and the consistency between our choice
  functions can be stated in ZFC, it actually works!

- Without the reference to NBG, we could construct the choice function in a
  consistent manner in the [Von Neumann hierarchy]. And since every collection is
  included at some stage in the cumulative hierarchy (the "union" of all
  V_α is the universe), we get the general result by restriction.
  Anyway, this stuff reads something like: for every ordinal $α$, there is a
  choice function $f: V_{α} \setminus {\varnothing} \to \cup V_{\alpha}$
  such that for any $s \in V_{α} \setminus {\varnothing}$, $f(s) \in s$.
  This is *very* similar to what we're going to introduce as our axiom of
  choice in the type-theoretic context (except that the hierarchy is not
  cumulative and we don't have the equivalent of limit universes,
  only successors).

[NBG]: https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory

[Von Neumann hierarchy]: https://en.wikipedia.org/wiki/Von_Neumann_universe

-/

/-!

## The Axiom of Choice in Type Theory

In type theory the axiom of choice states that their is a function,
named `choice` (in the namespace `Classical`) which associate to any
non-empty sorts (proposition or type) a term of this sort:

-/

#check Classical.choice
-- Classical.choice.{u} {α : Sort u} : Nonempty α → α

/-!
More explicitly maybe, the type of `choice` is:

```
⊢ {α : Sort u} → Nonempty α → α
```
-/

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
`Nonempty α` is a proposition that states that there is an element in `α`.

In set theory we would state something like $\exists \, a, \, a \in \alpha$,
but here, there is no extra "in α", since we only consider `a` in $α$ to
begin with. So what we have is actually:
-/

example {α} : Nonempty α ↔ ∃ (_ : α), True := by
  constructor
  . intro nonempty
    let ⟨a⟩ := nonempty
    exact Exists.intro a trivial
  . intro exists_a
    let ⟨a, _⟩ := exists_a
    exact Nonempty.intro a

/-!
If you look at the definition of `Exists`, you can see how it is pretty
similar to `NonEmpty`, with the extra property that needs to be fulfilled.
-/

#print Exists
-- inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop
-- number of parameters: 2
-- constructors:
-- Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p

/-!
We can probably agree that having a custom prop is nicer than dealing
with this existential statement with a dummy prop attached...
-/

/-!

## `Inhabited`

Some types have a default value:

-/

#eval (Inhabited.default : ℕ)
-- 0

#eval (Inhabited.default : String)
-- ""

/-!
That feature is available for types with an `Inhabited` instance.
-/


#check (inferInstance : Inhabited ℕ)

#check (inferInstance : Inhabited String)

#print Inhabited
-- class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Inhabited.default : α
-- constructor:
--   Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α


/-!
For any inductive type with no constructor,
there is no way we can declare such an instance;
for example:
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
-/

/-- error: failed to synthesize instance of type class
  Inhabited Empty

Hint: Adding the command `deriving instance Inhabited for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
#eval (Inhabited.default : Empty)

/-!
`Inhabited` and `Nonempty` are related but not identical. Obviously, we have:
-/

example {α} : Inhabited α → Nonempty α := by
  intro inhabited
  exact Nonempty.intro inhabited.default

/-!
But the converse is not true in general: an instance of `Inhabited α` provides
a designated value of type `α` that we can use in our programs
while `Nonempty α` merely provides the proof that (at least)
one value of type `α` exists.

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
However, the axiom of choice bridges the gap *non-constructively*.
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
Note that the axiom of choice is an axiom, not a rule in Lean's kernel;
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
**TODO.** Explain/show that `Inhabited` types are automatically `Nonempty`,
thanks to:

```lean4
instance (priority := 100) instNonemptyOfInhabited [Inhabited α] : Nonempty α :=
  ⟨default⟩
```

Show the construction of an `Inhabited` type? (and demonstrate that it's nonempty)

-/

/-!

## Syntaxic sugar


There is an alternative notation to invoke `Classical.choice`,
that is meant to be used in the UFCS style.
-/

#print Nonempty.some
-- @[reducible] protected def Nonempty.some.{u_3} :
--     {α : Sort u_3} → Nonempty α → α :=
--   fun {α} h => Classical.choice h

/-!
So for example:
-/
noncomputable example {α} : Nonempty α → Inhabited α :=
  fun nonempty => nonempty.some |> Inhabited.mk

/-!
Type-theoretic (actually sort-theoretic) version of the axiom of choice
I'm familiar with:
-/
example {ι : Sort u} (c : ι → Sort v) (h : (i : ι) → Nonempty (c i)) :
    Nonempty ((i : ι) → c i) :=
  Nonempty.intro fun i => (h i).some

/-!
... but this version of choice would be *weaker* than the original one
since I get a term in `Prop`, of which I cannot get something as a type.
Can I avoid that and return an object instead of a proof of existence?
Yes, trivially actually!
-/
noncomputable def choice' {ι : Sort u} (c : ι → Sort v)
    (h : (i : ι) → Nonempty (c i)) : (i : ι) → c i :=
  fun i => (h i).some

/-!
and this version is of course powerful enough to get the original choice
axiom back:
-/
noncomputable def choice'' {α} : Nonempty α → Inhabited α :=
  fun nonempty =>
    let f := choice' (ι := Unit) (h := fun _ => nonempty)
    f () |> Inhabited.mk

/-!
**TODO:** work the way up from `choice` to `choose` and `choose_spec`
before dealing with the set-theoretic version of the axiom of choice.
-/

/-!
## To be or not to be

Use the functions `chose` and `chose_spec` to apply the axiom of choice to
existential statements.
-/

#check Classical.choose
-- Classical.choose.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : α

#check Classical.choose_spec
-- Classical.choose_spec.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : p (Classical.choose h)

/-!
Alternatively, use `indefiniteDescription`[^id],
which encapsulates the return values of `choose` and `choose_spec`
in a subtype:

[^id]: The terminology originates in Bertrand Russel's [Theory of descriptions].

[Theory of descriptions]: https://en.wikipedia.org/wiki/Theory_of_descriptions
-/
#check Classical.indefiniteDescription
-- Classical.indefiniteDescription.{u} {α : Sort u}
-- (p : α → Prop) (h : ∃ x, p x) : { x // p x }

/-!
It's educational to derive these three functions from `choice` ourselves:
-/

noncomputable def indefiniteDescription.{u} {α : Sort u}
    (p : α → Prop) (h : ∃ x, p x) : { x // p x } :=
  have nonempty : Nonempty { x // p x } :=
    -- This unpacking is confined to a Prop context 👍
    let ⟨x, px⟩ : ∃ x, p x := h;
    -- Repack as a subtype
    let x_px : { x // p x } := ⟨x, px⟩
    -- Return as a Nonempty prop.
    x_px |> Nonempty.intro
  Classical.choice nonempty

/-!
-/

noncomputable def choose.{u} {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : α :=
  indefiniteDescription p h |>.val

noncomputable def choose_spec.{u} {α : Sort u} {p : α → Prop}
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
