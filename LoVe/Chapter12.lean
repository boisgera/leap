import Mathlib

/-

## 12.3 The Axiom of Choice


### The Axiom of Choice in Set Theory

⚠️ Warning: Large digression

Here we try to "massage" the classical formulation of the axiom of choice in
ZFC, until we end up with a formulation and understanding that will make
the transition to the type-theoretic version much smoother.

The classic:

$$
\forall c,
\left(
\emptyset \notin c
\rightarrow
\exists f: c \rightarrow \cup c \; \forall s \in c \; f(s) \in s
\right)
$$

What lacks IMHO: the function $f$ depends on the collection of non-empty sets
$c$ but if two collections share some sets we don't know if both associated
choices are the same. That would be nice! More generally what it hints to
is that we'd like to get a single *global* choice function, defined on
the class of sets which are not empty (which is not a set, this is why
we can't state that axiom in ZFC). All the "classic" choice functions
would then be restrictions of this global choice to a specific family.

This idea works perfectly in NBG and since NBG is a conservative extension of
ZFC, and the consistency between our choice functions can be stated in ZFC,
it actually works! This new, augmented version of the axiom of choice in ZFC
make it appear as simply a bounded version of the global choice.

Note that without the reference to NBG, we could work out the same result
by a definition of the choice function in a consistent manner
in the cumulative hierarchy. And since every collection is included at some
stage in the cumulative hierarchy, the general result is obtained by
restriction. Anyway, this stuff reads something like:

For every ordinal $α$, there is a choice function
$f: V_{α} \setminus {\varnothing} \to \cup V_{\alpha}$ such that
for any $s \in V_{α} \setminus {\varnothing}$, $f(s) \in s$.

This is *very* similar to what we're going to introduce as our axiom of choice
in the type-theoretic context (except that the hierarchy is not cumulative
and we don't have the equivalent of limit universes, only successors).

-/

#print Nonempty
-- inductive Nonempty.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α

/-
`Nonempty α` captures that there is an element in `α`.
In set theory we would state something like $\exists a, a \in \alpha$,
but here, there is no extra "in α", since we only consider `a` in $α$ to
begin with. So what we have is actually:
-/

example {α} : Nonempty α ↔ ∃ (_a : α), True := by
  constructor
  . intro nonempty
    let ⟨a⟩ := nonempty
    exact Exists.intro a trivial
  . intro exists_a
    let ⟨a, _⟩ := exists_a
    exact Nonempty.intro a

/-
We can probably agree that having a custom prop is nicer than dealing
with this existential statement with a dummy prop attached...
-/

/-
Note the difference between `Nonempty` and `Inhabited`: `Inhabited α`
provides a default value of `α` that we can use in computations.
`Nonempty α` provides merely the proof that such a value exist.
This is different because there is no large elimination for props
(you generally cannot extract information from a proof and use it
in a program).
-/

#print Inhabited
-- class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Inhabited.default : α
-- constructor:
--   Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α

-- Obviously, we have:

example {α} : Inhabited α → Nonempty α := by
  intro inhabited
  exact Nonempty.intro inhabited.default

-- The axiom of choice bridges the gap. Note that it's an axiom,
-- not a rule in Lean's kernel; you can perfectly work "choice-free"
-- if you are willing to audit all your dependencies.

#check Classical.choice
-- Classical.choice.{u} {α : Sort u} : Nonempty α → α

-- TODO: this is also more explicitly : {α : Type u} → Nonempty α → α
-- Or: the existence of a function defined on all types that are not empty
-- and which creates an element of the type. This is VERY close to what the
-- global choice function is doing in NBG and could somehow helps us explain
-- why this is not so different from the set-theoretic version after all.
-- (At first sight, it looks VERY different)
-- But there is some explaining work to do ...

noncomputable example {α} : Nonempty α → Inhabited α := by
  intro nonempty
  exact Classical.choice nonempty |> Inhabited.mk

-- Note that the LSP asked me to mark the example as noncomputable
-- since choice is not supported by the code generator. Fair enough!

-- There is an alternative notation to invoke `Classical.choice`,
-- that is meant to be used in the UFCS style.

#print Nonempty.some
-- @[reducible] protected def Nonempty.some.{u_3} :
--     {α : Sort u_3} → Nonempty α → α :=
--   fun {α} h => Classical.choice h

-- So for example:
noncomputable example {α} : Nonempty α → Inhabited α :=
  fun nonempty => nonempty.some |> Inhabited.mk

-- Type-theoretic (actually sort-theoretic) version of the axiom of choice
-- I'm familiar with:
example {ι : Sort u} (c : ι → Sort v) (h : (i : ι) → Nonempty (c i)) :
    Nonempty ((i : ι) → c i) :=
  Nonempty.intro fun i => (h i).some

-- ... but this version of choice would be *weaker* than the original one
-- since I get a term in `Prop`, of which I cannot get something as a type.
-- Can I avoid that and return an object instead of a proof of existence?
-- Yes, trivially actually!

noncomputable def choice' {ι : Sort u} (c : ι → Sort v)
    (h : (i : ι) → Nonempty (c i)) : (i : ι) → c i :=
  fun i => (h i).some

-- and this version is of course powerful enough to get the original choice
-- axiom back:
noncomputable def choice'' {α} : Nonempty α → Inhabited α :=
  fun nonempty =>
    let f := choice' (ι := Unit) (h := fun _ => nonempty)
    f () |> Inhabited.mk

-- TODO: work the way up from `choice` to `choose` and `choose_spec`
-- before dealing with the set-theoretic version of the axiom of choice.

#check Classical.choose
-- Classical.choose.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α

#check Classical.choose_spec
-- Classical.choose_spec.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : p (Classical.choose h)

-- The construct that actually encapsulate both `choose` and `choose_spec`
#print Classical.indefiniteDescription
-- Classical.indefiniteDescription.{u} {α : Sort u} (p : α → Prop)
--   (h : ∃ x, p x) : { x // p x }

noncomputable def indefiniteDescription.{u} {α : Sort u} (p : α → Prop)
    (h : ∃ x, p x) : { x // p x } :=
    ( -- This destructuring needs to be confined to a Prop context.
      let ⟨x, px⟩ : ∃ x, p x := h;
      -- we destructure only to restructure in a different type
      let x_px : { x // p x } := ⟨x, px⟩
      x_px |> Nonempty.intro -- OK, this is a Prop
    ) |> Classical.choice



-- -----------------------------------------------------------------------------

-- The set-theoretic version would use the `Nonempty` method defined
-- for sets, not the type-theoretic version:
#print Set.Nonempty
-- protected def Set.Nonempty.{u} : {α : Type u} → Set α → Prop :=
-- fun {α} s => ∃ x, x ∈ s

-- Note that we have the "obvious"
#print Set.nonempty_iff_ne_empty
-- Set.nonempty_iff_ne_empty.{u} {α : Type u} {s : Set α} : s.Nonempty ↔ s ≠ ∅

-- whose proof does not explicitly requires the axiom of choice ...
-- but it needs contradiction which relies on em ... which is actually
-- a consequence of choice by Diaconescu's theorem!
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

-- The variant of choice applied to sets in Lean would be something like:

#check Exists.choose
-- Exists.choose.{u_1} {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a) : α

#check Exists.choose_spec
-- Exists.choose_spec.{u_1} {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a) : p P.choose


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

#check Classical.choose
-- Classical.choose.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α

#check Classical.choose_spec
-- Classical.choose_spec.{u} {α : Sort u} {p : α → Prop}
--     (h : ∃ x, p x) : p (Classical.choose h)

example {α} {ι} (s : ι → Set α) (h : ∀ i, (s i).Nonempty) :
    { f : ι → α // ∀ (i : ι), f i ∈ s i } := by
  -- TODO
  admit

-- Can I produce a FULL set-theoretic versions, without indexed families
-- but with set of sets instead?
