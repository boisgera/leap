import Mathlib

-- ## 12.3 The Axiom of Choice

#print Nonempty
-- inductive Nonempty.{u} : Sort u → Prop
-- number of parameters: 1
-- constructors:
-- Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α

-- Note the difference between `Nonempty` and `Inhabited`: `Inhabited α`
-- provides a default value of `α` that we can use in computations.
-- `Nonempty α` provides merely the proof that such a value exist.
-- This is different because there is no large elimination for props
-- (you generally cannot extract information from a proof and use it
-- in a program).

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

-- TODO: work the way up to `Classical.choose` and `Classical.choose_spec`
-- before dealing with the set-theoretic version of the axiom of choice.

-- The set-theoretic version would use the `Nonempty` method defined
-- for sets, not the type-theoretic version:
#print Set.Nonempty
-- protected def Set.Nonempty.{u} : {α : Type u} → Set α → Prop :=
-- fun {α} s => ∃ x, x ∈ s

-- Note that we have the "obvious"
#print Set.nonempty_iff_ne_empty
-- Set.nonempty_iff_ne_empty.{u} {α : Type u} {s : Set α} : s.Nonempty ↔ s ≠ ∅

-- whose proof does not require the axiom of choice (but is not constructive
-- however, it requires classical logic):
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
