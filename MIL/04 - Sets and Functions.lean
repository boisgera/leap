import Mathlib

#check ℕ
-- The natural numbers **as a type**.

#check Set ℕ -- The type of all subsets of (the type) ℕ
-- Set ℕ : Type

#check Set.univ (α := ℕ) -- ℕ **as a subset of ℕ**.
-- Set

#check { x : ℝ | ∃ n : ℕ, ↑n = x } -- ℕ as a subset of ℝ.

-- Not only are they different, their equality doesn't even typecheck!
-- Their comparison doesn't make sense (at compile time)!

/--
error: Type mismatch
  {x | ∃ n, ↑n = x}
has type
  Set ℝ
but is expected to have type
  Set ℕ
-/
#guard_msgs in
#check Set.univ (α := ℕ) = { x : ℝ | ∃ n : ℕ, ↑n = x }

-- There is no **ℕ as a set**, in abstracto, it's always in the context of
-- a bigger set.

-- This is similar to what you get for other objects: `0 : ℕ` and `0 : ℝ`
-- both make sense. Here, `∅ : Set ℕ` and `∅ : Set ℝ` make sense, not `∅`
-- in abstracto.

-- Not everything is a set (the theory is typed), so propositions like `0 ∈ 1`
-- don't make sense to begin with. A prop `x ∈ y` will make sense if the
-- type of `x` is `α` and the type of `y` is `Set α`. ("safer")

-- -----------------------------------------------------------------------------
-- "Collections" of sets

#check Set (Set ℕ) -- The type of all collections of subsets of ℕ
-- Set (Set ℕ) : Type

#check Set.univ (α := ℕ) -- The powerset of ℕ : set of all subsets of ℕ
-- Set.univ : Set ℕ

-- -----------------------------------------------------------------------------

-- Technically, a subset of α is merely a function α → Prop.
-- The set-builder notation is a syntactic convenience to make it
-- more familiar to deal with collections of functions α → Prop,
-- and the usual set operations can be considered as syntactic
-- sugar on top on operations on such Props.

example {α} : Set α = (α -> Prop) := by rfl

example {α} {p : α → Prop} : { a : α | p a } = p := by rfl -- or simply { a | p a }

-- -----------------------------------------------------------------------------

-- In a given type, there is a unique empty set:

def emptySet {α} : Set α := ∅

-- But the notation ∅ is overriden, used in any context where the
-- EmptyCollection typeclass applies, such as lists.
def emptyList {α} : List α := ∅
-- This is why we'll often need explicit type annotations in the sequel.

-- If you don't like ∅, the notation {} also works!
example {α} : (∅ : Set α) = {} := by rfl

-- In the "subsets as props" paradigm, `∅` is (the constant function) `False`:

example {α} : (∅ : Set α) = fun (_ : α) => False := by rfl

-- which looks nicer in set-builder syntax:

example {α} : (∅ : Set α) = {_a : α | False} := by rfl

-- This property is actually recorded as `empty_def`.

#check Set.empty_def
-- Set.empty_def.{u} {α : Type u} : ∅ = {_x | False}

-- Applying a predicate `p : α → Prop` to some `a : α` reads in set syntax as
-- `a ∈ {x | p x}`: to simplify a ∈ {x | p x} into p a (or the converse),
-- use `Set.mem_setOf`.
#check Set.mem_setOf
-- Set.mem_setOf.{u} {α : Type u} {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a

-- Well, strictly speaking we don't *have* to, we can use any of the three
-- formulations which are definitionally equal:

#check (· ≥ 10) 11
-- (fun x => x ≥ 10) 11 : Prop

#check {n | n ≥ 10} 11
-- {n | n ≥ 10} 11 : Prop

#check 11 ∈ {n | n ≥ 10}
-- 11 ∈ {n | n ≥ 10} : Prop

-- ... but you have to admit that the 2nd one looks a bit weird.
-- Note that since this stuff is definitionally equal, if your prop is
-- decidable, you can evaluate the ∈ condition, as you would with the
-- "raw" prop:

#eval 11 ∈ {n | n ≥ 10}
-- true


-- Let's work out some basic stuff about the empty set!

-- There is nothing into the empty set:
example {α} (x : α) : ¬(x ∈ (∅ : Set α)) := by
  intro x_in_empty
  rw [Set.empty_def, Set.mem_setOf] at x_in_empty
  exact x_in_empty

-- Conversely, if you have no element, you're the empty set
example {α} (s : Set α) : (∀ x, x ∉ s) → s = ∅ := by
  intro h
  ext x
  constructor
  . intro x_in_s
    specialize h x x_in_s
    contradiction
  . intro x_in_empty
    rw [Set.empty_def, Set.mem_setOf] at x_in_empty
    contradiction

-- This is summarized as:
#check Set.mem_empty_iff_false
-- Set.mem_empty_iff_false.{u} {α : Type u} (x : α) : x ∈ ∅ ↔ False

-- Corollary (of sorts): there is a unique set which is empty:
example {α} : ∃! (s: Set α), s = {_x | False} := by
  rw [ExistsUnique]
  use ∅
  constructor
  . rfl
  . intro y hy
    rw [hy]
    rfl

-- -----------------------------------------------------------------------------

-- Symmetrically, there is the universal set `Set.univ`:

example {α} : Set.univ (α := α) = {_a | True} := by rfl

-- It is characterized as the only set that contains every element:

-- **TODO:** Need to introduce extensionality earlier and the `ext` tactic.

example {α} {s : Set α} : s = Set.univ ↔ ∀ x, x ∈ s := by
  constructor
  . intro s_eq_univ x
    rw [s_eq_univ, Set.univ, Set.mem_setOf]
    trivial
  . intro h
    rw [Set.univ]
    ext x
    specialize h x
    simp only [h]
    simp only [Set.mem_setOf]

-- The official stuff that is declared (the modus ponens)
#check Set.mem_univ
-- Set.mem_univ.{u} {α : Type u} (x : α) : x ∈ Set.univ



-- ## `Singleton`, `Insert` and `{a, b, c}` notation

#check Set.singleton
-- Set.singleton.{u} {α : Type u} (a : α) : Set α

#print Set.singleton
-- protected def Set.singleton.{u} : {α : Type u} → α → Set α :=
-- fun {α} a => {b | b = a}

-- The notation that you should use for a singleton is `{x}`.

example {α} (x : α): {x} = (Set.singleton x) := by rfl

-- I was a bit suprised that the definition was not using the insertion into
-- and empty set but actually I am advised not to use this definition but
-- instead:

#check Set.singleton_def
-- Set.singleton_def.{u} {α : Type u} (a : α) : {a} = insert a ∅

-- ... so that kinda solves that. Let's say that how `Set.singleton` is defined
-- is an implementation detail.


#check Set.insert
-- Set.insert.{u} {α : Type u} (a : α) (s : Set α) : Set α

-- I am a bit baffled by the order of the arguments here, I guess that I
-- would rather have the set first and the item second. But not a big deal
-- I guess since I can use the uniform function call syntax (UFCS) to
-- have `s.insert a` and/or `|>.insert` to chain multiple inserts.
-- OTOH the current convention matches the `List.cons` approach...

#print Set.insert
-- protected def Set.insert.{u} : {α : Type u} → α → Set α → Set α :=
-- fun {α} a s => {b | b = a ∨ b ∈ s}

#check Set.insert_def
-- Set.insert_def.{u} {α : Type u} (x : α) (s : Set α) :
-- insert x s = {y | y = x ∨ y ∈ s}


example {α} (x : α) : {x} = Set.insert x {} := by
  simp only [Set.singleton_def]
  -- insert x ∅ = Set.insert x ∅
  rfl

-- That's actually similar to `Set.eq_of_mem_singleton` in Mathlib
example {α} (x y : α) : x ∈ ({y} : Set α) ↔ x = y := by
  simp only [
    Set.singleton_def,
    Set.insert_def,
    Set.mem_empty_iff_false,
    or_false,
    Set.mem_setOf
  ]

#check Set.eq_of_mem_singleton
-- Set.eq_of_mem_singleton.{u} {α : Type u} {x y : α} (h : x ∈ {y}) : x = y

example {α} (a : α) : {a, a} = ({a} : Set α) := by
  rw [Set.singleton_def]
  repeat rw [Set.insert_def]
  simp only [Set.mem_setOf, Set.mem_empty_iff_false, or_false, or_self]

example {α} (a b : α) : {a, b} = ({b, a} : Set α) := by
  simp only [Set.insert_def, Set.singleton_def]
  simp only [Set.mem_empty_iff_false, or_false, Set.mem_setOf]
  ext x; simp only [Set.mem_setOf]
  -- ⊢ x = a ∨ x = b ↔ x = b ∨ x = a
  simp only [or_comm]


-- ## Unary and Binary Operators

#check Set.compl_def
-- Set.compl_def.{u_1} {α : Type u_1} (s : Set α) : sᶜ = {x | x ∉ s}

#check Set.union_def
-- Set.union_def.{u} {α : Type u} {s₁ s₂ : Set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂}

#check Set.inter_def
-- Set.inter_def.{u} {α : Type u} {s₁ s₂ : Set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂}

#check Set.diff_eq
-- Set.diff_eq.{u} {α : Type u} (s t : Set α) : s \ t = s ∩ tᶜ

#check Set.symmDiff_def
-- Set.symmDiff_def.{u} {α : Type u} (s t : Set α) : symmDiff s t = s \ t ∪ t \ s

example {α} (s : Set α) : (sᶜ)ᶜ = s := by
  ext x
  simp only [Set.compl_def, Set.mem_setOf]
  simp only [not_not]

#check compl_compl
-- compl_compl.{u} {α : Type u} [BooleanAlgebra α] (x : α) : xᶜᶜ = x

example {α} : Set.univᶜ = (∅ : Set α) := by
  -- Note: univ is "public" in the Set type class, empty is not even there.
  simp only [Set.univ, Set.empty_def]
  rw [Set.compl_def]
  simp only [Set.mem_setOf, not_true]

#check Set.compl_univ
-- Set.compl_univ.{u_1} {α : Type u_1} : Set.univᶜ = ∅

example {α} : (∅ᶜ : Set α) = Set.univ := by
  simp only [Set.compl_def, Set.univ, Set.empty_def, Set.mem_setOf]
  simp only [not_false_iff]

#check Set.compl_empty
-- Set.compl_empty.{u_1} {α : Type u_1} : ∅ᶜ = Set.univ

example {α} (s t : Set α) : s ∪ t = t ∪ s := by
  simp only [Set.union_def]
  simp only [or_comm]

#check Set.union_comm
-- Set.union_comm.{u} {α : Type u} (a b : Set α) : a ∪ b = b ∪ a

example {α} {s t : Set α} : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  simp only [Set.union_def, Set.inter_def, Set.compl_def]
  ext x; simp only [Set.mem_setOf]
  -- ⊢ ¬(x ∈ s ∨ x ∈ t) ↔ x ∉ s ∧ x ∉ t
  simp only [not_or]

#check Set.compl_union
-- Set.compl_union.{u_1} {α : Type u_1} (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ

example {α} (r s t : Set α) : r ∪ (s ∩ t) = (r ∪ s) ∩ (r ∪ t) := by
  simp only [Set.union_def, Set.inter_def, Set.mem_setOf]
  ext x; simp only [Set.mem_setOf]
  -- ⊢ x ∈ r ∨ x ∈ s ∧ x ∈ t ↔ (x ∈ r ∨ x ∈ s) ∧ (x ∈ r ∨ x ∈ t)
  simp [or_and_left]

#check Set.union_inter_distrib_left
-- Set.union_inter_distrib_left.{u} {α : Type u} (s t u : Set α) :
-- s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u)

example {α} (r s t : Set α) : (r \ s) \ t = r \ (s ∪ t) := by
  simp only [Set.diff_eq, Set.inter_def, Set.compl_def, Set.union_def]
  simp only [Set.mem_setOf]
  ext x; simp only [Set.mem_setOf]
  simp_all only [not_or]
  simp only [and_assoc]

-- ## Inclusion and Power Set

#check Set.subset_def
-- Set.subset_def.{u} {α : Type u} {s t : Set α} : (s ⊆ t) = ∀ x ∈ s, x ∈ t

example {α} (r s : Set α) : r ⊆ r ∪ s := by
  simp only [Set.subset_def]
  intro x x_in_r
  simp only [Set.mem_union]
  left
  assumption

-- Power set 𝒫 : AFAICT, the set of all subsets ** of a set, not a type**.
-- So 𝒫 ℕ is meaningless, but 𝒫 (Set.univ (α := ℕ)) makes sense for example.

#check 𝒫  {n : ℕ | n < 100}
-- 𝒫 {n | n < 100} : Set (Set ℕ)

#print Set.powerset
-- def Set.powerset.{u} : {α : Type u} → Set α → Set (Set α) :=
-- fun {α} s => {t | t ⊆ s}

example {α} (r s : Set α): r ∈ 𝒫 s ↔ r ⊆ s  := by
  simp only [Set.powerset, Set.mem_setOf]

-- ## Union and Intersection of Collections/Families

#check Set.sUnion
-- Set.sUnion.{u} {α : Type u} (S : Set (Set α)) : Set α

-- Don't go the route of the definition of this stuff, this goes too abstract
-- (IMHO). Instead use the operational theorem:

#check Set.mem_sUnion
-- Set.mem_sUnion.{u} {α : Type u} {x : α} {S : Set (Set α)} :
-- x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t

example {α} : ⋃₀ (Set.univ : Set (Set α)) = (Set.univ : Set α) := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ]
  simp only [true_and, iff_true]
  use Set.univ
  simp only [Set.mem_univ]

#check Set.iUnion
-- Set.iUnion.{u, v} {α : Type u} {ι : Sort v} (s : ι → Set α) : Set α

#check Set.mem_iUnion
-- Set.mem_iUnion.{u, v} {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α} :
-- x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i

example {α} : ⋃ x : α, {x} = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ]
  simp only [iff_true]
  use y; simp only [Set.mem_singleton_iff]

example {ι} {α} (s : Set α) (t : ι → Set α) :
    s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  . intro h
    rw [Set.inter_def, Set.mem_setOf] at h
    have ⟨x_in_s, x_in_iUnion_t⟩ := h
    rw [Set.mem_iUnion] at x_in_iUnion_t
    have ⟨i, x_in_ti⟩ := x_in_iUnion_t
    use i
    rw [Set.inter_def, Set.mem_setOf]
    exact And.intro x_in_s x_in_ti
  . rintro ⟨i, x_in_s_inter_ti⟩

    rw [Set.inter_def, Set.mem_setOf, Set.mem_iUnion]
    constructor
    .
      admit
    . admit

-- ## Image and Preimage

#print Set.image -- notation: ''
-- def Set.image.{u, v} : {α : Type u} → {β : Type v} → (α → β) → Set α → Set β :=
-- fun {α} {β} f s => {x | ∃ a ∈ s, f a = x}

#check Set.mem_image
-- Set.mem_image.{u, v} {α : Type u} {β : Type v} (f : α → β) (s : Set α) (y : β) :
-- y ∈ f '' s ↔ ∃ x ∈ s, f x = y

#print Set.preimage -- notation: ⁻¹'
-- def Set.preimage.{u, v} : {α : Type u} → {β : Type v} → (α → β) → Set β → Set α :=
-- fun {α} {β} f s => {x | f x ∈ s}

#check Set.mem_preimage
-- Set.mem_preimage.{u, v} {α : Type u} {β : Type v} {f : α → β} {s : Set β} {a : α} :
-- a ∈ f ⁻¹' s ↔ f a ∈ s

def evenNumbers : Set ℕ := { n : ℕ | 2 ∣ n }

example : (2 * ·) '' Set.univ = evenNumbers := by
  simp only [Set.image, Set.mem_univ, true_and]
  simp only [evenNumbers, dvd_def, eq_comm]

example : {-1, 1} ⊆ (fun (x : ℝ) => x ^ 2) ⁻¹' {1} := by
  simp only [Set.preimage, Set.mem_singleton_iff]
  intro x
  rw [Set.mem_setOf]
  rintro (h₁ | h₂)
  . rw [h₁]
    norm_num
  . rw [h₂]
    norm_num

example : Real.exp ⁻¹' { x | x > 0 } = Set.univ := by
  ext x
  constructor
  . intro _
    simp only [Set.mem_univ]
  . intro x_real
    simp only [Set.mem_preimage, Set.mem_setOf]
    apply Real.exp_pos

-- **TODO.** Image/Preimage and unions/intersections of families of sets.

-- **TODO.** Injectivity, surjectivity, left and right inverse

-- -----------------------------------------------------------------------------

-- **TODO.** Finsets and stuff
-- **TODO.** coutable union and stuff (think σ-algebra axioms).
