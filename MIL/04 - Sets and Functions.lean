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


-- -----------------------------------------------------------------------------

-- Insert stuff and {a, b, c} notation

def singleton_one : Set ℕ := {1}
-- Set.mem_insert.{u} {α : Type u} (x : α) (s : Set α) : x ∈ insert x s


#check Set.insert_def
-- Set.insert_def.{u} {α : Type u} (x : α) (s : Set α) : insert x s = {y | y = x ∨ y ∈ s}

#check Set.mem_insert
-- Set.mem_insert.{u} {α : Type u} (x : α) (s : Set α) : x ∈ insert x s

example (m n : ℕ) : m ∈ ({n} : Set ℕ) ↔ m = n := by
  simp only [Set.insert_def]
  admit



def zot : Set ℕ := {0, 1, 2}

def large : Set ℕ := { n : ℕ | n ≥ 1000 }

def allN : Set ℕ := Set.univ

-- -----------------------------------------------------------------------------
