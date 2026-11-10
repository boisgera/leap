/-
Sources:
  - https://en.wikipedia.org/wiki/Propositional_logic
  - https://leanprover-community.github.io/logic_and_proof/propositional_logic_in_lean.html
-/


/-!
In Lean, propositions behave very similarly to types.
A term of a given proposition (sometimes called a witness) represents
a proof of the proposition.
-/

/-!

True and False
--------------------------------------------------------------------------------

The `True` proposition is defined as:

```lean4
inductive True : Prop where
  | intro : True
```
-/

#print True
-- inductive True : Prop
-- number of parameters: 0
-- constructors:
-- True.intro : True

/-!
It's exceedingly easy to prove the proposition, with the proof `True.intro`.

-/

#check (True.intro : True)
-- True.intro : True

/-!
Lean even has a theorem named after this result: it's `trivial`:
-/

#print trivial
-- theorem trivial : True :=
-- True.intro

/-!
So if instead of the low-level proof you want to use the theorem, be my guest!
-/

#check (trivial : True)
-- trivial : True

/-!
The `False` proposition is even simpler:

```lean4
inductive False : Prop
```

-/

#print False
/-
inductive False : Prop
number of parameters: 0
constructors:
-/

/-!
It has no constructor! So good luck to you to prove that `False` holds!
-/


/-!
`And` and `Or`
--------------------------------------------------------------------------------

The conjunction operator `∧` is the notation for `And`:
-/

#print And
-- structure And (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   And.left : a
--   And.right : b
-- constructor:
--   And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

/-!
Now we can start proving our own theorems. For example, we can prove
that `True ∧ True` (that is `And True True`) holds. To do that we
have to provide a term of type `And True True`. We don't have much of
a choice here since `And` has a single constructor named `intro`;
to make a term in `And a b`, we have to provide a term of type
`a` and a term of type `b`. Here, since `a = b = True`, we can
use `True.intro`:

-/

theorem true_and_true : True ∧ True :=
  And.intro True.intro True.intro

/-!
If we don't feel like giving a name to a theorem, we can use the keyword
`example` instead:
-/

example : True ∧ True :=
  And.intro True.intro True.intro

/-!
We can have a more general version of this theorem, applied not merely to
`True` but to any proposition `p` that has a proof:
-/

theorem and_self_of_self {p : Prop} (hp : p) : p ∧ p :=
  And.intro hp hp

/-!
We can rederive our earlier result as a special case:
-/

example : True ∧ True := and_self_of_self True.intro

/-!
Note that anything that produces a term of type `Prop` is de factor a
theorem. Despite being given a constructor without the keyword
`theorem` or `example`, `And.intro` or `True.intro` are theorem:
given assumptions (optionally), they produce the proofs of propositions.
-/

/-!
The disjuction operator `∨` represents the `Or` type:
-/

#print Or
-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b

/-!
There is exactly to possible ways to prove `a ∨ b`: either you have a proof
`ha` of `a` and then you can use the first constructor `Or.inl` ("intro left")
or you have a proof `hb` of `b` and then you can use the second constructor
`Or.inr` ("intro right").

For example:
-/

example : True ∨ True :=
  Or.inl True.intro -- here Or.inr True.intro would also work.

example : False ∨ True :=
  Or.inr True.intro

/-!
Implication
--------------------------------------------------------------------------------

There is no new operator to denote implication in Lean: the operator `→` used
in function type is used, with actually the same meaning. Think about it for
a moment: with this notation a proof `p → q` is a function from `p` to `q`,
that is a function that given any proof of `p` can produce a proof of `q`.
This is exactly the meaning that we want!
-/

example {p : Prop} : p → p := fun hp => hp -- the identity is a proof!

example {p q : Prop} : p → p ∨ q := fun hp => Or.inl hp

example {p q : Prop} : p ∨ q → q ∨ p :=
  fun p_or_q =>
    match p_or_q with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

example {p q : Prop} : p ∧ q → p ∨ q :=
  fun p_and_q =>
    Or.inl p_and_q.left -- or Or.inr p_and_q.right

example {p q : Prop} : p ∧ q → (p → q) :=
  fun p_and_q =>
    fun _ =>
      p_and_q.right

/-!
When we feel the need, we can use local variables with `have`
(we could have used `let`, but `have` is more appropriate for `Prop` terms
since it forgets the value of you term and remember only its existence.)
-/

theorem exportation {p q r : Prop} : (p ∧ q → r) → (p → q → r) :=
  fun f =>
    fun hp hq =>
      have hp_and_hq := And.intro hp hq
      f hp_and_hq

theorem importation {p q r : Prop} : (p → q → r) → (p ∧ q → r) :=
  fun hr_of_hq_of_hp =>
    fun hp_and_hq =>
      have hp := And.left hp_and_hq
      have hq := And.right hp_and_hq
      hr_of_hq_of_hp hp hq

/-!
Note that since we need all fields of the term `hp_and_hq` in
`importation` we could have done some pattern matching instead:
-/

example {p q r : Prop} : (p → q → r) → (p ∧ q → r) :=
  fun hr_of_hq_of_hp =>
    fun hp_and_hq =>
      match hp_and_hq with
      | And.intro hp hq => hr_of_hq_of_hp hp hq

/-!
But since `And` is structure, with a single constructor,
a term of this type can be build from the constructor arguments,
or here decomposed into these arguments,
using the anonymous constructor `⟨⟩` notation.
-/

example {p q r : Prop} : (p → q → r) → (p ∧ q → r) :=
  fun hr_of_hq_of_hp =>
    fun hp_and_hq =>
      have ⟨hp, hq⟩ := hp_and_hq
      hr_of_hq_of_hp hp hq

/-!
Equivalence is denoted by the `↔` operator and corresponds to the following
`Prop`:
-/

#print Iff
-- structure Iff (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   Iff.mp : a → b
--   Iff.mpr : b → a
-- constructor:
--   Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b

/-!
To prove `p ↔ q` you need to provide a proof of `p → q` (the *modus ponens*)
and a proof of `q → p` (the reverse modus ponens).
-/

example {p q r : Prop} : (p → q → r) ↔ (p ∧ q → r) :=
  Iff.intro importation exportation

/-!
You can also prove
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    fun hp_or_hq_and_hr =>
      match hp_or_hq_and_hr with
      | Or.inl hp =>
        And.intro (Or.inl hp) (Or.inl hp)
      | Or.inr hq_and_r =>
        And.intro (Or.inr hq_and_r.left) (Or.inr hq_and_r.right)
    fun hp_or_hq_and_hp_or_hr =>
      have ⟨hp_or_hq, hp_or_hr⟩ := hp_or_hq_and_hp_or_hr
      match hp_or_hq with
      | Or.inl hp => Or.inl hp
      | Or.inr hq =>
        match hp_or_hr with
        | Or.inl hp => Or.inl hp
        | Or.inr hr => Or.inr (And.intro hq hr)

/-!
Using the anonymous constructor notation to destructure but also to build,
have the slightly terser:
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    fun hp_or_hq_and_hr =>
      match hp_or_hq_and_hr with
      | Or.inl hp => ⟨Or.inl hp, Or.inl hp⟩
      | Or.inr hq_and_r => ⟨Or.inr hq_and_r.left, Or.inr hq_and_r.right⟩
    fun hp_or_hq_and_hp_or_hr =>
      have ⟨hp_or_hq, hp_or_hr⟩ := hp_or_hq_and_hp_or_hr
      match hp_or_hq with
      | Or.inl hp => Or.inl hp
      | Or.inr hq =>
        match hp_or_hr with
        | Or.inl hp => Or.inl hp
        | Or.inr hr => Or.inr ⟨hq, hr⟩

/-!
But it's probably becoming slightly painful at this stage.
It's probably the good moment to introduce tactics, enable with the
`by` keyword. We can make a very partial sketch of our proof like that:
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry

/-!
If you position your cursor just before the `sorry`, you will get the state
of the proof in the infoview, with the list of assumptions and the goal.
Here, we see

```
p q r : Prop
⊢ p ∨ q ∧ r ↔ (p ∨ q) ∧ (p ∨ r)
```

Our assumption is that `p`, `q` and `r` are (any) propositions and we need
to prove `p ∨ q ∧ r ↔ (p ∨ q) ∧ (p ∨ r)`.

-/

/-!
If you happen to have a term of the goal term, your proof is over: just
use the tactic `exact` followed by this term:
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  exact Iff.intro
    fun hp_or_hq_and_hr =>
      match hp_or_hq_and_hr with
      | Or.inl hp => ⟨Or.inl hp, Or.inl hp⟩
      | Or.inr hq_and_r => ⟨Or.inr hq_and_r.left, Or.inr hq_and_r.right⟩
    fun hp_or_hq_and_hp_or_hr =>
      have ⟨hp_or_hq, hp_or_hr⟩ := hp_or_hq_and_hp_or_hr
      match hp_or_hq with
      | Or.inl hp => Or.inl hp
      | Or.inr hq =>
        match hp_or_hr with
        | Or.inl hp => Or.inl hp
        | Or.inr hr => Or.inr ⟨hq, hr⟩


/-!
Yes, this is not very useful here... Note how `exact` is somehow the "inverse"
of the `by` keyword, much like `return` is the inverse of `do`.
-/

/-!
Now since our final goal has the structure `a ↔ b`,
we know that there is a unique way to conclude the proof once we have
found proofs of `a` and `b`: apply the theorem `Iff.intro` to these proofs!
Since we know that it's how we are going to conclude, we ask Lean to reduce
the current proof to the proof of two subgoals.

-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · sorry
  · sorry

/-!
Now the first `sorry` is associated to the proof

```lean4
p q r : Prop
⊢ p ∨ q ∧ r → (p ∨ q) ∧ (p ∨ r)
```

and the second one to:

```lean4
p q r : Prop
⊢ (p ∨ q) ∧ (p ∨ r) → p ∨ q ∧ r
```
-/

/-
Since here `Iff.intro` was actually the unique constructor of a known type,
we could even have used instead:
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · sorry
  · sorry

/-!
Now in the first subproof that we have to perform the goal is a function.
We can transfer its input argument into our assumptions with `intro`
followed by the name that we want to give the assumption.
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hp_or_hq
    sorry
  · sorry

/-!
The state of the first subgoal now is:

```lean4
p q r : Prop
hp_or_hp_or_hq : p ∨ q ∧ r
⊢ (p ∨ q) ∧ (p ∨ r)
```

Since the goal is a `And` which has a unique constructor, we can use the same
trick as before:

-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hp_or_hq
    apply And.intro
    · sorry
    · sorry
  · sorry

/-!

The new subproofs are:

```lean4
p q r : Prop
hp_or_hp_or_hq : p ∨ q ∧ r
⊢ p ∨ q
```

and

```
p q r : Prop
hp_or_hp_or_hq : p ∨ q ∧ r
⊢ p ∨ r
```

In both case we could do some pattern matching on the `Or` terms with `match`
but in this context we can also use the (very similar) `cases` tactic:

-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hq_and_hr
    apply And.intro
    · cases hp_or_hq_and_hr with
      | inl hp => sorry
      | inr hq_and_hr => sorry
    · cases hp_or_hq_and_hr with
      | inl hp => sorry
      | inr hq_and_hr => sorry
  · sorry

/-
Consider the first 4 subproofs:

```lean4
p q r : Prop
hp : p
⊢ p ∨ q
```

```lean4
p q r : Prop
hp_and_hq : q ∧ r
⊢ p ∨ q
```

```lean4
p q r : Prop
hp : p
⊢ p ∨ r
```

```lean4
p q r : Prop
hp_and_hq : q ∧ r
⊢ p ∨ r
```

In each case it's now pretty easy to build an explicit term of the required
type. That would lead to:

-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hq_and_hr
    apply And.intro
    · cases hp_or_hq_and_hr with
      | inl hp => exact Or.inl hp
      | inr hq_and_hr =>
        have hq := hq_and_hr.left
        exact Or.inr hq
    · cases hp_or_hq_and_hr with
      | inl hp => exact Or.inl hp
      | inr hq_and_hr =>
        have hr := hq_and_hr.right
        exact Or.inr hr
  · sorry

/-!
We can also keep on in tactical mode right up to the moment where the desired
goals is in the assumption and even conclude with tactic `assumption` instead
of `exact` if we don't want to name the precise assumption.
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hq_and_hr
    apply And.intro
    · cases hp_or_hq_and_hr with
      | inl hp =>
        apply Or.inl
        assumption
      | inr hq_and_hr =>
        apply Or.inr
        have hq := hq_and_hr.left
        assumption
    · cases hp_or_hq_and_hr with
      | inl hp =>
        apply Or.inl
        assumption
      | inr hq_and_hr =>
        apply Or.inr
        have hr := hq_and_hr.right
        assumption
  · sorry

/-!
The proof of the final subgoals is also interesting since its conclusion is
an `Or`, but we don't know beforehand if the term is going to be introduced
by the left or the right constructor, so we can't apply for example `Or.inl`
from the get go; we need to consider the two possible constructors
that can lead to a proof of `p ∨ q` for example. If we have a proof of
`p` it's easy to conclude, otherwise we note that we have a proof of `q`
and perform a similar analysis on the proof of `p ∨ r`.
-/

example {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_or_hq_and_hr
    apply And.intro
    · cases hp_or_hq_and_hr with
      | inl hp =>
        apply Or.inl
        assumption
      | inr hq_and_hr =>
        apply Or.inr
        have hq := hq_and_hr.left
        assumption
    · cases hp_or_hq_and_hr with
      | inl hp =>
        apply Or.inl
        assumption
      | inr hq_and_hr =>
        apply Or.inr
        have hr := hq_and_hr.right
        assumption
  · intro hp_or_hq_and_hp_or_hr
    have ⟨hp_or_hq, hp_or_hr⟩ := hp_or_hq_and_hp_or_hr
    clear hp_or_hq_and_hp_or_hr
    cases hp_or_hq with
    | inl hp =>
      apply Or.inl
      assumption
    | inr hq =>
      cases hp_or_hr with
      | inl hp =>
        apply Or.inl
        assumption
      | inr hr =>
        apply Or.inr
        constructor
        · assumption
        · assumption

/-!
`False` and negation.
--------------------------------------------------------------------------------

TODO:
  - explosion
  - negation
  - some theorems with not
  - what limits us, non-constructive axioms, em
-/

#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:

example : False → 0 = 1 :=
  fun f =>
    False.elim (C := 0 = 1) f

example : False → 0 = 1 :=
  fun f =>
    nomatch f

#print Not
-- def Not : Prop → Prop :=
-- fun a => a → False

example {p : Prop} : p → ¬¬p :=
  fun hp =>
    fun not_hp =>
      not_hp hp

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

example {p : Prop} : ¬¬p → p :=
  match (Classical.em p) with
  | Or.inl hp => fun _ => hp
  | Or.inr hnot_p =>
      fun hnot_not_p =>
        have false := hnot_not_p hnot_p
        false.elim

example : 0 ≠ 1 := -- same as ¬ (0 = 1), same as 0 = 1 → False
  fun zero_eq_one =>
    nomatch zero_eq_one

theorem de_morgan_2 {p q : Prop} : ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  fun not_p_or_q =>
    And.intro
      (fun hp => not_p_or_q (Or.inl hp))
      (fun hq => not_p_or_q (Or.inr hq))

/-
Same theorem, proven with tactics
-/
theorem de_morgan_2' {p q : Prop} : ¬ (p ∨ q) → ¬ p ∧ ¬ q := by
  intro not_p_or_q
  apply And.intro
  . rw [Not] at *
    intro hp
    apply not_p_or_q
    apply Or.inl
    exact hp
  . rw [Not] at *
    intro hq
    apply not_p_or_q
    apply Or.inr
    exact hq

theorem de_morgan_1 {p q : Prop} : ¬ p ∧ ¬ q → ¬ (p ∨ q)  := by
  intro not_p_and_not_q
  have not_p := not_p_and_not_q.1
  have not_q := not_p_and_not_q.2
  have p_or_not_p := Classical.em p
  cases p_or_not_p with
  | inl hp =>
    have false := not_p hp
    apply false.elim
  | inr hnot_p =>
    repeat rw [Not] at *
    intro hp_or_q
    cases hp_or_q with
    | inl hp => exact not_p hp
    | inr hq => exact not_q hq

#print de_morgan_1



/------------------------------------------------------------------------------/

variable {p q r s: Prop}

theorem modus_ponens (hp : p) (hpq : p → q) : q :=
  hpq hp

theorem modus_tollens (hpq : p → q) (hq : ¬q) : ¬p :=
  fun hp => hq (hpq hp)

theorem modus_tollens₁ (hpq : p → q) (hq : ¬q) : ¬p :=
  fun hp => hp |> hpq |> hq

theorem modus_tollens₂ (hpq : p → q) (hq : ¬q) : ¬p :=
  hq ∘ hpq

theorem modus_tollens₃ (hpq : p → q) (hq : ¬q) : ¬p :=
  (· |> hpq |> hq)

#print And
-- structure And (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   And.left : a
--   And.right : b
-- constructor:
--   And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

#check And.elim
-- And.elim.{u_1} {a b : Prop} {α : Sort u_1} (f : a → b → α) (h : a ∧ b) : α

theorem hypothetical_syllogism (hpqr : (p → q) ∧ (q → r)) : p → r :=
  (And.right hpqr) ∘ (And.left hpqr)

theorem hypothetical_syllogism₁ (hpqr : (p → q) ∧ (q → r)) : p → r :=
  hpqr.right ∘ hpqr.left

theorem hypothetical_syllogism₂ (hpqr : (p → q) ∧ (q → r)) : p → r :=
  hpqr.2 ∘ hpqr.1

-- Structure destructuring
theorem hypothetical_syllogism₃ (hpqr : (p → q) ∧ (q → r)) : p → r :=
  have {left := hpq, right := hqr} := hpqr
  hqr ∘ hpq

-- Probably not a great idea here, but it works
theorem hypothetical_syllogism₄ (hpqr : (p → q) ∧ (q → r)) : p → r :=
  -- Shortcut for: have {left := left, right := right} := hpqr
  have {left, right} := hpqr
  right ∘ left

-- Unique constructor, dependant pair destructuring works
theorem hypothetical_syllogism₅ (hpqr : (p → q) ∧ (q → r)) : p → r :=
  have ⟨hpq, hqr⟩ := hpqr
  hqr ∘ hpq

#check False.elim
-- False.elim.{u} {C : Sort u} (h : False) : C

#print False.elim
-- def False.elim.{u} : {C : Sort u} → False → C :=
-- fun {C} h => False.rec (fun x => C) h
--
-- About recursors: <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#recursors>

def explosion (hq_and_nq : q ∧ ¬q) : p :=
  have ⟨hq, hnq⟩ := hq_and_nq
  have false : False := hnq hq
  False.elim false

-- "nomatch": See https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/#Lean___Parser___Term___nomatch
def explosion₁ (hq_and_nq : q ∧ ¬q) : p :=
  have ⟨hq, hnq⟩ := hq_and_nq
  have false : False := hnq hq
  nomatch false

#print Or
-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b

theorem disjunctive_syllogism (h : (p ∨ q) ∧ ¬q) : p :=
  have ⟨hpq, hnq⟩ := h
  match hpq with
  | Or.inl hp => hp
  | Or.inr hq => explosion (And.intro hq hnq)

theorem disjunctive_syllogism₁ (h : (p ∨ q) ∧ ¬q) : p :=
  have ⟨hpq, hnq⟩ := h
  match hpq with
  | Or.inl hp => hp
  | Or.inr hq => explosion ⟨hq, hnq⟩

#print Or.elim
-- theorem Or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c :=
-- fun {a b c} h left right =>
--   match h with
--   | Or.inl h => left h
--   | Or.inr h => right h

theorem disjunctive_syllogism₂ (h : (p ∨ q) ∧ ¬q) : p :=
  have ⟨hpq, hnq⟩ := h
  Or.elim hpq (.) (explosion ⟨·, hnq⟩)

theorem constructive_dilemma (hpqr : (p → q) ∧ (r → s) ∧ (p ∨ r)) : q ∨ s :=
  have ⟨hpq, hrs, hpr⟩ := hpqr
  match hpr with
  | Or.inl hp => Or.inl (hpq hp)
  | Or.inr hr => Or.inr (hrs hr)

theorem destructive_dilemma (hpqrs : (p → q) ∧ (r → s) ∧ (¬q ∨ ¬s)) : ¬p ∨ ¬r :=
  have ⟨hpq, hrs, hqs⟩ := hpqrs
  match hqs with
  | Or.inl hnq => Or.inl (hnq ∘ hpq)
  | Or.inr hns => Or.inr (hns ∘ hrs)

theorem bidirectional_dilemma (hpqrs :(p → q) ∧ (r → s) ∧ (p ∨ ¬s)) : q ∨ ¬r :=
  have ⟨hpq, hrs, hps⟩ := hpqrs
  match hps with
  | Or.inl hp => Or.inl (hpq hp)
  | Or.inr hns => Or.inr (hns ∘ hrs)

theorem simplification (hpq : (p ∨ q) ∧ ¬q) : p :=
  have ⟨hpq, hnq⟩ := hpq
  match hpq with
  | Or.inl hp => hp
  | Or.inr hq => explosion (And.intro hq hnq)

theorem conjunction (hp : p) (hq : q) : p ∧ q :=
  And.intro hp hq

theorem addition (hp : p) : p ∨ q :=
  Or.inl hp

theorem composition_of_conjuction (hpqr: (p → q) ∧ (p → r)) : p → (q ∧ r) :=
  let ⟨hpq, hpr⟩ := hpqr
  fun hp => And.intro (hpq hp) (hpr hp)

theorem composition_of_disjunction (hpqr: (p → q) ∨ (p → r)) : p → (q ∨ r) :=
  match hpqr with
  | Or.inl hpq => fun hp => Or.inl (hpq hp)
  | Or.inr hpr => fun hp => Or.inr (hpr hp)

#check Iff
-- ⊢ Prop → Prop → Prop

#print Iff
-- structure Iff (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   Iff.mp : a → b
--   Iff.mpr : b → a
-- constructor:
--   Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b

theorem de_morgan_theorem_1 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun not_p_or_q =>
      And.intro
       (fun hp => not_p_or_q (Or.inl hp))
       (fun hq => not_p_or_q (Or.inr hq))
    )
    (fun h_not_p_and_not_q =>
      have ⟨h_not_p, h_not_q⟩ := h_not_p_and_not_q
      (fun h_p_or_q =>
        match h_p_or_q with
        | Or.inl hp => h_not_p hp
        | Or.inr hq => h_not_q hq
      )
    )

-- Let's code golf a little ...
theorem de_morgan_theorem_1₁ : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    fun not_p_or_q => ⟨
       fun hp => not_p_or_q (Or.inl hp),
       fun hq => not_p_or_q (Or.inr hq)
    ⟩,
    fun ⟨h_not_p, h_not_q⟩ =>
      fun
      | Or.inl hp => h_not_p hp
      | Or.inr hq => h_not_q hq
  ⟩

-- Split the result in two prior (local) theorems and use this to have
-- the "fun" keyword disappear into the context if we want ; however
-- if we do that for the converse instance we cannot destructure the
-- argument.
theorem de_morgan_theorem_1₂ : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have h₁ (not_p_or_q : ¬(p ∨ q)) : ¬p ∧ ¬q := ⟨
    fun hp => not_p_or_q (Or.inl hp),
    fun hq => not_p_or_q (Or.inr hq)
  ⟩
  have h₂ : ¬p ∧ ¬q → ¬(p ∨ q) := fun ⟨h_not_p, h_not_q⟩ =>
    fun
    | Or.inl hp => h_not_p hp
    | Or.inr hq => h_not_q hq
  ⟨h₁, h₂⟩




/-

de_morgan_theorem_2

commutation_1

commutation_2

commutation_3

-/
