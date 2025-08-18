/-
Sources:
  - https://en.wikipedia.org/wiki/Propositional_logic
  - https://leanprover-community.github.io/logic_and_proof/propositional_logic_in_lean.html
-/

variable {p q r s: Prop}

theorem modus_ponens (hp : p) (hpq : p -> q) : q :=
  hpq hp

#print Not
-- def Not : Prop → Prop :=
-- fun a => a → False

#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:

theorem modus_tollens (hpq : p -> q) (hq : ¬q) : ¬p :=
  fun hp => hq (hpq hp)

theorem modus_tollens₁ (hpq : p -> q) (hq : ¬q) : ¬p :=
  fun hp => hp |> hpq |> hq

theorem modus_tollens₂ (hpq : p -> q) (hq : ¬q) : ¬p :=
  hq ∘ hpq

theorem modus_tollens₃ (hpq : p -> q) (hq : ¬q) : ¬p :=
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

theorem hypothetical_syllogism (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
  (And.right hpqr) ∘ (And.left hpqr)

theorem hypothetical_syllogism₁ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
  hpqr.right ∘ hpqr.left

theorem hypothetical_syllogism₂ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
  hpqr.2 ∘ hpqr.1

-- Structure destructuring
theorem hypothetical_syllogism₃ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
  have {left := hpq, right := hqr} := hpqr
  hqr ∘ hpq

-- Probably not a great idea here, but it works
theorem hypothetical_syllogism₄ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
  -- Shortcut for: have {left := left, right := right} := hpqr
  have {left, right} := hpqr
  right ∘ left

-- Unique constructor, dependant pair destructuring works
theorem hypothetical_syllogism₅ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
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

theorem constructive_dilemma (hpqr : (p -> q) ∧ (r -> s) ∧ (p ∨ r)) : q ∨ s :=
  have ⟨hpq, hrs, hpr⟩ := hpqr
  match hpr with
  | Or.inl hp => Or.inl (hpq hp)
  | Or.inr hr => Or.inr (hrs hr)

theorem destructive_dilemma (hpqrs : (p -> q) ∧ (r -> s) ∧ (¬q ∨ ¬s)) : ¬p ∨ ¬r :=
  have ⟨hpq, hrs, hqs⟩ := hpqrs
  match hqs with
  | Or.inl hnq => Or.inl (hnq ∘ hpq)
  | Or.inr hns => Or.inr (hns ∘ hrs)

theorem bidirectional_dilemma (hpqrs :(p -> q) ∧ (r -> s) ∧ (p ∨ ¬s)) : q ∨ ¬r :=
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

theorem composition_of_conjuction (hpqr: (p -> q) ∧ (p -> r)) : p -> (q ∧ r) :=
  let ⟨hpq, hpr⟩ := hpqr
  fun hp => And.intro (hpq hp) (hpr hp)

theorem composition_of_disjunction (hpqr: (p -> q) ∨ (p -> r)) : p -> (q ∨ r) :=
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

theorem de_morgan_theorem_1 : ¬(p ∨ q) <-> ¬p ∧ ¬q :=
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
theorem de_morgan_theorem_1₁ : ¬(p ∨ q) <-> ¬p ∧ ¬q :=
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
theorem de_morgan_theorem_1₂ : ¬(p ∨ q) <-> ¬p ∧ ¬q :=
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
