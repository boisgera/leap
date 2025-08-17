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

theorem hypothetical_syllogism₃ (hpqr : (p -> q) ∧ (q -> r)) : p -> r :=
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
  sorry

theorem destructive_dilemma (hpqrs : (p -> q) ∧ (r -> s) ∧ (¬q ∨ ¬s)) : ¬p ∨ ¬r :=
  sorry

theorem bidirectional_dilemma (hpqrs :(p -> q) ∧ (r -> s) ∧ (p -> ¬s)) : q ∨ ¬r :=
  sorry

theorem simplification (hpq : (p ∨ q) ∧ ¬q) : p :=
  sorry

theorem conjunction (hp : p) (hq : q) : p ∧ q :=
  sorry

theorem addition (hp : p) : p ∨ q :=
  sorry

theorem composition_of_conjuction (hpqr: (p -> q) ∧ (p -> r)) : p -> (q ∧ r) :=
  sorry

theorem composition_of_disjunction (hpqr: (p -> q) ∨ (p -> r)) : p -> (q ∨ r) :=
  sorry

-- TODO: to be continued
