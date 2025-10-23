/-
Sources:
  - https://en.wikipedia.org/wiki/Propositional_logic
  - https://leanprover-community.github.io/logic_and_proof/propositional_logic_in_lean.html
-/

#print True
-- inductive True : Prop
-- number of parameters: 0
-- constructors:
-- True.intro : True

#check True.intro
-- True.intro : True

#print trivial
-- theorem trivial : True :=
-- True.intro

#check trivial
-- trivial : True

#print Eq
-- inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
-- number of parameters: 2
-- constructors:
-- Eq.refl : ∀ {α : Sort u_1} (a : α), a = a

example : 0 = 0 := Eq.refl 0

#print And
-- structure And (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   And.left : a
--   And.right : b
-- constructor:
--   And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

example : True ∧ True :=
  And.intro trivial trivial

example : True ∧ True :=
  ⟨trivial, trivial⟩

example : True ∧ True ∧ True :=
  (And.intro trivial (And.intro trivial trivial))

example : True ∧ True ∧ True :=
  ⟨trivial, trivial, trivial⟩

example : 0 = 0 ∧ 1 = 1 := ⟨Eq.refl 0, Eq.refl 1 ⟩

#print Or
-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b

example : 0 = 0 ∨ 0 = 1 := Or.inl (Eq.refl 0)

example {p q : Prop} : p ∨ q -> q ∨ p :=
  fun p_or_q =>
    match p_or_q with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

-- Note: no "Imply", this is built-in with "->". We could define it with
def Imply (p q : Prop) : Prop :=
  p -> q

example {m n : Nat} : m = n -> m * m = n * n :=
  fun m_eq_n =>
    congrArg (fun p => p * p) m_eq_n

example {p q : Prop} : p ∧ q -> p ∨ q :=
  fun p_and_q =>
    Or.inl p_and_q.left -- or Or.inr p_and_q.right

example {p q : Prop} : p ∧ q -> (p -> q) :=
  fun p_and_q =>
    fun _ =>
      p_and_q.right

#print Iff
-- structure Iff (a b : Prop) : Prop
-- number of parameters: 2
-- fields:
--   Iff.mp : a → b
--   Iff.mpr : b → a
-- constructor:
--   Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b

example {p q : Prop} : (p <-> q) -> (p -> q) :=
  fun p_iff_q =>
    fun (hp : p) =>
      p_iff_q.mp hp

example {p q r : Prop} : ((p ∧ q)) -> r <-> (p -> q -> r) :=
  Iff.intro
    (fun hp_and_q_to_r =>
      fun hp hq =>
        hp_and_q_to_r (And.intro hp hq)
    )
    (fun hp_to_q_to_r =>
      fun hp_and_q =>
        have hp := hp_and_q.1
        have hq := hp_and_q.2
        hp_to_q_to_r hp hq
    )

example {p q r : Prop} : (p ∧ q) -> r <-> (p -> q -> r) := by
  apply Iff.intro
  . intro h
    intro hp
    intro hq
    have hp_and_q := And.intro hp hq
    exact h hp_and_q
  . intro h
    intro hp_and_q
    apply h
    . exact hp_and_q.1
    . exact hp_and_q.2



example {p q r : Prop} : p ∨ (q ∧ r) <-> (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    fun p_or_q_and_r =>
      match p_or_q_and_r with
      | Or.inl hp => And.intro (Or.inl hp) (Or.inl hp)
      | Or.inr hq_and_r => And.intro (Or.inr hq_and_r.left) (Or.inr hq_and_r.right)
    fun p_or_q_and_p_or_r =>
      have ⟨p_or_q, p_or_r⟩ := p_or_q_and_p_or_r
      match p_or_q with
      | Or.inl hp => Or.inl hp
      | Or.inr hq =>
        match p_or_r with
        | Or.inl hp' => Or.inl hp'
        | Or.inr hr => Or.inr (And.intro hq hr)

example {p q r : Prop} : p ∨ (q ∧ r) <-> (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro hp_or_q_and_r
    cases hp_or_q_and_r with
    | inl hp =>
      apply And.intro
      . exact Or.inl hp
      . exact Or.inl hp
    | inr hq_and_r =>
      have ⟨hq, hr⟩ := hq_and_r
      apply And.intro
      . exact Or.inr hq
      . exact Or.inr hr
  . sorry -- TODO


#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:

example : False -> 0 = 1 :=
  fun f =>
    False.elim (C := 0 = 1) f

example : False -> 0 = 1 :=
  fun f =>
    nomatch f

#print Not
-- def Not : Prop → Prop :=
-- fun a => a → False

example {p : Prop} : p -> ¬¬p :=
  fun hp =>
    fun not_hp =>
      not_hp hp

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

example {p : Prop} : ¬¬p -> p :=
  match (Classical.em p) with
  | Or.inl hp => fun _ => hp
  | Or.inr hnot_p =>
      fun hnot_not_p =>
        have false := hnot_not_p hnot_p
        false.elim

example : 0 ≠ 1 := -- same as ¬ (0 = 1), same as 0 = 1 -> False
  fun zero_eq_one =>
    nomatch zero_eq_one

theorem de_morgan_2 {p q : Prop} : ¬ (p ∨ q) -> ¬ p ∧ ¬ q :=
  fun not_p_or_q =>
    And.intro
      (fun hp => not_p_or_q (Or.inl hp))
      (fun hq => not_p_or_q (Or.inr hq))

/-
Same theorem, proven with tactics
-/
theorem de_morgan_2' {p q : Prop} : ¬ (p ∨ q) -> ¬ p ∧ ¬ q := by
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

theorem de_morgan_1 {p q : Prop} : ¬ p ∧ ¬ q -> ¬ (p ∨ q)  := by
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

theorem modus_ponens (hp : p) (hpq : p -> q) : q :=
  hpq hp

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
