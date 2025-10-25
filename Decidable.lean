import Mathlib

inductive TheAnswerIs : Nat -> Prop where
| intro : TheAnswerIs 42

/--
error: failed to synthesize
  Decidable (TheAnswerIs 0)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Decidable (TheAnswerIs 0)

-- instance (n : Nat) : Decidable (TheAnswerIs n) :=
--   if h : 42 = n then
--     isTrue (cast (congrArg TheAnswerIs h) TheAnswerIs.intro)
--   else
--     have k : ¬TheAnswerIs n := by
--       intro answer
--       match answer with
--       | TheAnswerIs.intro => simp at h
--     isFalse k

-- Simpler derivation of the instance
theorem theAnswerIs_iff_eq_42 {n : Nat} : TheAnswerIs n <-> n = 42 := by
  constructor
  . intro answer
    match answer with
    | TheAnswerIs.intro => rfl
  . intro h
    rw [h]
    exact TheAnswerIs.intro

#print theAnswerIs_iff_eq_42
-- theorem theAnswerIs_iff_eq_42 : ∀ {n : ℕ}, TheAnswerIs n ↔ n = 42 :=
-- fun {n} =>
--   {
--     mp := fun answer =>
--       match n, answer with
--       | .(42), TheAnswerIs.intro => Eq.refl 42,
--     mpr := fun h => Eq.mpr (id (congrArg (fun _a => TheAnswerIs _a) h)) TheAnswerIs.intro }

/-
There is already a standard way to pull over, see below.
-/

-- instance (n : Nat) : Decidable (TheAnswerIs n) :=
--   match decEq n 42 with
--   | Decidable.isFalse h => isFalse ((Iff.not theAnswerIs_iff_eq_42).mpr h)
--   | Decidable.isTrue h => isTrue (theAnswerIs_iff_eq_42.mpr h)

#check decidable_of_decidable_of_iff
-- decidable_of_decidable_of_iff {p q : Prop} [Decidable p] (h : p ↔ q) : Decidable q

instance (n : Nat) : Decidable (TheAnswerIs n) :=
  decidable_of_decidable_of_iff theAnswerIs_iff_eq_42.symm

#synth Decidable (TheAnswerIs 0)

#synth Decidable (TheAnswerIs 42)

#eval decide (TheAnswerIs 0)
-- false

#eval decide (TheAnswerIs 42)
-- true

/-
The code golf version by Kenny Lau <https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Decidable.20instance/with/546995270>
-/

namespace Golf

inductive TheAnswerIs : Nat → Prop where
  | intro : TheAnswerIs 42

theorem theAnswerIs_iff_eq_42 {n : Nat} : TheAnswerIs n ↔ n = 42 :=
  ⟨fun ⟨⟩ => rfl, (· ▸ ⟨⟩)⟩

instance (n : Nat) : Decidable (TheAnswerIs n) :=
  decidable_of_decidable_of_iff theAnswerIs_iff_eq_42.symm

end Golf
