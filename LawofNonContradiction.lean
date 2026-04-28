
/-!
The Law of Excluded Middle (LEM) requires classical logic.
-/

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

/-!
But the related Law of Non Contraction (LNC) does not.
Constructive logic is enough!


A step-by-step tactical proof:

-/

example : ∀ (p : Prop), ¬(p ∧ ¬ p) := by
  intro p
  rw [Not]
  intro hpnp
  let ⟨hp, hnp⟩ := hpnp
  rw [Not] at hnp
  apply hnp
  exact hp

/-!
A variant, code golfed:
-/

example : ∀ (p : Prop), ¬(p ∧ ¬ p) := by
  intro p ⟨hp, hnp⟩ -- Note: p is never used afterwards
  apply hnp
  exact hp

/-!
At this stage we have actually discovered the structure of the proof term and we
don't actually need a tactical proof anymore:
-/

example : ∀ (p : Prop), ¬(p ∧ ¬ p) :=
  fun _ ⟨hp, hnp⟩ => hnp hp
