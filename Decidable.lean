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

instance (n : Nat) : Decidable (TheAnswerIs n) :=
  if h : 42 = n then
    isTrue (cast (congrArg TheAnswerIs h) TheAnswerIs.intro)
  else
    have k : ¬TheAnswerIs n := by
      intro answer
      match answer with
      | TheAnswerIs.intro => simp at h
    isFalse k

#synth Decidable (TheAnswerIs 0)

#synth Decidable (TheAnswerIs 42)

#eval decide (TheAnswerIs 0)
-- false

#eval decide (TheAnswerIs 42)
-- true
