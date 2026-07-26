import Mathlib

/-!


The *existence* of a proof for a proposition, checked by Lean matters obviously.
But not its exact nature.

TODO: build a Prop that proves in two different ways that some numbers are
coprimes. Check that they are considered equal by Lean. Why?

Use the context of rationals. Two structures are considered equal iff all
the fields are equals. The only "sane" way to get a sane equality for
rationals is to accept that all possible proofs of coprimality of integers
are equal.
-/

#print Rat
-- structure Rat : Type
-- number of parameters: 0
-- fields:
--   Rat.num : Int
--   Rat.den : Nat :=
--     1
--   Rat.den_nz : self.den ≠ 0 := by
--     decide
--   Rat.reduced : self.num.natAbs.Coprime self.den := by
--     decide
-- constructor:
--   Rat.mk' (num : Int) (den : Nat) (den_nz : den ≠ 0 := by decide) (reduced : num.natAbs.Coprime den := by decide) : Rat

theorem coprime_4_3 : Nat.Coprime 4 3 := by
  decide

theorem foo : (1:Nat) + 1 = 2 := by decide
#reduce (proofs := true) foo          -- Eq.refl 2

#print coprime_4_3
-- theorem coprime_4_3 : Nat.Coprime 4 3 :=
-- of_decide_eq_true (id (Eq.refl true))

#reduce (proofs := true) coprime_4_3

theorem coprime_4_3' : Nat.Coprime 4 3 := by
  rw [Nat.coprime_iff_gcd_eq_one] -- ⊢ Nat.gcd 4 3 = 1
  rw [Nat.gcd]                    -- ⊢ (if 4 = 0 then 3 else (3 % 4).gcd 4) = 1
  rw [if_neg (by decide)]         -- ⊢ (3 % 4).gcd 4 = 1
  simp only [Nat.reduceMod]       -- ⊢ Nat.gcd 3 4 = 1
  rw [Nat.gcd]                    -- ⊢ (if 3 = 0 then 4 else (4 % 3).gcd 3) = 1
  rw [if_neg (by decide)]         -- ⊢ (4 % 3).gcd 3 = 1
  simp only [Nat.reduceMod]       -- ⊢ Nat.gcd 1 3 = 1
  rw [Nat.gcd]                    -- ⊢ (if 1 = 0 then 3 else (3 % 1).gcd 1) = 1
  simp only [Nat.reduceMod]       -- ⊢ (if 1 = 0 then 3 else Nat.gcd 0 1) = 1
  rw [if_neg (by decide)]         -- ⊢ Nat.gcd 0 1 = 1
  rw [Nat.gcd]                    -- ⊢ (if 0 = 0 then 1 else (1 % 0).gcd 0) = 1
  rw [if_pos (by rfl)]            -- 0 = 0

#print coprime_4_3'
-- theorem coprime_4_3' : Nat.Coprime 4 3 :=
-- Eq.mpr (id (congrArg (fun _a => _a) (propext Nat.coprime_iff_gcd_eq_one)))
--   (Eq.mpr (id (congrArg (fun _a => _a = 1) (Nat.gcd.eq_1 4 3)))
--     (Eq.mpr (id (congrArg (fun _a => _a = 1) (if_neg (of_decide_eq_true (id (Eq.refl true))))))
--       (id
--         (Eq.mpr (id (congrArg (fun _a => _a = 1) (Nat.gcd.eq_1 3 4)))
--           (Eq.mpr (id (congrArg (fun _a => _a = 1) (if_neg (of_decide_eq_true (id (Eq.refl true))))))
--             (id
--               (Eq.mpr (id (congrArg (fun _a => _a = 1) (Nat.gcd.eq_1 1 3)))
--                 (Eq.mpr
--                   (id
--                     (congrFun'
--                       (congrArg Eq (ite_congr (Eq.refl (1 = 0)) (fun a => Eq.refl 3) fun a => Eq.refl (Nat.gcd 0 1)))
--                       1))
--                   (Eq.mpr (id (congrArg (fun _a => _a = 1) (if_neg (of_decide_eq_true (id (Eq.refl true))))))
--                     (Eq.mpr (id (congrArg (fun _a => _a = 1) (Nat.gcd.eq_1 0 1)))
--                       (Eq.mpr (id (congrArg (fun _a => _a = 1) (if_pos (Eq.refl 0)))) (Eq.refl 1))))))))))))

#eval coprime_4_3 = coprime_4_3' -- implicit `decide` applied

def r1 := Rat.mk' 4 3 (by positivity) coprime_4_3

def r2 := Rat.mk' 4 3 (by positivity) coprime_4_3'

#check r1 = r2
-- r1 = r2 : Prop

#eval r1 = r2 -- implicit `decide` applied
-- true


/-!
Extra : what matters when you do a proof that has hypotheses (props) and a
conclusion (a prop) is how you derive (constructively) the conclusion from
the arguments. But the nature of the arguments should not matter. You are
not able to "special-case" your proofs on the nature of the proof of the
hypotheses (like you are able to special-case for functions with classic
values, by pattern-matching for example). Which is *good* for modularity
I guess?
-/

theorem modus_ponens (P Q : Prop) : (P ∧ (P → Q)) → Q :=
  fun p_and_p_implies_q =>
    let ⟨p, p_imp_q⟩ := p_and_p_implies_q
    p_imp_q p
