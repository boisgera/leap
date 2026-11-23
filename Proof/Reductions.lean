import Mathlib
import Lean
open Lean Meta Elab Command Term

/-!
Reductions
================================================================================
-/

/-!
Typology
--------------------------------------------------------------------------------
-/

/-!
### $δ$ and $ζ$-reductions
-/

def n := 7

#reduce n -- 7

#reduce (let m := 3; m) -- 3

/-!
### $β$-reduction

A.k.a . function application:
-/

#reduce (fun n => n + 1) 42 -- 43


/-!
### $ι$-reduction
-/

#reduce match true with
  | false => "not OK"
  | true => "OK"
-- "OK"

/-!
### Projection
-/

structure Point2D where
  x : ℕ
  y : ℕ

#reduce {x := 3, y := 5 : Point2D}.y -- 5

/-!
### Quotient
-/

namespace Sandbox

#check Quotient
-- Quotient.{u} {α : Sort u} (s : Setoid α) : Sort u

#print Setoid
-- class Setoid.{u} (α : Sort u) : Sort (max 1 u)
-- number of parameters: 1
-- fields:
--   Setoid.r : α → α → Prop
--   Setoid.iseqv : Equivalence ⇑self
-- constructor:
--   Setoid.mk.{u} {α : Sort u} (r : α → α → Prop) (iseqv : Equivalence r) : Setoid α

#print Equivalence
-- structure Equivalence.{u} {α : Sort u} (r : α → α → Prop) : Prop
-- number of parameters: 2
-- fields:
--   Equivalence.refl : ∀ (x : α), r x x
--   Equivalence.symm : ∀ {x y : α}, r x y → r y x
--   Equivalence.trans : ∀ {x y z : α}, r x y → r y z → r x z
-- constructor:
--   Equivalence.mk.{u} {α : Sort u} {r : α → α → Prop} (refl : ∀ (x : α), r x x) (symm : ∀ {x y : α}, r x y → r y x)
--     (trans : ∀ {x y z : α}, r x y → r y z → r x z) : Equivalence r

structure IntBase where
  pos : Nat
  neg : Nat

def IntBase.r (x y : IntBase) : Prop :=
  x.pos + y.neg = y.pos + x.neg

theorem IntBase.r_iseq : Equivalence r := {
  refl := by intro x; rw [r]
  symm := by intro x y hxy; simp [r] at *; exact hxy.symm
  trans := by intro x y z hxy hyz; simp [r] at *; grind
}

instance : Setoid IntBase where
  r := IntBase.r
  iseqv := IntBase.r_iseq

def Int := Quotient (inferInstance : Setoid IntBase)

-- TODO: function on Int; then transpose some of

-- def Parity := Quot (fun a b : Nat => a % 2 = b % 2)

-- def Parity.mk (n : Nat) : Parity := Quot.mk _ n

-- def Parity.isEven : Parity → Bool :=
--   Quot.lift (fun n => n % 2 == 0) (by
--     intro a b h
--     rw [h])

-- example : Parity.mk 2 = Parity.mk 4 := Quot.sound rfl   -- via the axiom

-- #reduce Parity.isEven (Parity.mk 4)   -- true, via Quot.lift f h (Quot.mk r a) ⇝ f a

-- end Sandbox


/-!
Reflexivity and weak head normal forms
--------------------------------------------------------------------------------

The `rfl` tactic proves obvious equalities like `0 = 0` but it also normalizes
each side of the equation into a weak head normal form before it performs the
obvious comparison between terms: it applies the sequence of classic reduction
*at the top-level of the expression* until it reaches something that it cannot
reduce: a constructor. Note that the arguments of the constructors may well
not be reduced.

-/

/-!
Need to talk about what rfl is doing? (-> whnf)?
What `simp only` is doing? (or done later?)
what `dsimp only` is doing?

AT THE VERY LEAST RFL, what it means, what it covers.
-/


/-- Reduce any `Expr` to weak head normal form (default transparency). -/
def whnfExpr (e : Expr) : MetaM Expr := whnf e

-- /-- Same, but unfolding everything, including `@[irreducible]` definitions. -/
def whnfAll (e : Expr) : MetaM Expr :=
  withTransparency .all (whnf e)

/-- `#whnf t` elaborates `t` and prints its weak head normal form. -/
elab "#whnf " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  logInfo m!"{e} ⟶ {← whnf e}"

#whnf (fun x => x + 1) 2
-- (fun x => x + 1) 2 ⟶ 3
#whnf List.map (· + 1) [1, 2, 3]
-- List.map (fun x => x + 1) [1, 2, 3] ⟶ (fun x => x + 1) 1 :: List.map (fun x => x + 1) [2, 3]
#whnf 1 + 2
-- 1 + 2 ⟶ 3


/-!
TODO: compare with the kind of reduction that `simp only` is doing?
And the #reduce?
-/

def deepWhnfCore (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let e' ← whnfCore e
    if e' == e then return .done e else return .visit e')

elab "#simp_only " t:term : command => Elab.Command.liftTermElabM do
  let e ← Elab.Term.elabTerm t none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  logInfo m!"{e} ⟶ {← deepWhnfCore e}"

#simp_only (fun x => x + 1) 2
-- (fun x => x + 1) 2 ⟶ 2 + 1
#simp_only List.map (· + 1) [1, 2, 3]
-- List.map (fun x => x + 1) [1, 2, 3] ⟶ List.map (fun x => x + 1) [1, 2, 3]
#simp_only 1 + 2
-- 1 + 2 ⟶ 1 + 2

#reduce (fun x => x + 1) 2
-- 3
#reduce List.map (· + 1) [1, 2, 3]
-- [2, 3, 4]
#reduce 1 + 2
-- 3

/-!
Concretely, reduce is the cbv stuff?
-/
