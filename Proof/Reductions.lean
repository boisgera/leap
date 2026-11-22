import Mathlib
import Lean
open Lean Meta Elab Command Term

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
  logInfo m!"{e}\n⟶\n{← whnf e}"

#whnf (fun x => x + 1) 2
#whnf List.map (· + 1) [1, 2, 3]
#whnf 1 + 2

/-!
TODO: compare with the kind of reduction that `simp only` is doing?
-/
