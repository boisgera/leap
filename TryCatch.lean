#print Except.tryCatch
-- protected def Except.tryCatch.{u, u_1} : {ε : Type u} → {α : Type u_1} → Except ε α → (ε → Except ε α) → Except ε α :=
-- fun {ε} {α} ma handle =>
--   match ma with
--   | Except.ok a => Except.ok a
--   | Except.error e => handle e

#check MonadExcept.tryCatch
-- MonadExcept.tryCatch.{u, v, w} {ε : outParam (Type u)}
--   {m : Type v → Type w} [self : MonadExcept ε m] {α : Type v}
--   (body : m α) (handler : ε → m α) :
--   m α


-- **TODO.** State that "every value of type Except ε α which is equal to a
-- try catch whose handler is ok for every potential error is ok.".
-- Or better, the comutable version, where we extract the value from the
-- exception.

theorem safe_try_except {ε α} (body : Except ε α) (handler : ε -> Except ε α) :
  (∀ (e : ε), (handler e).isOk = true) -> (tryCatch body handler).isOk = true
  := by
  intro h_ok
  rw [tryCatch]
  rw [instMonadExceptOfMonadExceptOf]
  simp [tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
  cases body with
  | ok a =>
    rw [Except.isOk, Except.toBool]
  | error e =>
    simp
    rw [h_ok e]

-- Nota: if instead of a new definition, we use Except.toList and Option.get,
-- we may be able to leverage the associated some_get & get_some simp theorems.
def Except.get {ε α} (except : Except ε α) : except.isOk = true -> α :=
  fun ex_ok =>
    match except with
    | ok a => a
    | error _ => nomatch ex_ok
