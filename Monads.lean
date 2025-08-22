
def unit_left (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, (fun a => (a |> pure) >>= f) = f
  -- or (pure · >>= f) = f

def unit_left' (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, pure >=> f = f

theorem ul' (m : Type u → Type v) [Monad m] : unit_left m -> unit_left' m := by
  intro h
  intro α β f
  ext x
  rw [Bind.kleisliRight]
  rw [unit_left] at h
  exact congrFun (h (f := f)) x

theorem ul (m : Type u → Type v) [Monad m] : unit_left' m -> unit_left m := by
  admit
