
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
  intro h
  rw [unit_left'] at h
  rw [unit_left]
  intro α β f
  funext a
  specialize h (α := α) (β := β) (f := f)
  have h' := congrFun h a
  rw [Bind.kleisliRight] at h'
  assumption

def unit_right (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, (fun a => f a >>= pure) = f
  -- or (f · >>= pure) = f

def unit_right' (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, f >=> pure = f

def ur' (m : Type u → Type v) [Monad m] : unit_right m -> unit_right' m := by
  intro h
  rw [unit_right] at h
  rw [unit_right']
  intro α β f
  specialize h (α := α) (β := β) (f := f)
  apply funext -- or ext x
  intro x
  rw [Bind.kleisliRight]
  revert x
  apply congrFun
  assumption

def ur (m : Type u → Type v) [Monad m] : unit_right' m -> unit_right m := by
  rw [unit_right, unit_right']
  intro h
  intro α β f
  specialize h (α := α) (β := β) (f := f)
  have h' := congrFun h
  simp [Bind.kleisliRight] at h' -- rw wouldn't work here *directly*
  funext a
  exact h' a

def assoc (m : Type u -> Type v) [Monad m] :=
  ∀ {α β γ : Type u} {f : α -> m β} {g : β → m γ},
  ∀ (ma : m α), (ma >>= f >>= g) = (ma >>= fun a => f a >>= g)

def assoc' (m : Type u -> Type v) [Monad m] :=
  ∀ {α β γ δ: Type u} {f : α -> m β} {g : β → m γ} {h : γ -> m δ},
  (f >=> g) >=> h = f >=> (g >=> h)

theorem ass' (m : Type u -> Type v) [Monad m] : assoc m -> assoc' m := by
  intro ha
  rw [assoc, assoc'] at *
  intro α β γ δ f g h
  ext ma
  simp [Bind.kleisliRight] -- ⊢ f ma >>= g >>= h = f ma >>= (g >=> h)
  -- need to replace g >=> h with (fun x => (g >=> h) x) in order to
  -- get rid of the Kleisli operator.
  -- nth_rewrite would work, but that's in Mathlib
  change f ma >>= g >>= h = f ma >>= (fun x => (g >=> h) x)
  specialize ha (f := g) (g := h) (f ma)
  simp [Bind.kleisliRight]
  assumption

theorem ass (m : Type u -> Type v) [Monad m] : assoc' m -> assoc m := by
  admit
