#print Bind.kleisliRight
-- def Bind.kleisliRight.{u, u_1, u_2} :
--   {α : Type u} →
--   {m : Type u_1 → Type u_2} → {β γ : Type u_1} → [Bind m] →
--   (α → m β) → (β → m γ) → α → m γ :=
--   fun {α} {m} {β γ} [Bind m] f₁ f₂ a => f₁ a >>= f₂

universe u_1 u_2

-- TODO: roll back the variables
variable {m : Type u_1 -> Type u_2} [Monad m]

variable {α : Type u_1} (a : α) (ma : m α)

variable {β γ δ : Type u_1} {f : α -> m β} {g : β -> m γ} {h : γ -> m δ}

-- Turn the definition into an equality (easy!)
theorem kleisli : (f >=> g) a = f a >>= g := by
  rw [Bind.kleisliRight]

-- Define f >=> g as a function, without explicit reference to an argument
theorem kleisli' : (f >=> g) = (fun a => f a >>= g) := by
  ext a -- `funext a` would also work
  rw [kleisli] -- apply kleisli would also work

-- Define f >=> g as a function, using |> and · in the rhs
theorem kleisli'' : f >=> g = (f · >>= g) := by
  rw [kleisli']

def unit_left : Prop := (pure · >>= f) = f

def unit_left' : Prop := (pure >=> f) = f

-- Study why I need to specify again so many already declared parameters ...
-- Ah OK, I can guess: otherwise the implication is ambiguous, we could end
-- up with different monads m and function on the left and the right of ->
-- OTOH it's ok to have m implicit (it's inferred) by the knowledge of the
-- type of f.
theorem ul' (f : α -> m β) : (unit_left (f:=f) -> unit_left' (f:=f)) := by
  intro h
  rw [unit_left] at h
  rw [unit_left'] at ⊢
  -- rw [kleisli] won't work, we do not have args
  rw [kleisli'] -- better :)
  rw [h] -- or apply h, or exact h, or assumptions, etc.

theorem ul (f : α -> m β) : unit_left' (f := f) -> unit_left (f := f) := by
  intro h
  rw [unit_left, unit_left'] at *
  rw [kleisli'] at h
  rw [h]

-- Here we try a more explicit version, without using the variables
-- (since it generates its own set of problems to solve!)
-- Honnestly at this stage I'd like to rollback on variables until I
-- understand in details what's going on.
-- Mmm except that it also simplifies the PROOFS? Not really,
-- what simplifies the proof is having the types & such at the left of
-- :, not as ∀ in the right.
def unit_right (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, (f ·  >>= pure) = f
  -- or (f · >>= pure) = f

def unit_right' (m : Type u → Type v) [Monad m] :=
  ∀ {α β : Type u}, ∀ {f : α -> m β}, f >=> pure = f

def ur' (m : Type u → Type v) [Monad m] : unit_right m -> unit_right' m := by
  intro h
  rw [unit_right] at h
  rw [unit_right'] at ⊢
  intro α β f
  have h := h (α := α) (β := β) (f := f) -- specialization
  rw [kleisli']
  rw [h]


def ur (m : Type u → Type v) [Monad m] : unit_right' m -> unit_right m := by
  intro h
  rw [unit_right'] at h
  rw [unit_right] at ⊢
  intro α β f
  have h := h (α := α) (β := β) (f := f) -- specialization
  rw [kleisli'] at h
  rw [h]

def assoc (m : Type u -> Type v) [Monad m] :=
  ∀ {α β γ : Type u} (f : α -> m β) (g : β → m γ),
  ∀ (ma : m α), (ma >>= f >>= g) = (ma >>= (f · >>= g))

def assoc' (m : Type u -> Type v) [Monad m] :=
  ∀ {α β γ δ: Type u} (f : α -> m β) (g : β → m γ) (h : γ -> m δ),
  (f >=> g) >=> h = f >=> (g >=> h)

theorem ass' (m : Type u -> Type v) [Monad m] : assoc m -> assoc' m := by
  rw [assoc, assoc']
  intro ha
  intro α β γ δa
  intro f g h
  ext a
  rw [kleisli]
  rw [kleisli]
  rw [kleisli]
  rw [kleisli']
  have ha' := ha (f := g) (g := h) (ma := f a)
  rw [ha']

theorem ass (m : Type u -> Type v) [Monad m] : assoc' m -> assoc m := by
  rw [assoc, assoc']; intro ha
  intro α β γ
  intro f g
  intro ma
  -- rw [kleisli'] at ha doesn't work (not under binders, here the ∀)
  -- but we can specialize ha to make it work, right?
  have ha := ha (fun (_ : PUnit) => ma) f g
  repeat rw [kleisli'] at ha
  have h' := congrFun ha PUnit.unit -- (fun a => ma >>= f) PUnit.unit >>= g = ma >>= fun a => f a >>= g
  dsimp at h' -- definitional reduction; simp at h' would work too.
  rw [h']
