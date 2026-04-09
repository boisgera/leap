
/-!
# Type Inhabitation

Prove that `(α → β → γ) → ((β → α) → β) → α → γ` is inhabited.

-/


def f {α β γ} : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun (abg : α → β → γ) (bab : (β → α) → β) (a : α) =>
    let ba : β → α := fun (_ : β) => a
    let b : β := bab ba
    let g : γ := abg a b
    g

#check f
-- f.{u_1, u_2, u_3} {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} :
-- (α → β → γ) → ((β → α) → β) → α → γ
