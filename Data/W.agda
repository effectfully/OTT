module OTT.Data.W where

open import OTT.Main

w : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔ β)
w A B = mu (π A λ x -> (B x ⇨ pos) ⊛ pos)

W : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Set
W A B = ⟦ w A B ⟧

pattern sup x g = node (x , g , tt)

elimW : ∀ {a b π} {α : Level a} {β : Level b} {A : Univ α} {B : ⟦ A ⟧ -> Univ β}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : ⟦ B x ⟧ -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h = elim′ P λ _ _ -> h
