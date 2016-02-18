module OTT.Data.W where

open import OTT.Main

w : (A : Type) -> (⟦ A ⟧ -> Type) -> Type
w A B = rose ((pi A λ x -> ret ((B x ⇨ ret triv) ∷ [] , triv)) ∷ []) triv

W : (A : Type) -> (⟦ A ⟧ -> Type) -> Set
W A B = ⟦ w A B ⟧

sup : ∀ {A} {B : ⟦ A ⟧ -> Type} x -> (⟦ B x ⟧ -> W A B) -> W A B
sup x g = #₀ (x , g ∷ [] , tt)

elimW : ∀ {π A} {B : ⟦ A ⟧ -> Type}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : ⟦ B x ⟧ -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h (#₀ (x , g ∷ [] , tt)) = h (λ y -> elimW P h (g y))
elimW P h  ⟨⟩₁
