module OTT.Tele.W where

open import OTT.Prelude
open import OTT.Tele.Core
open import OTT.Tele.Coerce

w : (A : Type) -> (⟦ A ⟧ -> Type) -> Type
w A B = rose ((pi A λ x -> ret ((pi (B x) λ _ -> ret triv) ∷ [] , triv)) ∷ []) triv

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
