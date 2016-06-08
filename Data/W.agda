module OTT.Data.W where

open import OTT.Main

-- instance
--   level-⊔ : ∀ {a b} {{α : Level a}} {{β : Level b}} -> Level (a ⊔ₘ b)
--   level-⊔ {{α}} {{β}} = α ⊔ β

-- w : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔ β)
-- w {α = α} {β} A B = mu {{_}} (πᵈ {{α ⊔ β}} A λ x -> (_⇒ᵈ_ {{α ⊔ β}} (B x) pos) ⊛ pos)

w : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔ β)
w A B = mu (πᵈ A λ x -> (B x ⇒ᵈ pos) ⊛ pos)

W : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Set
W A B = ⟦ w A B ⟧

pattern sup x g = node (x , g , tt)

{-# TERMINATING #-}
elimW : ∀ {a b π} {α : Level a} {β : Level b} {A : Univ α} {B : ⟦ A ⟧ -> Univ β}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : ⟦ B x ⟧ -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h (sup x g) = h (λ y -> elimW P h (g y))
