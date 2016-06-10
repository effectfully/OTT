module OTT.Data.Lift where

open import OTT.Main

Lift : ∀ {a b} {α : Level a} -> (β : Level b) -> Univ α -> Univ (α ⊔ β)
Lift β A = mu (A ⇨ pos)

-- lift : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} -> ⟦ A ⟧ -> ⟦ Lift β A ⟧
pattern lift x = node (x , tt)

lower : ∀ {a b} {α : Level a} {A : Univ α} -> (β : Level b) -> ⟦ Lift β A ⟧ -> ⟦ A ⟧
lower β (lift x) = x

private
  β = natToLevel 2

  lnat : Univ# 2
  lnat = Lift β nat

  ln : ⟦ lnat ⟧
  ln = lift 0

  n : ℕ
  n = lower β ln
