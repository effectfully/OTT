module OTT.Data.Variations.FinF where

open import OTT.Main
open import OTT.Data.Maybe

fin : ℕ -> Type
fin  0      = unit & bot
fin (suc n) = maybe (fin n)

Fin : ℕ -> Set
Fin n = ⟦ fin n ⟧

fzero : ∀ n -> Fin (suc n)
fzero _ = nothing

fsuc : ∀ n -> Fin n -> Fin (suc n)
fsuc _ = just

elimFin : ∀ {n π}
        -> (P : ∀ n -> Fin n -> Set π)
        -> (∀ {n} {i : Fin n} -> P n i -> P (suc n) (fsuc n i))
        -> (∀ {n} -> P (suc n) (fzero n))
        -> (i : Fin n)
        -> P n i
elimFin {0}     P f x (_ , ())
elimFin {suc n} P f x  nothing = x
elimFin {suc n} P f x (just i) = f (elimFin P f x i)
elimFin {suc n} P f x  ⟨⟩₂
