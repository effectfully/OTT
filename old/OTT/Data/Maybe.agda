module OTT.Data.Maybe where

open import OTT.Main

maybe : ∀ {k} -> Univ k -> Type
maybe A = rose (ret ([] , triv) ∷ (A ⇨ ret ([] , triv)) ∷ []) triv

Maybe : ∀ {k} -> Univ k -> Set
Maybe A = ⟦ maybe A ⟧

pattern nothing = #₀ ([] , tt)
pattern just x  = #₁ (x , [] , tt)

elimMaybe : ∀ {k π} {A : Univ k} {P : Maybe A -> Set π}
          -> (∀ x -> P (just x)) -> P nothing -> ∀ a -> P a
elimMaybe f z  nothing = z
elimMaybe f z (just x) = f x
elimMaybe f z  ⟨⟩₂

fmap : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ (A ⇒ B) ⇒ maybe A ⇒ maybe B ⟧
fmap f = elimMaybe (just ∘ f) nothing
