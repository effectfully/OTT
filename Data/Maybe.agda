module OTT.Data.Maybe where

open import OTT.Main

maybe : ∀ {a} {α : Level a} -> Univ α -> Type₋₁ α
maybe {α = α} A = cmu′ α $ pos ∷ (A ⇨ pos) ∷ []

Maybe : ∀ {a} {α : Level a} -> Univ α -> Set
Maybe A = ⟦ maybe A ⟧

pattern nothing = #₀  tt
pattern just x  = !#₁ (x , tt)

elimMaybe : ∀ {a π} {α : Level a} {A : Univ α} {P : Maybe A -> Set π}
          -> (∀ x -> P (just x)) -> P nothing -> ∀ a -> P a
elimMaybe f z = elim′ _ (fromTuple (z , f))

fmap : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
     -> ⟦ (A ⇒ B) ⇒ maybe A ⇒ maybe B ⟧
fmap f = elimMaybe (just ∘ f) nothing
