-- An example from https://pigworker.wordpress.com/2015/01/08/observational-type-theory-delivery/

module OTT.Examples.Favourite where

open import OTT.Main

c42 : ℕ -> ℕ
c42 = const 42

favourite : (ℕ -> ℕ) -> Prop
favourite = imu (var c42)

Favourite : (ℕ -> ℕ) -> Set
Favourite f = ⟦ favourite f ⟧

pattern faveₑ q = node q

fave : Favourite c42
fave = faveₑ (refl c42)

deep : ℕ -> ℕ
deep  0      = 42
deep (suc n) = deep n

deep-42 : ∀ n -> ⟦ 42 ≟ⁿ deep n ⟧
deep-42  0      = tt
deep-42 (suc n) = deep-42 n

fave′ : Favourite deep
fave′ = faveₑ (λ _ n _ -> deep-42 n)
