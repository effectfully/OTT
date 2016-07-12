module OTT.Data.Sum where

open import OTT.Main

infixr 3 _⊕_ _⊎_

_⊕_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Type₋₁ (α ⊔ β)
_⊕_ {α = α} {β} A B = cmu₋₁ (α ⊔ β)
                    $ (A ⇨ pos)
                    ∷ (B ⇨ pos)
                    ∷ []

_⊎_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Set
A ⊎ B = ⟦ A ⊕ B ⟧

pattern inj₁ x =  #₀ (x , tt)
pattern inj₂ y = !#₁ (y , tt)

[_,_] : ∀ {a b π} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} {P : A ⊎ B -> Set π}
      -> (∀ x -> P (inj₁ x)) -> (∀ y -> P (inj₂ y)) -> ∀ s -> P s
[ f , g ] = elim′ _ (fromTuple (f , g))

smap : ∀ {a₁ a₂ b₁ b₂} {α₁ : Level a₁} {α₂ : Level a₂} {β₁ : Level b₁} {β₂ : Level b₂}
         {A₁ : Univ α₁} {A₂ : Univ α₂} {B₁ : Univ β₁} {B₂ : Univ β₂}
     -> ⟦ (A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂) ⇒ A₁ ⊕ B₁ ⇒ A₂ ⊕ B₂ ⟧
smap f g = [ inj₁ ∘ f , inj₂ ∘ g ]
