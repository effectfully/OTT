module OTT.Lib.Decidable where

open import Relation.Nullary public
open import Relation.Nullary.Decidable public
open import Relation.Binary using (Decidable) public

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import OTT.Lib.Heteroindexed

infixl 10 _%
infix  3  _#_

_% = _∘_

IsSet : ∀ {α} -> Set α -> Set α
IsSet A = Decidable {A = A} _≡_

_#_ : ∀ {α} {A : Set α} -> A -> A -> Set α
x # y = Dec (x ≡ y)

delim : ∀ {α π} {A : Set α} {P : Dec A -> Set π}
      -> (∀ x -> P (yes x)) -> (∀ c -> P (no c)) -> (d : Dec A) -> P d
delim f g (yes x) = f x
delim f g (no  c) = g c

drec : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> B) -> Dec A -> B
drec = delim

dmap : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> ¬ B) -> Dec A -> Dec B
dmap f g = drec (yes ∘ f) (no ∘ g)

sumM2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      -> (A -> Dec C) -> (B -> Dec C) -> (¬ A -> ¬ B -> Dec C) -> Dec A -> Dec B -> Dec C
sumM2 f g h d e = drec f (λ c -> drec g (h c) e) d

prodM2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> (A -> B -> Dec C) -> (¬ A -> Dec C) -> (¬ B -> Dec C) -> Dec A -> Dec B -> Dec C
prodM2 h f g d e = drec (λ x -> drec (h x) g e) f d

sumF2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      -> (A -> C) -> (B -> C) -> (¬ A -> ¬ B -> ¬ C) -> Dec A -> Dec B -> Dec C
sumF2 f g h = sumM2 (yes ∘ f) (yes ∘ g) (no % ∘ h) 

prodF2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> (A -> B -> C) -> (¬ A -> ¬ C) -> (¬ B -> ¬ C) -> Dec A -> Dec B -> Dec C
prodF2 h f g = prodM2 (yes % ∘ h) (no ∘ f) (no ∘ g) 

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      -> (f : A -> B) -> (f x ≡ f y -> x ≡ y) -> x # y -> f x # f y
dcong f inj = dmap (cong f) (_∘ inj)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
       -> (f : A -> B -> C)
       -> (f x₁ y₁ ≡ f x₂ y₂ -> x₁ ≡ x₂ × y₁ ≡ y₂)
       -> x₁ # x₂
       -> y₁ # y₂
       -> f x₁ y₁ # f x₂ y₂
dcong₂ f inj = prodF2 (cong₂ f) (λ c -> c ∘ proj₁ ∘ inj) (λ c -> c ∘ proj₂ ∘ inj)

dhcong₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
        -> (f : ∀ x -> B x -> C) 
        -> (f x₁ y₁ ≡ f x₂ y₂ -> [ B ] y₁ ≅ y₂)
        -> x₁ # x₂
        -> (∀ y₂ -> y₁ # y₂)
        -> f x₁ y₁ # f x₂ y₂
dhcong₂ f inj (yes refl) q = dcong (f _) (homo ∘ inj) (q _)
dhcong₂ f inj (no c)     q = no (c ∘ inds ∘ inj)

,-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
      -> (x₁ , y₁) ≡ (x₂ , y₂) -> [ B ] y₁ ≅ y₂
,-inj refl = irefl

_<,>ᵈ_ : ∀ {α β} {A : Set α} {B : Set β} {x₁ x₂ : A} {y₁ y₂ : B}
       -> x₁ # x₂ -> y₁ # y₂ -> x₁ , y₁ # x₂ , y₂
_<,>ᵈ_ = dcong₂ _,_ (inds-homo ∘ ,-inj)

_<,>ᵈⁱ_ : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
        -> x₁ # x₂ -> (∀ y₂ -> y₁ # y₂) -> x₁ , y₁ # x₂ , y₂
_<,>ᵈⁱ_ = dhcong₂ _,_ ,-inj
