module OTT.Lib.PartDec where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import OTT.Lib.HeteroIndexed

infixl 10 _%
infix  3  _#_

_% = _∘_

data PartDec {α} (A : Set α) : Set α where
  yes  : A   -> PartDec A
  no   : ¬ A -> PartDec A
  none : PartDec A

PartDecidable : ∀ {α} {A : Set α} -> (A -> A -> Set α) -> Set α
PartDecidable _~_ = ∀ x y -> PartDec (x ~ y)

IsPartSet : ∀ {α} -> Set α -> Set α
IsPartSet A = PartDecidable {A = A} _≡_

_#_ : ∀ {α} {A : Set α} -> A -> A -> Set α
x # y = PartDec (x ≡ y)

delim : ∀ {α π} {A : Set α} {P : PartDec A -> Set π}
      -> (∀ x -> P (yes x)) -> (∀ c -> P (no c)) -> P none -> (d : PartDec A) -> P d
delim f g z (yes x) = f x
delim f g z (no  c) = g c
delim f g z  none   = z

drec : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> B) -> B -> PartDec A -> B
drec = delim

dbind : ∀ {α β} {A : Set α} {B : Set β}
      -> (A -> PartDec B) -> (¬ A -> PartDec B) -> PartDec A -> PartDec B
dbind f g = drec f g none

dmap : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> ¬ B) -> PartDec A -> PartDec B
dmap f g = dbind (yes ∘ f) (no ∘ g)

sumM2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      -> (A -> PartDec C)
      -> (B -> PartDec C)
      -> (¬ A -> ¬ B -> PartDec C)
      -> PartDec A -> PartDec B
      -> PartDec C
sumM2 f g h d e = dbind f (λ c -> dbind g (h c) e) d

prodM2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> (A -> B -> PartDec C)
       -> (¬ A -> PartDec C)
       -> (¬ B -> PartDec C)
       -> PartDec A
       -> PartDec B
       -> PartDec C
prodM2 h f g d e = dbind (λ x -> dbind (h x) g e) f d

sumF2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
     -> (A -> C) -> (B -> C) -> (¬ A -> ¬ B -> ¬ C) -> PartDec A -> PartDec B -> PartDec C
sumF2 f g h = sumM2 (yes ∘ f) (yes ∘ g) (no % ∘ h) 

prodF2 : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
       -> (A -> B -> C) -> (¬ A -> ¬ C) -> (¬ B -> ¬ C) -> PartDec A -> PartDec B -> PartDec C
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
dhcong₂ f inj  none      q = none

decToPartDec : ∀ {α} {A : Set α} -> Dec A -> PartDec A
decToPartDec (yes x) = yes x
decToPartDec (no  c) = no  c
