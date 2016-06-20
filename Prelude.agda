module OTT.Prelude where

open import Level
  renaming (Level to MetaLevel; zero to lzeroₘ; suc to lsucₘ; _⊔_ to _⊔ₘ_) using () public
open import Function public
open import Relation.Binary.PropositionalEquality
  as P renaming (refl to prefl; trans to ptrans; cong to pcong; cong₂ to pcong₂) using (_≡_) public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Nat.Base hiding (_⊔_; _≟_; erase) public
open import Data.Maybe.Base using (Maybe; nothing; just) public
open import Data.Product hiding (,_) renaming (map to pmap) public

open import OTT.Lib.Heteroindexed public
open import OTT.Lib.Decidable public

open import Relation.Nullary
open import Relation.Binary

infix 4  ,_

pattern ,_ y = _ , y

instance
  iprefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  iprefl = prefl

  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y

pright : ∀ {α} {A : Set α} {x y z : A} -> x ≡ y -> x ≡ z -> y ≡ z
pright prefl prefl = prefl

,-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
      -> (x₁ , y₁) ≡ (x₂ , y₂) -> [ B ] y₁ ≅ y₂
,-inj prefl = irefl

_<,>ᵈ_ : ∀ {α β} {A : Set α} {B : Set β} {x₁ x₂ : A} {y₁ y₂ : B}
       -> x₁ # x₂ -> y₁ # y₂ -> x₁ , y₁ # x₂ , y₂
_<,>ᵈ_ = dcong₂ _,_ (inds-homo ∘ ,-inj)

_<,>ᵈᵒ_ : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
        -> x₁ # x₂ -> (∀ y₂ -> y₁ # y₂) -> x₁ , y₁ # x₂ , y₂
_<,>ᵈᵒ_ = dhcong₂ _,_ ,-inj

record Apply {α β} {A : Set α} (B : A -> Set β) x : Set β where
  constructor tag
  field detag : B x
open Apply public

tag-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x} {y₁ y₂ : B x}
        -> tag {B = B} y₁ ≡ tag y₂ -> y₁ ≡ y₂
tag-inj prefl = prefl

module _ {α} {A : Set α} where
  open import Relation.Nullary.Decidable
  open import Data.Maybe

  toPropEq : {a b : Maybe A} -> a ≡ b -> Eq _≡_ a b
  toPropEq {a = nothing} prefl = nothing
  toPropEq {a = just _ } prefl = just prefl

  fromPropEq : {a b : Maybe A} -> Eq _≡_ a b -> a ≡ b
  fromPropEq (just q) = pcong just q
  fromPropEq  nothing = prefl

  fromDecPropEq : {a b : Maybe A} -> Dec (Eq _≡_ a b) -> Dec (a ≡ b)
  fromDecPropEq = map′ fromPropEq toPropEq where

  decideMaybe : Decidable (_≡_ {A = A}) -> Decidable (_≡_ {A = Maybe A})
  decideMaybe D a b = fromDecPropEq (a ≟ b) where
    open DecSetoid (decSetoid (P.decSetoid D))

Enum : ℕ -> Set
Enum  0      = ⊥
Enum  1      = ⊤
Enum (suc n) = Maybe (Enum n)

decEnum : ∀ n -> Decidable (_≡_ {A = Enum n})
decEnum  0            () ()
decEnum  1            tt tt = yes prefl
decEnum (suc (suc n)) e₁ e₂ = decideMaybe (decEnum (suc n)) e₁ e₂
