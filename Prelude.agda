module OTT.Prelude where

open import Level
  renaming (Level to MetaLevel; zero to lzeroₘ; suc to lsucₘ; _⊔_ to _⊔ₘ_) using () public
open import Function public
open import Relation.Binary.PropositionalEquality as P using (_≡_)
  renaming (refl to prefl; trans to ptrans; subst to psubst; cong to pcong; cong₂ to pcong₂) public
open import Data.Empty public
open import Data.Nat.Base hiding (_⊔_; _≟_; erase) public
open import Data.Maybe.Base using (Maybe; nothing; just) public
open import Data.Product hiding (,_) renaming (map to pmap) public

open import OTT.Lib.Heteroindexed public
open import OTT.Lib.Decidable public

open import Relation.Nullary
open import Relation.Binary

infix 4  ,_

pattern ,_ y = _ , y

record ⊤ {α} : Set α where
  constructor tt

⊤₀ : Set
⊤₀ = ⊤

instance
  iprefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  iprefl = prefl

  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y

pright : ∀ {α} {A : Set α} {x y z : A} -> x ≡ y -> x ≡ z -> y ≡ z
pright prefl prefl = prefl

hpcong₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
        -> (f : ∀ x -> B x -> C) -> (q : x₁ ≡ x₂) -> psubst B q y₁ ≡ y₂ -> f x₁ y₁ ≡ f x₂ y₂
hpcong₂ f prefl prefl = prefl

record Apply {α β} {A : Set α} (B : A -> Set β) x : Set β where
  constructor tag
  field detag : B x
open Apply public

tag-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x} {y₁ y₂ : B x}
        -> tag {B = B} y₁ ≡ tag y₂ -> y₁ ≡ y₂
tag-inj prefl = prefl

data Match {ι α} {I : Set ι} {i} (A : I -> Set α) (x : A i) : Set (ι ⊔ₘ α) where
  matched : ∀ {j} -> (x′ : A j) -> [ A ] x ≅ x′ -> Match A x

match : ∀ {ι α} {I : Set ι} {i} -> (A : I -> Set α) -> (x : A i) -> Match A x
match A x = matched x irefl

data IMatch {ι α β} {I : Set ι} {i} (A : I -> Set α) {x : A i} 
            (B : ∀ {i} -> A i -> Set β) (y : B x) : Set (ι ⊔ₘ α ⊔ₘ β) where
  imatched : ∀ {i} {x : A i} -> (y′ : B x) -> [ A ][ B ] y ≅ y′ -> IMatch A B y

imatch : ∀ {ι α β} {I : Set ι} {i}
       -> (A : I -> Set α) {x : A i} -> (B : ∀ {i} -> A i -> Set β) -> (y : B x) -> IMatch A B y
imatch A B y = imatched y iirefl

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
