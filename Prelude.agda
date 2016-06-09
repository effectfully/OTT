module OTT.Prelude where

open import Level renaming (Level to MetaLevel; zero to lzeroₘ; suc to lsucₘ; _⊔_ to _⊔ₘ_) public
open import Function public
open import Relation.Binary.PropositionalEquality
  renaming (refl to prefl; trans to ptrans; cong to pcong) using (_≡_) public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Nat.Base hiding (_⊔_) public
open import Data.Maybe.Base using (Maybe; nothing; just) public
open import Data.Product hiding (,_) renaming (map to pmap) public

infix 4 ,_

pattern ,_ y = _ , y

instance
  iprefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  iprefl = prefl

pright : ∀ {α} {A : Set α} {x y z : A} -> x ≡ y -> x ≡ z -> y ≡ z
pright prefl prefl = prefl

record Apply {α β} {A : Set α} (B : A -> Set β) x : Set β where
  constructor tag
  field detag : B x
open Apply public

record Wrap {α} (A : Set α) : Set α where
  constructor wrap
  field unwrap : A
open Wrap public
