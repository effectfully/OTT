module OTT.Lib.Heteroindexed where

open import Relation.Binary.PropositionalEquality
open import Data.Product

data [_]_≅_ {ι α} {I : Set ι} {i} (A : I -> Set α) (x : A i) : ∀ {j} -> A j -> Set where
  irefl : [ A ] x ≅ x

inds : ∀ {ι α} {I : Set ι} {A : I -> Set α} {i j} {x : A i} {y : A j}
     -> [ A ] x ≅ y -> i ≡ j
inds irefl = refl

homo : ∀ {ι α} {I : Set ι} {A : I -> Set α} {i} {x y : A i}
     -> [ A ] x ≅ y -> x ≡ y
homo irefl = refl

inds-homo : ∀ {ι α} {I : Set ι} {A : Set α} {i j : I} {x y : A}
          -> [_]_≅_ {i = i} (λ _ -> A) x {j} y -> i ≡ j × x ≡ y
inds-homo irefl = refl , refl
