module OTT.Prelude where

open import Function public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base public
open import Data.List.Base hiding (zip) renaming (map to lmap) public
open import Data.List.Any using (Any; here; there) public
open import Data.List.All using (All; []; _∷_) public
open import Data.Product hiding (,_) renaming (map to pmap) public

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Fin hiding (#_; _+_)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to fmap)

infix  4 ,_
infixl 7 _^_
infixl 1 _>>=ᵀ_ _>>=ᵗ_
infixl 4 _!!_

pattern ,_ y = _ , y

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = A
A ^ suc n = A × A ^ n

toList : ∀ {α} {A : Set α} n -> A ^ n -> List A
toList  0       x       = x ∷ []
toList (suc n) (x , xs) = x ∷ toList n xs

_>>=ᵀ_ : ∀ {α β} {A : Set α} -> Maybe A -> (A -> Set β) -> Set β
nothing >>=ᵀ B = Lift ⊤
just x  >>=ᵀ B = B x

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β} mx -> (∀ x -> B x) -> mx >>=ᵀ B
nothing >>=ᵗ f = _
just x  >>=ᵗ f = f x

tryFromℕ : ∀ {m} -> ℕ -> Maybe (Fin m)
tryFromℕ {0}      n      = nothing
tryFromℕ {suc m}  0      = just zero
tryFromℕ {suc m} (suc n) = fmap suc (tryFromℕ n)

_!!_ : ∀ {α} {A : Set α} -> (xs : List A) -> Fin (length xs) -> A
[]     !! ()
x ∷ xs !! zero  = x
x ∷ xs !! suc i = xs !! i

injAt⁺ : ∀ {α π} {A : Set α} {P : A -> Set π} {ys} xs i -> P (xs !! i) -> Any P (xs ++ ys)
injAt⁺  []       ()     p
injAt⁺ (x ∷ xs)  zero   p = here p
injAt⁺ (x ∷ xs) (suc i) p = there (injAt⁺ xs i p)

module _ {α π} {A : Set α} {P : A -> Set π} n {p : A ^ n} where
  infix 2 _#_

  xs = toList n p

  _#_ : tryFromℕ n >>=ᵀ λ i -> ∀ {ys} -> P (xs !! i) -> Any P (xs ++ ys)
  _#_ = tryFromℕ n >>=ᵗ λ i {_} -> injAt⁺ xs i
