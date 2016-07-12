module OTT.Data.List where

open import OTT.Core
open import OTT.Coerce
open import OTT.Function.Pi
open import OTT.Function.Elim

infixr 5 _∷_

list : ∀ {a} {α : Level a} -> Univ α -> Type₋₁ α
list A = mu $ π (enum 2) (fromTuple (pos , (A ⇨ pos ⊛ pos)))

List : ∀ {a} {α : Level a} -> Univ α -> Set
List A = ⟦ list A ⟧

pattern []       =  #₀  tt
pattern _∷_ x xs = !#₁ (x , xs , tt)

elimList : ∀ {a π} {α : Level a} {A : Univ α}
         -> (P : List A -> Set π) -> (∀ {xs} x -> P xs -> P (x ∷ xs)) -> P [] -> ∀ xs -> P xs
elimList P f z = elim′ P (fromTuple (z , λ x xs -> f x))

foldList : ∀ {a β} {α : Level a} {A : Univ α} {B : Set β}
         -> (⟦ A ⟧ -> B -> B) -> B -> List A -> B
foldList f = elimList _ f

length : ∀ {a} {α : Level a} {A : Univ α} -> List A -> ℕ
length = foldList (const suc) 0

fromList : ∀ {a} {α : Level a} {A : Univ α} -> (xs : List A) -> Apply Enum (length xs) -> ⟦ A ⟧
fromList xs = go xs ∘ detag where
  go : ∀ {a} {α : Level a} {A : Univ α} -> (xs : List A) -> Enum (length xs) -> ⟦ A ⟧
  go  []           ()
  go (x ∷ [])      tt      = x
  go (x ∷ y ∷ xs)  nothing = x
  go (x ∷ y ∷ xs) (just e) = go (y ∷ xs) e

icmu : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
     -> List (desc I (lsuc α)) -> ⟦ I ⟧ -> Type α
icmu Ds = imu $ π (enum (length Ds)) (fromList Ds)

cmu : ∀ {a} {α : Level a} -> List (desc unit (lsuc α)) -> Type α
cmu Ds = icmu Ds triv

icmu₋₁ : ∀ {i a} {ι : Level i} {I : Type ι}
       -> (α : Level a) -> List (desc₋₁ I α) -> ⟦ I ⟧ -> Type₋₁ α
icmu₋₁ α Ds = imu $ π (enum (length Ds)) (fromList Ds)

cmu₋₁ : ∀ {a} -> (α : Level a) -> List (desc₋₁ unit α) -> Type₋₁ α
cmu₋₁ α Ds = icmu₋₁ α Ds triv
