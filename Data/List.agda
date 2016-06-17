module OTT.Data.List where

open import OTT.Core
open import OTT.Coerce

infixr 5 _∷_

list : ∀ {a} -> Type a -> Type a
list A = mu $ π (enum 2) λ
  { (tag  nothing)  -> pos
  ; (tag (just tt)) -> A ⇨ pos ⊛ pos
  }

List : ∀ {a} -> Type a -> Set
List A = ⟦ list A ⟧

pattern []       = #₀ tt
pattern _∷_ x xs = !#₁ (x , xs , tt)

{-# TERMINATING #-}
elimList : ∀ {a π} {A : Type a}
         -> (P : List A -> Set π) -> (∀ {xs} x -> P xs -> P (x ∷ xs)) -> P [] -> ∀ xs -> P xs
elimList P f z  []      = z
elimList P f z (x ∷ xs) = f x (elimList P f z xs)

foldList : ∀ {a β} {A : Type a} {B : Set β} -> (⟦ A ⟧ -> B -> B) -> B -> List A -> B
foldList f = elimList _ f

length : ∀ {a} {A : Type a} -> List A -> ℕ
length = foldList (const suc) 0

icmu : ∀ {i a} {I : Type i} -> List (desc I (lsuc a)) -> ⟦ I ⟧ -> Type a
icmu {I = I} Ds = imu $ π (enum (length Ds)) (go Ds ∘ detag) where
  go : ∀ {a} {A : Type a} -> (xs : List A) -> Enum (length xs) -> ⟦ A ⟧
  go  []           ()
  go (x ∷ [])      tt      = x
  go (x ∷ y ∷ xs)  nothing = x
  go (x ∷ y ∷ xs) (just e) = go (y ∷ xs) e

cmu : ∀ {a} -> List (desc unit (lsuc a)) -> Type a
cmu Ds = icmu Ds triv
