module OTT.Data.Vec where

open import OTT.Main
open import OTT.Data.Fin

infixr 5 _∷ᵥ_

vec : ∀ {a} {α : Level a} -> Univ α -> ℕ -> Type₋₁ α
vec {α = α} A = icmu₋₁ α
              $ var 0
              ∷ (π nat λ n -> A ⇨ var n ⊛ var (suc n))
              ∷ []

Vec : ∀ {a} {α : Level a} -> Univ α -> ℕ -> Set
Vec A n = ⟦ vec A n ⟧

pattern vnilₑ      q      =  #₀  q
pattern vconsₑ {n} q x xs = !#₁ (n , x , xs , q)

[]ᵥ : ∀ {a} {α : Level a} {A : Univ α} -> Vec A 0
[]ᵥ = vnilₑ (refl 0)

_∷ᵥ_ : ∀ {n a} {α : Level a} {A : Univ α} -> ⟦ A ⇒ vec A n ⇒ vec A (suc n) ⟧
_∷ᵥ_ {n} = vconsₑ (refl (suc n))

gelimVec : ∀ {n a π} {α : Level a} {A : Univ α}
         -> (P : ∀ {n} -> Vec A n -> Set π)
         -> (∀ {n m} {xs : Vec A n}
               -> (q : ⟦ suc n ≅ m ⟧) -> (x : ⟦ A ⟧) -> P xs -> P {m} (vconsₑ q x xs))
         -> (∀ {m} -> (q : ⟦ 0 ≅ m ⟧) -> P {m} (vnilₑ q))
         -> (xs : Vec A n)
         -> P xs
gelimVec P f z = gelim P (fromTuple ((λ _ -> z) , (λ n x xs r _ q -> f q x r)))

foldVec : ∀ {n a π} {α : Level a} {A : Univ α} {P : Set π}
        -> (⟦ A ⟧ -> P -> P) -> P -> Vec A n -> P
foldVec f z = gelimVec _ (const f) (const z)

fromVec : ∀ {n a} {α : Level a} {A : Univ α} -> Vec A n -> List A
fromVec = foldVec _∷_ []

elimVec′ : ∀ {n a π} {α : Level a} {A : Univ α}
         -> (P : List A -> Set π)
         -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> P (fromVec xs) -> P (x ∷ fromVec xs))
         -> P []
         -> (xs : Vec A n)
         -> P (fromVec xs)
elimVec′ P f z = gelimVec (P ∘ fromVec) (λ {n m xs} _ -> f {xs = xs}) (const z)

elimVec : ∀ {n a p} {α : Level a} {π : Level p} {A : Univ α}
        -> (P : ∀ {n} -> Vec A n -> Univ π)
        -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> ⟦ P xs ⇒ P (x ∷ᵥ xs) ⟧)
        -> ⟦ P []ᵥ ⟧
        -> (xs : Vec A n)
        -> ⟦ P xs ⟧
elimVec P f z = elim P (fromTuple (z , λ n x xs -> f x))

vlookupₑ : ∀ {n m a} {α : Level a} {A : Univ α} -> ⟦ n ≅ m ⇒ fin n ⇒ vec A m ⇒ A ⟧
vlookupₑ         p (fzeroₑ q)       (vconsₑ r x xs)      = x
vlookupₑ {n} {m} p (fsucₑ {n′} q i) (vconsₑ {m′} r x xs) =
  vlookupₑ (left (suc n′) {m} {suc m′} (trans (suc n′) {n} {m} q p) r) i xs
vlookupₑ {n} {m} p (fzeroₑ {n′} q)  (vnilₑ r)            =
  ⊥-elim $ left (suc n′) {m} {0} (trans (suc n′) {n} {m} q p) r
vlookupₑ {n} {m} p (fsucₑ {n′} q i) (vnilₑ r)            =
  ⊥-elim $ left (suc n′) {m} {0} (trans (suc n′) {n} {m} q p) r

vlookup : ∀ {n a} {α : Level a} {A : Univ α} -> Fin n -> Vec A n -> ⟦ A ⟧
vlookup {n} = vlookupₑ (refl n)
