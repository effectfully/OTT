module OTT.Data.Fin where

open import OTT.Core
open import OTT.Coerce

fin : ℕ -> Type
fin = rose ((, nat , λ m -> [] , suc m) ∷ (, nat , λ m -> m ∷ [] , suc m) ∷ [])

Fin : ℕ -> Set
Fin n = ⟦ fin n ⟧

fzeroₑ : ∀ {n m} -> ⟦ suc n ≅ m ⟧ -> Fin m
fzeroₑ {n} q = node (here (n , [] , q))

fsucₑ : ∀ {n m} -> ⟦ suc n ≅ m ⟧ -> Fin n -> Fin m
fsucₑ {n} q i = node (there (here (n , i ∷ [] , q)))

fzero : ∀ {n} -> Fin (suc n)
fzero {n} = fzeroₑ {n} (refl (suc n))

fsuc : ∀ {n} -> Fin n -> Fin (suc n)
fsuc {n} = fsucₑ {n} (refl (suc n))

elimFinₑ : ∀ {n π}
         -> (P : ∀ {n} -> Fin n -> Set π)
         -> (∀ {n m} {i : Fin n} -> (q : ⟦ suc n ≅ m ⟧) -> P i -> P {m} (fsucₑ q i))
         -> (∀ {n m} -> (q : ⟦ suc n ≅ m ⟧) -> P {m} (fzeroₑ q))
         -> (i : Fin n)
         -> P i
elimFinₑ P f x (node (here  (m , [] , q)))            = x q
elimFinₑ P f x (node (there (here (m , i ∷ [] , q)))) = f q (elimFinₑ P f x i)
elimFinₑ P f x (node (there (there ())))

foldFin : ∀ {n π} {P : Set π} -> (P -> P) -> P -> Fin n -> P
foldFin f x = elimFinₑ _ (const f) (const x)

fromFin : ∀ {n} -> Fin n -> ℕ
fromFin = foldFin suc 0

elimFin′ : ∀ {n π}
         -> (P : ∀ n -> Set π)
         -> (∀ {n} {i : Fin n} -> P (fromFin i) -> P (suc (fromFin i)))
         -> P 0
         -> (i : Fin n)
         -> P (fromFin i)
elimFin′ P f x = elimFinₑ (P ∘ fromFin) (λ {n m i} _ -> f {i = i}) (const x)

elimFin : ∀ {n k}
        -> (P : ∀ {n} -> Fin n -> Univ k)
        -> (∀ {n} {i : Fin n} -> ⟦ P i ⇒ P (fsuc i) ⟧)
        -> (∀ {n} -> ⟦ P {suc n} fzero ⟧)
        -> (i : Fin n)
        -> ⟦ P i ⟧
elimFin P f x = elimFinₑ (⟦_⟧ ∘ P)
  (λ {n m i} q r -> subst₂ (λ m q -> P {m} (fsucₑ q i)) q (huip (suc n) m q) (f r))
  (λ {n m}   q   -> subst₂ (λ m q -> P {m} (fzeroₑ q))  q (huip (suc n) m q)  x)



-- _+ᶠ_ : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (fromFin i + m)
-- i +ᶠ j = elimFin′ (λ n -> Fin (n + _)) fsuc j i 

_+ᶠ_ : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (fromFin i + m)
i +ᶠ j = elimFin (λ i -> fin (fromFin i + _)) fsuc j i 

postulate
  n m : ℕ

test : ⟦ fromFin ((Fin (3 + n) ∋ fsuc (fsuc fzero)) +ᶠ (Fin (2 + m) ∋ fsuc fzero)) ≅ 3 ⟧
test = tt
