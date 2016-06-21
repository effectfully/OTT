module OTT.Data.Fin where

open import OTT.Main

fin : ℕ -> Type₀
fin = icmu
    $ (π nat λ n -> var (suc n))
    ∷ (π nat λ n -> var n ⊛ var (suc n))
    ∷ []

Fin : ℕ -> Set
Fin n = ⟦ fin n ⟧

pattern fzeroₑ {n} q   = #₀  (n , q)
pattern fsucₑ  {n} q i = !#₁ (n , i , q)

fzero : ∀ {n} -> Fin (suc n)
fzero {n} = fzeroₑ {n} (refl (suc n))

fsuc : ∀ {n} -> Fin n -> Fin (suc n)
fsuc {n} = fsucₑ {n} (refl (suc n))

gelimFin : ∀ {n π}
         -> (P : ∀ {n} -> Fin n -> Set π)
         -> (∀ {n m} {i : Fin n} -> (q : ⟦ suc n ≅ m ⟧) -> P i -> P {m} (fsucₑ q i))
         -> (∀ {n m} -> (q : ⟦ suc n ≅ m ⟧) -> P {m} (fzeroₑ q))
         -> (i : Fin n)
         -> P i
gelimFin P f x = gelim P (fromTuple ((λ _ _ -> x) , (λ _ _ r _ q -> f q r)))

foldFin : ∀ {n π} {P : Set π} -> (P -> P) -> P -> Fin n -> P
foldFin f x = gelimFin _ (const f) (const x)

fromFin : ∀ {n} -> Fin n -> ℕ
fromFin = foldFin suc 0

elimFin′ : ∀ {n π}
         -> (P : ∀ n -> Set π)
         -> (∀ {n} {i : Fin n} -> P (fromFin i) -> P (suc (fromFin i)))
         -> P 0
         -> (i : Fin n)
         -> P (fromFin i)
elimFin′ P f x = gelimFin (P ∘ fromFin) (λ {n m i} _ -> f {i = i}) (const x)

elimFin : ∀ {n p} {π : Level p}
        -> (P : ∀ {n} -> Fin n -> Univ π)
        -> (∀ {n} {i : Fin n} -> ⟦ P i ⇒ P (fsuc i) ⟧)
        -> (∀ {n} -> ⟦ P {suc n} fzero ⟧)
        -> (i : Fin n)
        -> ⟦ P i ⟧
elimFin P f x = elim P (fromTuple ((λ _ -> x) , (λ _ _ -> f)))



-- private
--   module Test where
--     -- _+ᶠ_ : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (fromFin i + m)
--     -- i +ᶠ j = elimFin′ (λ n -> Fin (n + _)) fsuc j i 

--     _+ᶠ_ : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (fromFin i + m)
--     i +ᶠ j = elimFin (λ i -> fin (fromFin i + _)) fsuc j i 

--     postulate
--       n m : ℕ

--     test : ⟦ fromFin ((Fin (3 + n) ∋ fsuc (fsuc fzero)) +ᶠ (Fin (2 + m) ∋ fsuc fzero)) ≅ 3 ⟧
--     test = tt
