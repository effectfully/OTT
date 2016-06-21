module OTT.Function.Erase where

open import OTT.Core

data UnitView : ∀ {a} {α : Level a} -> Univ α -> Set where
  yes-unit : UnitView unit
  no-unit  : ∀ {a} {α : Level a} {A : Univ α} -> UnitView A

unitView : ∀ {a} {α : Level a} -> (A : Univ α) -> UnitView A
unitView unit = yes-unit
unitView A    = no-unit

Erase : ∀ {i b} {I : Type i} {β : Level b} -> Desc I β -> Desc unit β
Erase (var i) = pos
Erase (π A D) = π A (λ x -> Erase (D x))
Erase (D ⊛ E) = Erase D ⊛ Erase E

module _ {i b} {I : Type i} {β : Level b} {D : Desc I β} where
  mutual
    eraseSem : (E : Desc I β) -> ⟦ E ⟧ᵈ (μ D) -> ⟦ Erase E ⟧ᵈ (μ (Erase D))
    eraseSem (var i)  d      = erase d
    eraseSem (π A D)  f      = λ x -> eraseSem (D x) (f x)
    eraseSem (D ⊛ E) (r , s) = eraseSem D r , eraseSem E s

    eraseExtend : ∀ {j}
                -> (E : Desc I β) -> Extend E (μ D) j -> Extend (Erase E) (μ (Erase D)) triv
    eraseExtend (var i)  q      = tt
    eraseExtend (π A D) (x , e) = x , eraseExtend (D x) e
    eraseExtend (D ⊛ E) (r , e) = eraseSem D r , eraseExtend E e

    erase : ∀ {j} -> μ D j -> μ (Erase D) triv
    erase (node e) = node (eraseExtend D e)

module _ {i b} {I : Type i} {β : Level b} {B} where
  mutual
    eraseConstSem : (D : Desc I β) -> ⟦ D ⟧ᵈ (const B) -> ⟦ Erase D ⟧ᵈ (const B)
    eraseConstSem (var i)  y      = y
    eraseConstSem (π A D)  f      = λ x -> eraseConstSem (D x) (f x)
    eraseConstSem (D ⊛ E) (x , y) = eraseConstSem D x , eraseConstSem E y

    eraseConstExtend : ∀ {j}
                     -> (D : Desc I β) -> Extend D (const B) j -> Extend (Erase D) (const B) triv
    eraseConstExtend (var i)  q      = tt
    eraseConstExtend (π A D) (x , e) = x , eraseConstExtend (D x) e
    eraseConstExtend (D ⊛ E) (x , e) = eraseConstSem D x , eraseConstExtend E e

module _ {b} {β : Level b} {B : Unit -> Set} where
  mutual
    uneraseSem : (D : Desc unit β) -> ⟦ Erase D ⟧ᵈ B -> ⟦ D ⟧ᵈ B
    uneraseSem (var i)  y      = y
    uneraseSem (π A D)  f      = λ x -> uneraseSem (D x) (f x)
    uneraseSem (D ⊛ E) (x , y) = uneraseSem D x , uneraseSem E y

    uneraseExtend : ∀ {j}
                  -> (D : Desc unit β) -> Extend (Erase D) B j -> Extend D B triv
    uneraseExtend (var i)  q      = tt
    uneraseExtend (π A D) (x , e) = x , uneraseExtend (D x) e
    uneraseExtend (D ⊛ E) (x , e) = uneraseSem D x , uneraseExtend E e

CheckErase : ∀ {i b} {I : Type i} {β : Level b} -> Desc I β -> Desc unit β
CheckErase {I = I} D with unitView I
... | yes-unit = D
... | no-unit  = Erase D

checkErase : ∀ {i b} {I : Type i} {β : Level b} {D : Desc I β} {j}
           -> μ D j -> μ (CheckErase D) triv
checkErase {I = I} d with unitView I
... | yes-unit = d
... | no-unit  = erase d
