{-# OPTIONS --no-termination-check #-}

module OTT.Coerce where

open import OTT.Prelude
open import OTT.Core

coerceFamℕ : ∀ {n₁ n₂} -> (A : ℕ -> Set) -> ⟦ n₁ ≅ n₂ ⟧ -> A n₁ -> A n₂
coerceFamℕ {0}     {0}     A q  x = x
coerceFamℕ {suc _} {suc _} A q  x = coerceFamℕ (A ∘ suc) q x
coerceFamℕ {0}     {suc _} A () x
coerceFamℕ {suc _} {0}     A () x

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  Coerce : ∀ {a b} {α : Level a} {β : Level b} -> level α ≡ level β -> Univ α -> Univ β
  Coerce {a} {b} {α} {β} q A rewrite trustMe {x = a} {y = b} | trustMe {x = α} {β} = A

mutual
  coerce : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ≈ B ⇒ A ⇒ B ⟧
  coerce {α = lzero } {lzero } (f , _) = f
  coerce {α = lsuc _} {lsuc _}  q      = coerce′ q
  coerce {α = lzero } {lsuc _}  ()
  coerce {α = lsuc _} {lzero }  ()

  coerce′ : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⇒ A ⇒ B ⟧
  coerce′ {A = bot          } {bot          } q ()
  coerce′ {A = top          } {top          } q tt = tt
  -- It's OK to be strict here.
  coerce′ {A = α₁ ≡ˢˡ β₁    } {α₂ ≡ˢˡ β₂    } q p  rewrite proj₁ q | proj₂ q = p
  coerce′ {A = nat          } {nat          } q n  = n
  coerce′ {A = enum n₁      } {enum n₂      } q e  = coerceFamℕ (Apply Enum) q e
  coerce′ {A = univ α₁      } {univ α₂      } q A  = Coerce q A
  coerce′ {A = σ A₁ B₁      } {σ A₂ B₂      } q p  = let q₁ , q₂ = q ; x , y = p in
    coerce q₁ x , coerce (q₂ x (coerce q₁ x) (coherence q₁ x)) y
  coerce′ {A = π A₁ B₁      } {π A₂ B₂      } q f  = let q₁ , q₂ = q in
    λ x -> coerce (q₂ (coerce q₁ x) x (coherence q₁ x)) (f (coerce q₁ x))
  coerce′ {A = udesc _ _ _  } {udesc _ _ _  } q D  = let qI , qo , qa = q in
    coerceUDesc qI (meta-inj qo) (meta-inj qa) D
  coerce′ {A = extend D₁ _ _} {extend D₂ _ _} q e  = let qD , qF , qj = q in
    wrap (coerceExtend D₁ D₂ qD qF qj (unwrap e))
  coerce′ {A = imu _ _      } {imu _ _      } q d  = let qD , qi = q in coerceMu qD qi d
  coerce′ {A = bot          } {top          } ()
  coerce′ {A = bot          } {_ ≡ˢˡ _      } ()
  coerce′ {A = bot          } {nat          } ()
  coerce′ {A = bot          } {enum _       } ()
  coerce′ {A = bot          } {univ _       } ()
  coerce′ {A = bot          } {σ _ _        } ()
  coerce′ {A = bot          } {π _ _        } ()
  coerce′ {A = bot          } {udesc _ _ _  } ()
  coerce′ {A = bot          } {extend _ _ _ } ()
  coerce′ {A = bot          } {imu _ _      } ()
  coerce′ {A = top          } {bot          } ()
  coerce′ {A = top          } {_ ≡ˢˡ _      } ()
  coerce′ {A = top          } {nat          } ()
  coerce′ {A = top          } {enum _       } ()
  coerce′ {A = top          } {univ _       } ()
  coerce′ {A = top          } {σ _ _        } ()
  coerce′ {A = top          } {π _ _        } ()
  coerce′ {A = top          } {udesc _ _ _  } ()
  coerce′ {A = top          } {extend _ _ _ } ()
  coerce′ {A = top          } {imu _ _      } ()
  coerce′ {A = _ ≡ˢˡ _      } {bot          } ()
  coerce′ {A = _ ≡ˢˡ _      } {top          } ()
  coerce′ {A = _ ≡ˢˡ _      } {nat          } ()
  coerce′ {A = _ ≡ˢˡ _      } {enum _       } ()
  coerce′ {A = _ ≡ˢˡ _      } {univ _       } ()
  coerce′ {A = _ ≡ˢˡ _      } {σ _ _        } ()
  coerce′ {A = _ ≡ˢˡ _      } {π _ _        } ()
  coerce′ {A = _ ≡ˢˡ _      } {udesc _ _ _  } ()
  coerce′ {A = _ ≡ˢˡ _      } {extend _ _ _ } ()
  coerce′ {A = _ ≡ˢˡ _      } {imu _ _      } ()
  coerce′ {A = nat          } {bot          } ()
  coerce′ {A = nat          } {top          } ()
  coerce′ {A = nat          } {_ ≡ˢˡ _      } ()
  coerce′ {A = nat          } {enum _       } ()
  coerce′ {A = nat          } {univ _       } ()
  coerce′ {A = nat          } {σ _ _        } ()
  coerce′ {A = nat          } {π _ _        } ()
  coerce′ {A = nat          } {udesc _ _ _  } ()
  coerce′ {A = nat          } {extend _ _ _ } ()
  coerce′ {A = nat          } {imu _ _      } ()
  coerce′ {A = enum _       } {bot          } ()
  coerce′ {A = enum _       } {top          } ()
  coerce′ {A = enum _       } {_ ≡ˢˡ _      } ()
  coerce′ {A = enum _       } {nat          } ()
  coerce′ {A = enum _       } {univ _       } ()
  coerce′ {A = enum _       } {σ _ _        } ()
  coerce′ {A = enum _       } {π _ _        } ()
  coerce′ {A = enum _       } {udesc _ _ _  } ()
  coerce′ {A = enum _       } {extend _ _ _ } ()
  coerce′ {A = enum _       } {imu _ _      } ()
  coerce′ {A = univ _       } {bot          } ()
  coerce′ {A = univ _       } {top          } ()
  coerce′ {A = univ _       } {_ ≡ˢˡ _      } ()
  coerce′ {A = univ _       } {nat          } ()
  coerce′ {A = univ _       } {enum _       } ()
  coerce′ {A = univ _       } {σ _ _        } ()
  coerce′ {A = univ _       } {π _ _        } ()
  coerce′ {A = univ _       } {udesc _ _ _  } ()
  coerce′ {A = univ _       } {extend _ _ _ } ()
  coerce′ {A = univ _       } {imu _ _      } ()
  coerce′ {A = σ _ _        } {bot          } ()
  coerce′ {A = σ _ _        } {top          } ()
  coerce′ {A = σ _ _        } {_ ≡ˢˡ _      } ()
  coerce′ {A = σ _ _        } {nat          } ()
  coerce′ {A = σ _ _        } {enum _       } ()
  coerce′ {A = σ _ _        } {univ _       } ()
  coerce′ {A = σ _ _        } {π _ _        } ()
  coerce′ {A = σ _ _        } {udesc _ _ _  } ()
  coerce′ {A = σ _ _        } {extend _ _ _ } ()
  coerce′ {A = σ _ _        } {imu _ _      } ()
  coerce′ {A = π _ _        } {bot          } ()
  coerce′ {A = π _ _        } {top          } ()
  coerce′ {A = π _ _        } {_ ≡ˢˡ _      } ()
  coerce′ {A = π _ _        } {nat          } ()
  coerce′ {A = π _ _        } {enum _       } ()
  coerce′ {A = π _ _        } {univ _       } ()
  coerce′ {A = π _ _        } {σ _ _        } ()
  coerce′ {A = π _ _        } {udesc _ _ _  } ()
  coerce′ {A = π _ _        } {extend _ _ _ } ()
  coerce′ {A = π _ _        } {imu _ _      } ()
  coerce′ {A = udesc _ _ _  } {bot          } ()
  coerce′ {A = udesc _ _ _  } {top          } ()
  coerce′ {A = udesc _ _ _  } {_ ≡ˢˡ _      } ()
  coerce′ {A = udesc _ _ _  } {nat          } ()
  coerce′ {A = udesc _ _ _  } {enum _       } ()
  coerce′ {A = udesc _ _ _  } {univ _       } ()
  coerce′ {A = udesc _ _ _  } {σ _ _        } ()
  coerce′ {A = udesc _ _ _  } {π _ _        } ()
  coerce′ {A = udesc _ _ _  } {extend _ _ _ } ()
  coerce′ {A = udesc _ _ _  } {imu _ _      } ()
  coerce′ {A = extend _ _ _ } {bot          } ()
  coerce′ {A = extend _ _ _ } {top          } ()
  coerce′ {A = extend _ _ _ } {_ ≡ˢˡ _      } ()
  coerce′ {A = extend _ _ _ } {nat          } ()
  coerce′ {A = extend _ _ _ } {enum _       } ()
  coerce′ {A = extend _ _ _ } {univ _       } ()
  coerce′ {A = extend _ _ _ } {σ _ _        } ()
  coerce′ {A = extend _ _ _ } {π _ _        } ()
  coerce′ {A = extend _ _ _ } {udesc _ _ _  } ()
  coerce′ {A = extend _ _ _ } {imu _ _      } ()
  coerce′ {A = imu _ _      } {bot          } ()
  coerce′ {A = imu _ _      } {top          } ()
  coerce′ {A = imu _ _      } {_ ≡ˢˡ _      } ()
  coerce′ {A = imu _ _      } {nat          } ()
  coerce′ {A = imu _ _      } {enum _       } ()
  coerce′ {A = imu _ _      } {univ _       } ()
  coerce′ {A = imu _ _      } {σ _ _        } ()
  coerce′ {A = imu _ _      } {π _ _        } ()
  coerce′ {A = imu _ _      } {udesc _ _ _  } ()
  coerce′ {A = imu _ _      } {extend _ _ _ } ()
  -- generated by http://ideone.com/ltrf04

  coerceUDesc : ∀ {i₁ i₂ o₁ o₂ a₁ a₂} {ω₁ : Level o₁} {ω₂ : Level o₂} {I₁ : Type i₁} {I₂ : Type i₂}
              -> ⟦ I₁ ≃ I₂ ⟧ -> o₁ ≡ o₂ -> a₁ ≡ a₂ -> UDesc I₁ ω₁ a₁ -> UDesc I₂ ω₂ a₂
  coerceUDesc qI qo qa (var[ q ] j)     = var[ pright qo (ptrans q qa) ] (coerce qI j)
  coerceUDesc qI qo qa (π[_] {a} q A D) =
    π[ ptrans (pright (pcong (a ⊔ₘ_) qo) q) qa ] A (coerceUDesc qI qo qa ∘ D)
  coerceUDesc qI qo qa (D ⊛ E)          = coerceUDesc qI qo qa D ⊛ coerceUDesc qI qo qa E
  
  coerceSem : ∀ {i₁ i₂ o₁ o₂ a₁ a₂ b₁ b₂}
                {ω₁ : Level o₁} {ω₂ : Level o₂} {β₁ : Level b₁} {β₂ : Level b₂}
                {I₁ : Type i₁} {I₂ : Type i₂}
                {F₁ : ⟦ I₁ ⟧ -> Univ β₁} {F₂ : ⟦ I₂ ⟧ -> Univ β₂}
            -> (D₁ : UDesc I₁ ω₁ a₁)
            -> (D₂ : UDesc I₂ ω₂ a₂)
            -> ⟦ D₁ ≅ᵈ D₂ ⟧
            -> ⟦ F₁ ≅ F₂ ⟧
            -> (⟦ D₁ ⟧ᵈ λ x₁ -> ⟦ F₁ x₁ ⟧)
            -> (⟦ D₂ ⟧ᵈ λ x₂ -> ⟦ F₂ x₂ ⟧)
  coerceSem (var′ j₁)  (var′ j₂)   qj       qF  x      = coerce (qF j₁ j₂ qj) x
  coerceSem (π′ A₁ D₁) (π′ A₂ D₂) (qA , qD) qF  f      = λ x ->
    let qA′ = sym A₁ {A₂} qA
        x′  = coerce qA′ x
    in coerceSem (D₁ x′) (D₂ x) (qD x′ x (sym x (coherence qA′ x))) qF (f x′)
  coerceSem (D₁ ⊛ E₁)  (D₂ ⊛ E₂)  (qD , qE) qF (s , t) =
    coerceSem D₁ D₂ qD qF s , coerceSem E₁ E₂ qE qF t
  coerceSem (var′ _) (π′ _ _) ()
  coerceSem (var′ _) (_ ⊛ _ ) ()
  coerceSem (π′ _ _) (var′ _) ()
  coerceSem (π′ _ _) (_ ⊛ _ ) ()
  coerceSem (_ ⊛ _ ) (var′ _) ()
  coerceSem (_ ⊛ _ ) (π′ _ _) ()

  coerceExtend : ∀ {i₁ i₂ o₁ o₂ a₁ a₂ b₁ b₂}
                   {ω₁ : Level o₁} {ω₂ : Level o₂} {β₁ : Level b₁} {β₂ : Level b₂}
                   {I₁ : Type i₁} {I₂ : Type i₂}
                   {F₁ : ⟦ I₁ ⟧ -> Univ β₁} {F₂ : ⟦ I₂ ⟧ -> Univ β₂} {j₁ j₂}
               -> (D₁ : UDesc I₁ ω₁ a₁)
               -> (D₂ : UDesc I₂ ω₂ a₂)
               -> ⟦ D₁ ≅ᵈ D₂ ⟧
               -> ⟦ F₁ ≅ F₂ ⟧
               -> ⟦ j₁ ≅ j₂ ⟧
               -> Extend D₁ (λ x₁ -> ⟦ F₁ x₁ ⟧) j₁
               -> Extend D₂ (λ x₂ -> ⟦ F₂ x₂ ⟧) j₂
  coerceExtend (var′ j₁)  (var′ j₂)   qj       qF qi  qji    = trans j₂ (right j₁ qj qji) qi
  coerceExtend (π′ A₁ D₁) (π′ A₂ D₂) (qA , qD) qF qi (x , e) = let x′ = coerce qA x in
    x′ , coerceExtend (D₁ x) (D₂ x′) (qD x x′ (coherence qA x)) qF qi e
  coerceExtend (D₁ ⊛ E₁ ) (D₂ ⊛ E₂ ) (qD , qE) qF qi (s , e) =
    coerceSem D₁ D₂ qD qF s , coerceExtend E₁ E₂ qE qF qi e
  coerceExtend (var′ _) (π′ _ _) ()
  coerceExtend (var′ _) (_ ⊛ _ ) ()
  coerceExtend (π′ _ _) (var′ _) ()
  coerceExtend (π′ _ _) (_ ⊛ _ ) ()
  coerceExtend (_ ⊛ _ ) (var′ _) ()
  coerceExtend (_ ⊛ _ ) (π′ _ _) ()

  coerceMu : ∀ {i₁ i₂ a₁ a₂} {α₁ : Level a₁} {α₂ : Level a₂}
               {I₁ : Type i₁} {I₂ : Type i₂} {D₁ : Desc I₁ α₁} {D₂ : Desc I₂ α₂} {j₁ j₂}
           -> ⟦ D₁ ≊ᵈ D₂ ⟧ -> ⟦ j₁ ≅ j₂ ⟧ -> μ D₁ j₁ -> μ D₂ j₂     
  coerceMu {α₁ = lzero } {lzero }                qD qj (node e) =
    node (unwrap (proj₁ (qD _ _ qj) (wrap e)))
  coerceMu {α₁ = lsuc _} {lsuc _} {D₁ = D₁} {D₂} qD qj (node e) =
    node (coerceExtend D₁ D₂ qD (λ _ _ -> _,_ qD) qj e)
  coerceMu {α₁ = lzero } {lsuc _} ()
  coerceMu {α₁ = lsuc _} {lzero } ()

  postulate
    refl      : ∀ {a} {α : Level a} {A : Univ α} -> (x : ⟦ A ⟧) -> ⟦ x ≅ x ⟧
    coherence : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
              -> (q : ⟦ A ≈ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≅ coerce q x ⟧
    cong-≅z   : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c}
                  {A : Univ α} {B : Univ β} {C : Univ γ}
              -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ (x ≅ z) ≈ (y ≅ z)⟧
    huip      : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
              -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ refl x ≅ q ⟧

  right : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c}
            {A : Univ α} {B : Univ β} {C : Univ γ}
        -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ x ≅ z ⟧ -> ⟦ y ≅ z ⟧
  right x q₁ = proj₁ (cong-≅z x q₁)

  trans : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c}
            {A : Univ α} {B : Univ β} {C : Univ γ}
        -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ y ≅ z ⟧ -> ⟦ x ≅ z ⟧
  trans x {y} q₁ = proj₂ (cong-≅z x q₁)

  sym : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
      -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ y ≅ x ⟧
  sym x q = right x q (refl x)

  left : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c}
           {A : Univ α} {B : Univ β} {C : Univ γ}
       -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ z ≅ y ⟧ -> ⟦ x ≅ z ⟧
  left x {z = z} q₁ q₂ = trans x q₁ (sym z q₂)

subst : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {x y}
      -> (B : ⟦ A ⟧ -> Univ β) -> ⟦ x ≅ y ⇒ B x ⇒ B y ⟧
subst B q = coerce (refl B _ _ q)

subst₂ : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c} {A : Univ α}
           {B : ⟦ A ⟧ -> Univ β} {x₁ x₂} {y₁ : ⟦ B x₁ ⟧} {y₂ : ⟦ B x₂ ⟧}
       -> (C : ∀ x -> ⟦ B x ⟧ -> Univ γ) -> ⟦ x₁ ≅ x₂ ⇒ y₁ ≅ y₂ ⇒ C x₁ y₁ ⇒ C x₂ y₂ ⟧
subst₂ C q₁ q₂ = coerce (refl C _ _ q₁ _ _ q₂)

J : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {x y : ⟦ A ⟧}
  -> (B : (y : ⟦ A ⟧) -> ⟦ x ≅ y ⟧ -> Univ β)
  -> ⟦ B _ (refl x) ⟧
  -> (q : ⟦ x ≅ y ⟧)
  -> ⟦ B _ q ⟧
J {x = x} B z q = subst₂ B q (huip x q) z
