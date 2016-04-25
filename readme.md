# OTT

It's an implementation of Observational Type Theory as an Agda library. The universe contains `⊤` (one in `Prop` and one in `Type`), `⊥`, natural numbers, two impredicative universes (`Prop` (OK) and `Type` (not OK)), Σ- and Π-types, lists and allows generic programming via the `rose` construct.

## Implemented

 - Equality for propositions is isomorphism. Equal types are equal either weakly

 ```
 _≈_  : ∀ {k s} -> Univ k -> Univ s -> Prop
 _≈_ {false} {false} A₁ A₂ = A₁ ⇒ A₂ & A₂ ⇒ A₁
 _≈_ {true } {true } A₁ A₂ = A₁ ≃ A₂
 _≈_                 _  _  = bot
 ```

 or strictly

 ```
 _≃_  : ∀ {k s} -> Univ k -> Univ s -> Prop
 bot     ≃ bot     = top
 top     ≃ top     = top
 σ A₁ B₁ ≃ σ A₂ B₂ = A₁ ≈ A₂ & B₁ ≅ B₂
 ...
 ```

 This way we can avoid explicit liftings of propositions into `Type`, which introduce ambiguity (`lift A ⇒ lift B` has the same meaning as `lift (A ⇒ B)`, but the codes are different). But clearly we want cumulativity, so this is not a proper solution.

 Correspondingly, there are two `coerce`s: one which requires weak equality

 ```
 coerce : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ≈ B ⇒ A ⇒ B ⟧
 ```

 and one which requires strict

 ```
 coerce′ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ≃ B ⇒ A ⇒ B ⟧
 ```

 - `rose` allows to define inductive data types (including inductive families) in the target theory. `coerce` computes under constructors of any inductive family defined in terms of `rose`. This is achieved via the trick described in the section 5 of [1]. `rose` also allows to define eliminators of data types (even in an intensional type theory). Each inductive family has at least two eliminators: one classical and one "up to propositional equality". An example from the `OTT.Data.Fin` module:

 ```
 elimFinₑ : ∀ {n π}
          -> (P : ∀ {n} -> Fin n -> Set π)
          -> (∀ {n m} {i : Fin n} -> (q : ⟦ suc n ≅ m ⟧) -> P i -> P {m} (fsucₑ q i))
          -> (∀ {n m} -> (q : ⟦ suc n ≅ m ⟧) -> P {m} (fzeroₑ q))
          -> (i : Fin n)
          -> P i
 elimFinₑ P f x (fzeroₑ q)  = x q
 elimFinₑ P f x (fsucₑ q i) = f q (elimFinₑ P f x i)
 elimFinₑ P f x  ⟨⟩₂

 ```

 `elimFinₑ` is an "up to propositional equality" eliminator. The thing here is that `elimFinₑ` doesn't contain any coercions at all, so its "non-dependent" computational behaviour is the same as the corresponding behaviour of an eliminator in an intensional type theory. It even gives you slightly more:

 ```
 elimFin′ : ∀ {n π}
          -> (P : ∀ n -> Set π)
          -> (∀ {n} {i : Fin n} -> P (fromFin i) -> P (suc (fromFin i)))
          -> P 0
          -> (i : Fin n)
          -> P (fromFin i)
 elimFin′ P f x = elimFinₑ (P ∘ fromFin) (λ {n m i} _ -> f {i = i}) (const x)
 ```

 `elimFin′` doesn't mention `coerce` as well.

 We can recover the usual eliminator with the help from our old friend (something strange is happening with the markdown)

 ```
 J : ∀ {k s} {A : Univ k} {x y : ⟦ A ⟧}
   -> (P : (y : ⟦ A ⟧) -> ⟦ x ≅ y ⟧ -> Univ s)
   -> ⟦ P _ (refl x) ⟧
   -> (q : ⟦ x ≅ y ⟧)
   -> ⟦ P _ q ⟧
 J {x = x} P z q = subst₂ P q (huip x q) z

 elimFin : ∀ {n k}
         -> (P : ∀ {n} -> Fin n -> Univ k)
         -> (∀ {n} {i : Fin n} -> ⟦ P i ⇒ P (fsuc i) ⟧)
         -> (∀ {n} -> ⟦ P {suc n} fzero ⟧)
         -> (i : Fin n)
         -> ⟦ P i ⟧
 elimFin P f x = elimFinₑ (⟦_⟧ ∘ P)
   (λ q r -> J (λ m q -> P {m} (fsucₑ q _)) (f r) q)
   (J (λ m q -> P {m} (fzeroₑ q)) x)
 ```

 `subst₂` is defined in terms of `coerce`, so it computes under constructors of data types, hence classical eliminators have pretty good computational behaviour too.

 A simple test:

 ```
 postulate
   n m : ℕ

 test : ⟦ fromFin ((Fin (3 + n) ∋ fsuc (fsuc fzero)) +ᶠ (Fin (2 + m) ∋ fsuc fzero)) ≅ 3 ⟧
 test = tt
 ```

 `n` and `m` are stuck, but the expression reduces properly regardless of whether `_+ᶠ_` is defined in terms of `elimFin′` or `elimFin`.

 Eliminators for inductive data types (not families) are the usual intensional eliminators, e.g.

 ```
 [_,_] : ∀ {k s π} {A : Univ k} {B : Univ s} {P : A ⊎ B -> Set π}
       -> (∀ x -> P (inj₁ x)) -> (∀ y -> P (inj₂ y)) -> ∀ s -> P s
 [ f , g ] (inj₁ x) = f x
 [ f , g ] (inj₂ y) = g y
 [ f , g ]  ⟨⟩₂

 elimW : ∀ {π A} {B : ⟦ A ⟧ -> Type}
       -> (P : W A B -> Set π)
       -> (∀ {x} {g : ⟦ B x ⟧ -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
       -> ∀ w
       -> P w
 elimW P h (sup x g) = h (λ y -> elimW P h (g y))
 elimW P h  ⟨⟩₁
 ```

 To define a data type you need to define a description. Each description is a list of constructors. Each constructor is a telescope that ends with a list of inductive occurences and the final index that the constructor produces. Each inductive occurence is itself a telescope which allows to put the inductive position to the right of the arrow, i.e. to describe data types like `W`. The code looks like this:

 ```
 data Tele (B : Set) : Set where
  ret : B -> Tele B
  pi  : ∀ {k} -> (A : Univ k) -> (⟦ A ⟧ -> Tele B) -> Tele B

 Cons : Type -> Set
 Cons I = Tele (List (Tele ⟦ I ⟧) × ⟦ I ⟧)

 Desc : Type -> Set
 Desc = List ∘ Cons
 ```

 `rose` then ties the know and connect the constructor together. An example:

 ```
 vec : ∀ {k} -> Univ k -> ℕ -> Type
 vec A = rose $ ret ([] , 0) ∷ (pi nat λ n -> A ⇨ ret (ret n ∷ [] , suc n)) ∷ []

 Vec : ∀ {k} -> Univ k -> ℕ -> Set
 Vec A n = ⟦ vec A n ⟧
 ```

 Vectors have two constructors: `[]` and `_∷_`. The first constructor produces index `0` and doesn't contain any data indcluding inductive occurences. The second constructor produces index `suc n`, carries an `A` and an inductive occurence.

 Another example:

 ```
 w : (A : Type) -> (⟦ A ⟧ -> Type) -> Type
 w A B = rose ((pi A λ x -> ret ((B x ⇨ ret triv) ∷ [] , triv)) ∷ []) triv

 W : (A : Type) -> (⟦ A ⟧ -> Type) -> Set
 W A B = ⟦ w A B ⟧
 ```

 `W` is a non-indexed data types, hence the `triv` everywhere. `W` has one constructor:

 ```
 sup : (x : A) -> (B x -> W A B) -> W A B
 ```

 so there one inductive occurence where the inductive position occurs to the right of the arrow. This is encoded as `(B x ⇨ ret triv) ∷ []`.

 An example of generic programming can be found in the `OTT.Property.Showable` module:

 ```
 instance
   named-vec : {A : Type} -> Named (vec-cs A)
   named-vec = record { names = "nil" ∷ "cons" ∷ [] }

 test₂ : show (Vec (nat & nat) 3 ∋ (7 , 8) ∷ᵥ (9 , 10) ∷ᵥ (11 , 12) ∷ᵥ []ᵥ)
       ≡ "(cons 2 (7 , 8) (cons 1 (9 , 10) (cons 0 (11 , 12) nil)))"
 test₂ = prefl
 ```

 I.e. to be able to print a vector all you need is to name the constructors.

 A model of the model can be found [here](https://github.com/effectfully/random-stuff/blob/master/Rose/Coercible.agda) (it's slightly weaker, though, as it doesn't allow to describe `W` and similar data types in which an inductive position occurs to the right of the arrow in a parameter of a constructor).

 There is [an alternative encoding](https://github.com/effectfully/random-stuff/blob/master/IRDesc.agda) in terms of proper propositional descriptions (see [6]), which is a slightly modified version of [7]. It's more standard, more powerful (it's able to express induction-recursion), but also significantly more complicated: data types must be defined mutually with coercions (or maybe we can to use a parametrised module like in the model, but it still doesn't look nice), which results in a giant mutual block. I didn't try to define equality and coercions for descriptions, but I suspect it's much harder than how it's now. I'll go with the current simple approach.

 In the levitation paper ([8]) they don't have lists at all, but instead use finite enumerations. We can't define `Desc I = Tele (Tele I × I)`, because a non-recursive constructor doesn't return a `Tele I` and we can't use `empty = pi ⊥ ⊥-elim`, because it's too extensional.

 I don't like computational descriptions, because explicit unification constraints are ugly. I don't like propositional descriptions, because `B` in `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I` is not a proper telescope and I don't want to manually extract elements from a big tuple that can appear in the place of `A`. I don't like the encoding presented here, because those lists look redundant. The encoding I like currently is [computational descriptions used as propositional desciptions](https://github.com/effectfully/random-stuff/blob/master/CompPropDesc.agda).

 But who said that we should entirely exclude non-strictly-positive data types?

## Not implemented

- Universe hierarchy. We want a universe hierarchy with the following properties:

  1. predicativity
  2. cumulativity
  3. non-redundancy
  4. `⟦ type n ⟧ ≡ Type n` for neutral `n`
  5. easy to use
  
  I'm not aware of such encoding. The best seems to be [3], but as far as I understand only (1) and (2) hold for it. It's probably possible to add (4) by introducing a super universe in the style of [5] like [this](https://github.com/effectfully/random-stuff/blob/master/Omega.agda).

- Definitional proof irrelevance.

- Erasion of stuck coercions between definitionally equal types (that's not my fault, Agda just doesn't have an available definitional equality checker) (note that we have proper eliminators without this tool unlike in OTT with W-types (and they are still improper, see [4])).

- Codata (is it simply the coinductive counterpart of `rose`?).

## Remarks

Originally I added the codes for `All` and `Any` (both were explicit-unification-constraints-transformed to make them appropriately coercible) to the universe, but it's very (**very**) annoying to define eliminators with such machinery, so I switched to a simpler one. We could add codes for `All` and `Any` without transforming the corresponding data types and even derive equality and coercions for `rose` from them, but it's nearly impossible to understand the behaviour of `coerce` then:

```
coerceChilds : ∀ {I₁ I₂} {cs₁ : Desc I₁} {cs₂ : Desc I₂} {i₂ i₁}
             -> ⟦ rose cs₁ i₁ ≅ rose cs₂ i₂ ⟧ -> Childs cs₁ cs₁ i₁ -> Childs cs₂ cs₂ i₂
coerceChilds {i₂ = i₂} {i₁} q = let q₁ , q₂ , q₃ = q in coerce
  ((, (λ A B q₄ -> sym A {B} q₄ , λ _ _ _ -> q₁ , λ _ _ _ -> q₁))
    , (λ q₄ q₅ q₆ -> proj₁ q₆ , λ x₁ x₂ q₇ ->
         let q₈  , q₉  = proj₂ q₄ x₁       in
         let q₁₀ , q₁₁ = proj₂ q₅ x₂       in
         let q₁₂ , q₁₃ = proj₂ q₆ x₁ x₂ q₇ in
           (q₁ , (λ j₁ j₂ q₁₃ -> q₁ , (q₂ , sym j₁ q₁₃)) , sym q₈ {q₁₀} q₁₂)
           , λ rs₁ rs₂ q₈ -> ≈-zip i₁ i₂ q₉ q₁₁ (sym i₂ q₃) q₁₃)
    , q₂)
```

A bunch of different encodings of OTT can be found [here](https://github.com/effectfully/random-stuff/tree/master/OTT).

## References

[1] ["Towards Observational Type Theory"](http://strictlypositive.org/ott.pdf), Thorsten Altenkirch and Conor McBride

[2] ["Observational Equality, Now!"](http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf), Thorsten Altenkirch, Conor McBride, Wouter Swierstra

[3] ["Hier Soir, an OTT Hierarchy"](http://mazzo.li/epilogue/index.html%3Fp=1098.html), Conor McBride

[4] ["W-types: good news and bad news"](http://mazzo.li/epilogue/index.html%3Fp=324.html), Conor McBride

[5] ["On Universes in Type Theory"](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.1318&rep=rep1&type=pdf), Erik Palmgren

[6] ["Modeling Elimination of Described Types"](http://spire-lang.org/blog/2014/01/15/modeling-elimination-of-described-types/), Larry Diehl

[7] ["Inductive-Recursive Descriptions"](http://spire-lang.org/blog/2014/08/04/inductive-recursive-descriptions/), Larry Diehl

[8] ["The Gengtle Art of Levitation"](https://jmchapman.github.io/papers/levitation.pdf), James Chapman, Pierre-Évariste Dagand, Conor McBride, Peter Morris
