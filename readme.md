# OTT

It's an implementation of Observational Type Theory as an Agda library. The universe contains `⊤`, `⊥`, natural numbers, two impredicative universes (`Prop` (OK) and `Type` (not OK)), Σ- and Π-types, lists and allows generic programming via the `rose` construct.

## Implemented

 - `rose` allows to define inductive data types (including inductive families) in the target theory. `coerce` computes under constructors of any inductive family defined in terms of `rose`. This is achieved via the trick described in the section 5 of [1]. `rose` also allows to define eliminators of data types (even in an intensional type theory). Each data type has at least two eliminators: one classical and one "up to propositional equality". An example from the `OTT.Data.Fin` module:

```
elimFinₑ : ∀ {n π}
         -> (P : ∀ {n} -> Fin n -> Set π)
         -> (∀ {n m} {i : Fin n} -> (q : ⟦ suc n ≅ m ⟧) -> P i -> P {m} (fsucₑ q i))
         -> (∀ {n m} -> (q : ⟦ suc n ≅ m ⟧) -> P {m} (fzeroₑ q))
         -> (i : Fin n)
         -> P i
elimFinₑ P f x (node (here  (m , [] , q)))            = x q
elimFinₑ P f x (node (there (here (m , i ∷ [] , q)))) = f q (elimFinₑ P f x i)
elimFinₑ P f x (node (there (there ())))

elimFin : ∀ {n π}
        -> (P : ∀ {n} -> Fin n -> Univ π)
        -> (∀ {n} {i : Fin n} -> ⟦ P i ⇒ P (fsuc i) ⟧)
        -> (∀ {n} -> ⟦ P {suc n} fzero ⟧)
        -> (i : Fin n)
        -> ⟦ P i ⟧
elimFin P f x = elimFinₑ (⟦_⟧ ∘ P)
  (λ {n m i} q r -> subst₂ (λ p q -> P {p} (fsucₑ q i)) q (huip (suc n) m q) (f r))
  (λ {n m}   q   -> subst₂ (λ p q -> P {p} (fzeroₑ q))  q (huip (suc n) m q)  x)
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

`elimFin′` doesn't mention `coerce` as well. `subst₂` is defined in terms of `coerce`, so it computes under constructors of data types, hence classical eliminators have pretty good computational behaviour too.

A simple test:

```
postulate
  n m : ℕ

test : ⟦ fromFin ((Fin (3 + n) ∋ fsuc (fsuc fzero)) +ᶠ (Fin (2 + m) ∋ fsuc fzero)) ≅ 3 ⟧
test = tt
```

`n` and `m` are stuck, but the expression reduces properly regardless of whether `_+ᶠ_` is defined in terms of `elimFin′` or `elimFin`.

A model of the model can be found [here](https://github.com/effectfully/random-stuff/blob/master/Rose/Coercible.agda).

## Not implemented

- Universe hierarchy. We want a universe hierarchy with the following properties:

  1. predicativity
  2. cumulativity
  3. non-redundancy
  4. `⟦ type n ⟧ ≡ Type n` for neutral `n`
  5. easy to use
  
  I'm not aware of such encoding. The best seems to be [3], but as far as I understand only (1) and (2) hold for it. It's probably possible to add (4) by introducing the superuniverse in the style of [5] like [this](https://github.com/effectfully/random-stuff/blob/master/Omega.agda).

- Definional proof irrelevance.
- Erasing of stuck coercions between definitionally equal sets (that's not my fault, Agda just doesn't have an available definitional equality checker) (note that we have proper eliminators without this tool unlike in OTT with W-types (see [4])).
- Equality for propositions should be isomorphism.
- Codata (is it simply the coinductive counterpart of `rose`?).

# Remarks

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

# References

[1] ["Towards Observational Type Theory", Thorsten Altenkirch and Conor McBride](http://strictlypositive.org/ott.pdf)
[2] ["Observational Equality, Now!", Thorsten Altenkirch, Conor McBride, Wouter Swierstra](http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf)
[3] ["Hier Soir, an OTT Hierarchy", Conor McBride](http://mazzo.li/epilogue/index.html%3Fp=1098.html)
[4] ["W-types: good news and bad news", Conor McBride](http://mazzo.li/epilogue/index.html%3Fp=324.html)
[5] ["On Universes in Type Theory", Erik Palmgren](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.1318&rep=rep1&type=pdf)