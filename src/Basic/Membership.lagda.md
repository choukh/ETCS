```agda
open import Axiom
module Basic.Membership (ℳ : ETCS) where
open ETCS ℳ

open import Basic.Isomorphism ℳ
open import Function using (_$_)
open import Relation.Nullary using (¬_)
```

```agda
-- Lemma 2.3.3
isoInvariant-terminal : isoInvariant terminal
isoInvariant-terminal {a = T} {b = T′} j (j⁻¹ , jj⁻¹ , _) tt tml X =
  let (f , tt) , f! = tml X in
  (j ∘ f , tt) , λ {f′ g′} _ _ → begin
    f′                      ≡˘⟨ AssIdˡ jj⁻¹ ⟩
    j ∘ (j⁻¹ ∘ f′)          ≡⟨ cong (j ∘_) (f! tt tt) ⟩
    j ∘ (j⁻¹ ∘ g′)          ≡⟨ AssIdˡ jj⁻¹ ⟩
    g′                      ∎ where open ≡-Reasoning
```

```agda
-- Lemma 2.3.4
isoUnique-terminal : isoUnique terminal
isoUnique-terminal {a = T} {b = T′} tT tT′ =
  let f : T →̇ T′
      f = tT′ T .fst .fst
      f′ : T′ →̇ T
      f′ = tT T′ .fst .fst
      ff′ : f ∘ f′ ≡ id
      ff′ = tT′ T′ .snd tt tt
      f′f : f′ ∘ f ≡ id
      f′f = tT T .snd tt tt
      f≡g : {f g : T →̇ T′} → f ≡ g
      f≡g = tT′ T .snd tt tt
  in f , (f′ , ff′ , f′f) , tt , λ _ _ → f≡g
```

```agda
!⟨_⟩ : (X : CSet) → X →̇ １
!⟨ X ⟩ = AxTml .snd X .fst .fst

! : X →̇ １
! {X} = !⟨ X ⟩
```

```agda
-- Lemma 2.3.7
id-wellDefined : ∀[ x ∈ X ] id ⦅ x ⦆ ≡ x
id-wellDefined x = AxIdˡ

∘-wellDefined : ∀[ x ∈ X ] (g ∘ f) ⦅ x ⦆ ≡ g ⦅ f ⦅ x ⦆ ⦆
∘-wellDefined _ = AxAss
```

```agda
oneElement : CSet → Set
oneElement X = Elm X × ∀ {x y : Elm X} → x ≡ y

* : Elm １
* = AxTml .snd １ .fst .fst

oneElement-１ : oneElement １
oneElement-１ = * , AxTml .snd １ .snd tt tt
```

```agda
-- Lemma 2.4.1
terminal→oneElement : terminal X → oneElement X
terminal→oneElement tml = tml １ .fst .fst , tml １ .snd tt tt

oneElement→terminal : oneElement X → terminal X
oneElement→terminal (x , x!) = isoInvariant-terminal
  x (! , AxFunExt q , p) tt (AxTml .snd) where
    p : {x y : Elm １} → x ≡ y
    p = AxTml .snd １ .snd tt tt
    q = λ y →         begin
      (x ∘ !) ∘ y     ≡⟨ AssIdʳ p ⟩
      x               ≡⟨ x! ⟩
      y               ≡˘⟨ AxIdˡ ⟩
      id ∘ y          ∎ where open ≡-Reasoning
```

```agda
-- Example 2.5.2
_ : ¬ empty １
_ = λ p → p *
```

```agda
-- Exercise 2.6.4
_ : ((P , _) : ProductDiagram X Y) → empty X → empty P
_ = λ (P , p , _) eX q → eX (p ⦅ q ⦆)
```
