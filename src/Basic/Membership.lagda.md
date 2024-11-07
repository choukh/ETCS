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
isoInvariant-isTerminal : isoInvariant⟨ TerminalCommuter ⟩ isTerminal
isoInvariant-isTerminal {a = T} {b = T′} j (j⁻¹ , jj⁻¹ , _) tt tml X =
  let (f , tt) , f! = tml X in
  (j ∘ f , tt) , λ {f′ g′} _ _ → begin
    f′                      ≡˘⟨ AssIdˡ jj⁻¹ ⟩
    j ∘ (j⁻¹ ∘ f′)          ≡⟨ cong (j ∘_) (f! tt tt) ⟩
    j ∘ (j⁻¹ ∘ g′)          ≡⟨ AssIdˡ jj⁻¹ ⟩
    g′                      ∎ where open ≡-Reasoning
```

```agda
-- Lemma 2.3.4
isoUnique-isTerminal : isoUnique⟨ TerminalCommuter ⟩ isTerminal
isoUnique-isTerminal a@{T , _} b@{T′ , _} ta tb =
  let f : T →̇ T′
      f = tb a .fst .fst
      f′ : T′ →̇ T
      f′ = ta b .fst .fst
      ff′ : f ∘ f′ ≡ id
      ff′ = tb b .snd tt tt
      f′f : f′ ∘ f ≡ id
      f′f = ta a .snd tt tt
      f≡g : {f g : T →̇ T′} → f ≡ g
      f≡g = tb a .snd tt tt
  in f , (f′ , ff′ , f′f) , tt , λ _ _ → f≡g
```

```agda
!⟨_⟩ : (X : CSet) → X →̇ １
!⟨ X ⟩ = AxTml .snd (X , tt) .fst .fst

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
* = AxTml .snd (１ , tt) .fst .fst

oneElement-１ : oneElement １
oneElement-１ = * , AxTml .snd (１ , tt) .snd tt tt
```

```agda
-- Lemma 2.4.1
isTerminal→oneElement : isTerminal (X , tt) → oneElement X
isTerminal→oneElement tml = tml (１ , tt) .fst .fst , tml (１ , tt) .snd tt tt

oneElement→isTerminal : oneElement X → isTerminal (X , tt)
oneElement→isTerminal (x , x!) = isoInvariant-isTerminal
  x (! , AxFunExt q , p) tt (AxTml .snd) where
    p : {x y : Elm １} → x ≡ y
    p = AxTml .snd (１ , tt) .snd tt tt
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
