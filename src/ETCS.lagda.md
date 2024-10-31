```agda
module ETCS where
open import MetaLogic
```

```agda
unique : {A : Set} (P : A → Set) → Set
unique P = ∀ {a b} → P a → P b → a ≡ b
```

```agda
universal : {A : Set} (B : A → Set) (P : ∀ {x} → B x → Set) → Set
universal B P = ∀ x → Σ (B x) λ a → (b : B x) → P b → a ≡ b
```

```agda
-- 2.1 The data
record Data : Set₁ where
  field
    CSet : Set
    _⇒_ : (X Y : CSet) → Set
    _∘_ : {X Y Z : CSet} (g : Y ⇒ Z) (f : X ⇒ Y) → (X ⇒ Z)
    id⟨_⟩ : (X : CSet) → X ⇒ X

  id : {X : CSet} → X ⇒ X
  id {X} = id⟨ X ⟩
```

```agda
module _ (D : Data) where
  open Data D
  variable
    W X Y Z : CSet
    f g h f′ g′ h′ : X ⇒ Y
```

```agda
  -- Definition 2.3.1
  isTerminal : CSet → Set
  isTerminal T = universal (_⇒ T) (λ _ → ⊤)
```

```agda
  record Axiom : Set where
    field
      -- Axiom 1
      AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      AxIdˡ : id ∘ f ≡ f
      AxIdʳ : f ∘ id ≡ f
      -- Axiom 2
      AxTml : Σ CSet isTerminal
```

```agda
    -- Definition 2.2.2
    isInv : (f : X ⇒ Y) (g : Y ⇒ X) → Set
    isInv f g = f ∘ g ≡ id ∧ g ∘ f ≡ id
```

```agda
    -- Lemma 2.2.4
    unique-isInv : unique (isInv f)
    unique-isInv {f} {a = g} {b = g′} (_ , p) (q , _) = begin
      g             ≡˘⟨ AxIdʳ ⟩
      g ∘ id        ≡˘⟨ cong (g ∘_) q ⟩
      g ∘ (f ∘ g′)  ≡˘⟨ AxAss ⟩
      (g ∘ f) ∘ g′  ≡⟨ cong (_∘ g′) p ⟩
      id ∘ g′       ≡⟨ AxIdˡ ⟩
      g′            ∎ where open ≡-Reasoning
```

```agda
    -- Definition 2.2.5
    isIso : (f : X ⇒ Y) → Set
    isIso {X} {Y} f = Σ (Y ⇒ X) λ g → isInv f g
```

```agda
    -- Lemma 2.2.6
    isIso-id : isIso id⟨ X ⟩
    isIso-id = id , AxIdˡ , AxIdˡ

    isIso-∘ : isIso f → isIso g → isIso (g ∘ f)
    isIso-∘ {f} {g} (f⁻¹ , ff⁻¹ , f⁻¹f) (g⁻¹ , gg⁻¹ , g⁻¹g) = f⁻¹ ∘ g⁻¹ , p , q where
      p =                       begin
        (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)   ≡⟨ AxAss ⟩
        g ∘ (f ∘ (f⁻¹ ∘ g⁻¹))   ≡˘⟨ cong (g ∘_) AxAss ⟩
        g ∘ ((f ∘ f⁻¹) ∘ g⁻¹)   ≡⟨ cong (g ∘_) $ cong (_∘ g⁻¹) ff⁻¹ ⟩
        g ∘ (id ∘ g⁻¹)          ≡⟨ cong (g ∘_) AxIdˡ ⟩
        g ∘ g⁻¹                 ≡⟨ gg⁻¹ ⟩
        id                      ∎ where open ≡-Reasoning
      q =                       begin
        (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)   ≡⟨ AxAss ⟩
        f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f))   ≡˘⟨ cong (f⁻¹ ∘_) AxAss ⟩
        f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f)   ≡⟨ cong (f⁻¹ ∘_) $ cong (_∘ f) g⁻¹g ⟩
        f⁻¹ ∘ (id ∘ f)          ≡⟨ cong (f⁻¹ ∘_) AxIdˡ ⟩
        f⁻¹ ∘ f                 ≡⟨ f⁻¹f ⟩
        id                      ∎ where open ≡-Reasoning

    isIso-⁻¹ : ((f⁻¹ , _) : isIso f) → isIso (f⁻¹)
    isIso-⁻¹ {f} (f⁻¹ , p , q) = f , q , p
```

```agda
    -- Definition 2.2.8
    _≅_ : CSet → CSet → Set
    X ≅ Y = Σ (X ⇒ Y) isIso
```

```agda
    -- Lemma 2.2.9
    ≅-refl : X ≅ X
    ≅-refl = id , isIso-id

    ≅-trans : X ≅ Y → Y ≅ Z → X ≅ Z
    ≅-trans (f , if) (g , ig) = g ∘ f , isIso-∘ if ig

    ≅-sym : X ≅ Y → Y ≅ X
    ≅-sym (f , i@(f⁻¹ , _)) = f⁻¹ , isIso-⁻¹ i
```

```agda
    isoInvariant : (P : CSet → Set) → Set
    isoInvariant P = ∀ {X Y} → P X → X ≅ Y → P Y

    isoUnique : (P : CSet → Set) → Set
    isoUnique P = ∀ {X Y} → P X → P Y → X ≅ Y
```

```agda
    -- Lemma 2.3.3
    isoInvariant-isTerminal : isoInvariant isTerminal
    isoInvariant-isTerminal = {!   !}
```
(j , _) t X with t X
    ... | f , t = {!   !}
