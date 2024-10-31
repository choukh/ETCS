```agda
module ETCS where
open import MetaLogic
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
  record Axiom : Set where
    field
      -- Axiom 1
      Assoc : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      Idˡ : id ∘ f ≡ f
      Idʳ : f ∘ id ≡ f
```

```agda
    -- Definition 2.2.2
    isInv : (f : X ⇒ Y) (g : Y ⇒ X) → Set
    isInv f g = f ∘ g ≡ id ∧ g ∘ f ≡ id
```

```agda
    -- Lemma 2.2.4
    unique-inverse : isInv f g → isInv f g′ → g ≡ g′
    unique-inverse {f} {g} {g′} (_ , p) (q , _) = begin
      g             ≡˘⟨ Idʳ ⟩
      g ∘ id        ≡˘⟨ cong (g ∘_) q ⟩
      g ∘ (f ∘ g′)  ≡˘⟨ Assoc ⟩
      (g ∘ f) ∘ g′  ≡⟨ cong (_∘ g′) p ⟩
      id ∘ g′       ≡⟨ Idˡ ⟩
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
    isIso-id = id , Idˡ , Idˡ

    isIso-∘ : isIso f → isIso g → isIso (g ∘ f)
    isIso-∘ {f} {g} (f⁻¹ , ff⁻¹ , f⁻¹f) (g⁻¹ , gg⁻¹ , g⁻¹g) = f⁻¹ ∘ g⁻¹ , p , q where
      p =                       begin
        (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)   ≡⟨ Assoc ⟩
        g ∘ (f ∘ (f⁻¹ ∘ g⁻¹))   ≡˘⟨ cong (g ∘_) Assoc ⟩
        g ∘ ((f ∘ f⁻¹) ∘ g⁻¹)   ≡⟨ cong (g ∘_) $ cong (_∘ g⁻¹) ff⁻¹ ⟩
        g ∘ (id ∘ g⁻¹)          ≡⟨ cong (g ∘_) Idˡ ⟩
        g ∘ g⁻¹                 ≡⟨ gg⁻¹ ⟩
        id                      ∎ where open ≡-Reasoning
      q =                       begin
        (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)   ≡⟨ Assoc ⟩
        f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f))   ≡˘⟨ cong (f⁻¹ ∘_) Assoc ⟩
        f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f)   ≡⟨ cong (f⁻¹ ∘_) $ cong (_∘ f) g⁻¹g ⟩
        f⁻¹ ∘ (id ∘ f)          ≡⟨ cong (f⁻¹ ∘_) Idˡ ⟩
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
