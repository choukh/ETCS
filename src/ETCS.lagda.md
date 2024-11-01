```agda
module ETCS where

open import Level public using (Level)
open import Data.Unit public using (⊤; tt)
open import Data.Product public
  renaming (_×_ to _∧_) using (Σ; _,_; proj₁; proj₂)
open import Function using (_$_) public
open import Relation.Binary.PropositionalEquality public
```

```agda
variable ℓ ℓ′ ℓ′′ : Level

unique : {A : Set ℓ} (P : A → Set ℓ′) → Set _
unique P = ∀ {a b} → P a → P b → a ≡ b

universal : {A : Set ℓ} (B : A → Set ℓ′) (P : ∀ {x} → B x → Set ℓ′′) → Set _
universal B P = ∀ x → (Σ (B x) P) ∧ unique (P {x})
```

```agda
-- 2.1 The data
record Data : Set₁ where
  infix 5 _∘_
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
    isoInvariant-isTerminal {X = T} {Y = T′} tml (j , j⁻¹ , jj⁻¹ , _) X with tml X
    ... | (f , tt) , f! = (j ∘ f , tt) , λ {f′ g′} _ _ → begin
      f′                      ≡˘⟨ AxIdˡ ⟩
      id ∘ f′                 ≡˘⟨ cong (_∘ f′) jj⁻¹ ⟩
      (j ∘ j⁻¹) ∘ f′          ≡⟨ AxAss ⟩
      j ∘ (j⁻¹ ∘ f′)          ≡⟨ cong (j ∘_) (f! tt tt) ⟩
      j ∘ (j⁻¹ ∘ g′)          ≡˘⟨ AxAss ⟩
      (j ∘ j⁻¹) ∘ g′          ≡⟨ cong (_∘ g′) jj⁻¹ ⟩
      id ∘ g′                 ≡⟨ AxIdˡ ⟩
      g′                      ∎ where open ≡-Reasoning
```

```agda
    -- Lemma 2.3.4
    isoUnique-isTerminal : isoUnique isTerminal
    isoUnique-isTerminal {X = T} {Y = T′} tml tml′ with tml′ T | tml T′
    ... | (f , tt) , f! | (g , tt) , g! = f , g , tml′ T′ .proj₂ tt tt , tml T .proj₂ tt tt
```
