```agda
open import Axiom
module Basic.Isomorphism (ℳ : ETCS) where
open ETCS ℳ
```

```agda
AssIdˡ : {f : X →̇ Y} {g : Y →̇ Z} {h : Z →̇ Y} → h ∘ g ≡ id → h ∘ (g ∘ f) ≡ f
AssIdˡ {f} {g} {h} hg = begin
  h ∘ (g ∘ f)           ≡˘⟨ AxAss ⟩
  (h ∘ g) ∘ f           ≡⟨ cong (_∘ f) hg ⟩
  id ∘ f                ≡⟨ AxIdˡ ⟩
  f                     ∎ where open ≡-Reasoning

AssIdʳ : {f : X →̇ Y} {g : W →̇ X} {h : X →̇ W} → g ∘ h ≡ id → (f ∘ g) ∘ h ≡ f
AssIdʳ {f} {g} {h} hg = begin
  (f ∘ g) ∘ h           ≡⟨ AxAss ⟩
  f ∘ (g ∘ h)           ≡⟨ cong (f ∘_) hg ⟩
  f ∘ id                ≡⟨ AxIdʳ ⟩
  f                     ∎ where open ≡-Reasoning
```

```agda
-- Definition 2.2.2
isInv : (f : X →̇ Y) (g : Y →̇ X) → Set
isInv f g = f ∘ g ≡ id × g ∘ f ≡ id
```

```agda
-- Lemma 2.2.4
unique-isInv : unique (isInv f)
unique-isInv {f} {a = g} {b = g′} (_ , p) (q , _) = begin
  g             ≡˘⟨ AssIdʳ q ⟩
  (g ∘ f) ∘ g′  ≡⟨ AxAss ⟩
  g ∘ (f ∘ g′)  ≡⟨ AssIdˡ p ⟩
  g′            ∎ where open ≡-Reasoning
```

```agda
-- Definition 2.2.5
isIso : (f : X →̇ Y) → Set
isIso {X} {Y} f = Σ (Y →̇ X) λ g → isInv f g
```

```agda
-- Definition 2.2.8
infix 10 _≅_
_≅_ : CSet → CSet → Set
X ≅ Y = Σ (X →̇ Y) isIso
```

```agda
-- Lemma 2.2.6
isIso-id : isIso id⟨ X ⟩
isIso-id = id , AxIdˡ , AxIdˡ

isIso-∘ : isIso f → isIso g → isIso (g ∘ f)
isIso-∘ {f} {g} (f⁻¹ , ff⁻¹ , f⁻¹f) (g⁻¹ , gg⁻¹ , g⁻¹g) = f⁻¹ ∘ g⁻¹ , p , q where
  p =                       begin
    (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)   ≡⟨ AxAss ⟩
    g ∘ (f ∘ (f⁻¹ ∘ g⁻¹))   ≡⟨ cong (g ∘_) (AssIdˡ ff⁻¹) ⟩
    g ∘ g⁻¹                 ≡⟨ gg⁻¹ ⟩
    id                      ∎ where open ≡-Reasoning
  q =                       begin
    (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)   ≡⟨ AxAss ⟩
    f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f))   ≡⟨ cong (f⁻¹ ∘_) (AssIdˡ g⁻¹g) ⟩
    f⁻¹ ∘ f                 ≡⟨ f⁻¹f ⟩
    id                      ∎ where open ≡-Reasoning

isIso-⁻¹ : ((f⁻¹ , _) : isIso f) → isIso f⁻¹
isIso-⁻¹ {f} (f⁻¹ , p , q) = f , q , p
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
isoInvariant⟨_⟩ : {A : Set ℓ} (C : Commuter A) (P : A → Set ℓ′) → Set _
isoInvariant⟨_⟩ (π , comm) P = ∀ {a b} (j : π a →̇ π b) → isIso j → comm a b j → P a → P b

isoUnique⟨_⟩ : {A : Set ℓ} (C : Commuter A) (P : A → Set ℓ′) → Set _
isoUnique⟨_⟩ (π , comm) P = ∀ {a b} → P a → P b → Σ (π a →̇ π b) λ j → isIso j × comm a b j × unique (comm a b)

isoInvariant : (P : CSet → Set) → Set
isoInvariant P = isoInvariant⟨ id⒨ , (λ _ _ _ → ⊤) ⟩ P

isoUnique : (P : CSet → Set) → Set
isoUnique P = isoUnique⟨ id⒨ , (λ _ _ _ → ⊤) ⟩ P
```
