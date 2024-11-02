```agda
module ETCS where

open import Level public using (Level; suc; _⊔_)
open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤; tt)
open import Data.Product public
  using (Σ; _×_; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Function as Meta using (_$_) public
open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality public
```

## Introduction

```agda
variable ℓ ℓ′ ℓ′′ : Level

unique : {A : Set ℓ} (P : A → Set ℓ′) → Set _
unique P = ∀ {a b} → P a → P b → a ≡ b

universal : (A : Set ℓ) (B : A → Set ℓ′) (P : ∀ {x} → B x → Set ℓ′′) → Set _
universal A B P = ∀ x → (Σ (B x) P) × unique (P {x})
```

## The data

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

## Axioms

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
      AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      AxIdˡ : id ∘ f ≡ f
      AxIdʳ : f ∘ id ≡ f
```

```agda
    -- Definition 2.3.1
    terminal : CSet → Set
    terminal T = universal CSet (_⇒ T) (λ _ → ⊤)

    -- Axiom 2
    field AxTml : Σ CSet terminal
```

```agda
    𝟏 : CSet
    𝟏 = AxTml .fst

    Elm : CSet → Set
    Elm = 𝟏 ⇒_
```

```agda
    -- Definition 2.3.6
    ∀[∈]-syntax : (X : CSet) (P : Elm X → Set) → Set
    ∀[∈]-syntax X P = (x : Elm X) → P x

    infix 3 ∀[∈]-syntax
    syntax ∀[∈]-syntax X (λ x → A) = ∀[ x ∈ X ] A
```

```agda
    _（_） : (f : X ⇒ Y) → ∀[ x ∈ X ] Elm Y
    f （ x ） = f ∘ x

    -- Axiom 3
    field AxFunExt : (∀[ x ∈ X ] f （ x ） ≡ g （ x ）) → f ≡ g
```

```agda
    -- Definition 2.5.1
    empty : CSet → Set
    empty X = ∀[ x ∈ X ] ⊥

    -- Axiom 4
    field AxEmpty : Σ CSet empty
```

```agda
    ProductDiagram : (X Y : CSet) → Set
    ProductDiagram X Y = Σ CSet λ P → P ⇒ X × P ⇒ Y

    -- Definition 2.6.2
    isProduct : ProductDiagram X Y → Set
    isProduct {X} {Y} d = let (P , p , q) = d in universal
      (ProductDiagram X Y)
      (λ (A , _) → A ⇒ P)
      (λ {(A , f , g)} h → p ∘ h ≡ f × q ∘ h ≡ g)

    -- Axiom 5
    field AxProd : Σ (ProductDiagram X Y) isProduct
```

## Justification

```agda
    -- Definition 2.2.2
    isInv : (f : X ⇒ Y) (g : Y ⇒ X) → Set
    isInv f g = f ∘ g ≡ id × g ∘ f ≡ id
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
    -- Definition 2.2.8
    _≅_ : CSet → CSet → Set
    X ≅ Y = Σ (X ⇒ Y) isIso
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
    Commuter : (A : Set ℓ) (ℓ′ : Level) → Set (ℓ ⊔ suc ℓ′)
    Commuter A ℓ′ = Σ (A → CSet) λ π → (a b : A) (j : π a ⇒ π b) → Set ℓ′

    isoInvariant⟨_⟩ : {A : Set ℓ} (C : Commuter A ℓ′) (P : A → Set ℓ′′) → Set _
    isoInvariant⟨_⟩ (π , comm) P = ∀ {a b} (j : π a ⇒ π b) → isIso j → comm a b j → P a → P b

    isoUnique⟨_⟩ : {A : Set ℓ} (C : Commuter A ℓ′) (P : A → Set ℓ′′) → Set _
    isoUnique⟨_⟩ (π , comm) P = ∀ {a b} → P a → P b → Σ (π a ⇒ π b) λ j → isIso j × comm a b j

    isoInvariant : (P : CSet → Set) → Set
    isoInvariant P = isoInvariant⟨ Meta.id , (λ _ _ _ → ⊤) ⟩ P

    isoUnique : (P : CSet → Set) → Set
    isoUnique P = isoUnique⟨ Meta.id , (λ _ _ _ → ⊤) ⟩ P
```

```agda
    -- Lemma 2.3.3
    isoInvariant-terminal : isoInvariant terminal
    isoInvariant-terminal {a = T} {b = T′} j (j⁻¹ , jj⁻¹ , _) tt tml X =
      let (f , tt) , f! = tml X in
      (j ∘ f , tt) , λ {f′ g′} _ _ → begin
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
    isoUnique-terminal : isoUnique terminal
    isoUnique-terminal {a = T} {b = T′} tT tT′ =
      tT′ T .fst .fst , (tT T′ .fst .fst , tT′ T′ .snd tt tt , tT T .snd tt tt) , tt
```

```agda
    !⟨_⟩ : (X : CSet) → X ⇒ 𝟏
    !⟨ X ⟩ = AxTml .snd X .fst .fst

    ! : X ⇒ 𝟏
    ! {X} = !⟨ X ⟩
```

```agda
    -- Lemma 2.3.7
    id-wellDefined : ∀[ x ∈ X ] id （ x ） ≡ x
    id-wellDefined x = AxIdˡ

    ∘-wellDefined : ∀[ x ∈ X ] (g ∘ f) （ x ） ≡ g （ f （ x ） ）
    ∘-wellDefined _ = AxAss
```

```agda
    oneElement : CSet → Set
    oneElement X = Elm X × ∀ {x y : Elm X} → x ≡ y

    * : Elm 𝟏
    * = AxTml .snd 𝟏 .fst .fst

    oneElement-𝟏 : oneElement 𝟏
    oneElement-𝟏 = * , AxTml .snd 𝟏 .snd tt tt
```

```agda
    -- Lemma 2.4.1
    terminal→oneElement : terminal X → oneElement X
    terminal→oneElement tml = tml 𝟏 .fst .fst , tml 𝟏 .snd tt tt

    oneElement→terminal : oneElement X → terminal X
    oneElement→terminal (x , x!) = isoInvariant-terminal
      x (! , AxFunExt q , p) tt (AxTml .snd) where
        p : {x y : Elm 𝟏} → x ≡ y
        p = AxTml .snd 𝟏 .snd tt tt
        q = λ y →         begin
          (x ∘ !) ∘ y     ≡⟨ AxAss ⟩
          x ∘ (! ∘ y)     ≡⟨ cong (x ∘_) p ⟩
          x ∘ id          ≡⟨ AxIdʳ ⟩
          x               ≡⟨ x! ⟩
          y               ≡˘⟨ AxIdˡ ⟩
          id ∘ y          ∎ where open ≡-Reasoning
```

```agda
    -- Example 2.5.2
    _ : ¬ empty 𝟏
    _ = λ p → p *
```

```agda
    -- Exercise 2.6.4
    _ : ((P , _) : ProductDiagram X Y) → empty X → empty P
    _ = λ (P , p , _) eX q → eX (p （ q ）)
```

```agda
    ProductCommuter : Commuter (ProductDiagram X Y) _
    ProductCommuter = fst , λ { (P , p , q) (P′ , p′ , q′) j → p′ ∘ j ≡ p × q′ ∘ j ≡ q }

    -- Lemma 2.6.6
    isoInvariant-isProduct : isoInvariant⟨ ProductCommuter ⟩ (isProduct {X} {Y})
    isoInvariant-isProduct {a = P , p , q} {b = P′ , p′ , q′}
      j (j⁻¹ , jj⁻¹ , j⁻¹j) (p′j , q′j) Pa c@(A , f , g) =
        let ((h , ph , qh) , u) = Pa c in
        (j ∘ h , {!  !} , {!   !}) , {!   !}
```
