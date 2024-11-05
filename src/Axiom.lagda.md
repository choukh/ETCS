```agda
module Axiom where

open import Level public using (Level; suc; _⊔_)
open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤; tt)
open import Data.Product public using (Σ; _×_; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary.PropositionalEquality public
```

## Introduction

```agda
variable ℓ ℓ′ ℓ′′ : Level

unique : {A : Set ℓ} (P : A → Set ℓ′) → Set _
unique P = ∀ {a b} → P a → P b → a ≡ b

universal : (A : Set ℓ) (B : A → Set ℓ′) (P : ∀ x → B x → Set ℓ′′) → Set _
universal A B P = ∀ x → (Σ (B x) (P x)) × unique (P x)
```

## The data

```agda
-- 2.1 The data
record Data : Set₁ where
  infixl 10 _→̇_
  infix 10 _∘_
  field
    CSet : Set
    _→̇_ : (X Y : CSet) → Set
    _∘_ : {X Y Z : CSet} (g : Y →̇ Z) (f : X →̇ Y) → (X →̇ Z)
    id⟨_⟩ : (X : CSet) → X →̇ X

  id : {X : CSet} → X →̇ X
  id {X} = id⟨ X ⟩
```

```agda
  variable
    A W X Y Z X′ Y′ : CSet
    f g h f′ g′ : X →̇ Y
```

## Axioms

```agda
  record Axiom : Set where
```

### Axiom 1 - 4

```agda
    field
      -- Axiom 1
      AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      AxIdˡ : id ∘ f ≡ f
      AxIdʳ : f ∘ id ≡ f
```

```agda
    -- Definition 2.3.1
    terminal : CSet → Set
    terminal T = universal CSet (_→̇ T) (λ _ _ → ⊤)

    -- Axiom 2
    field AxTml : Σ CSet terminal
```

```agda
    １ : CSet
    １ = AxTml .fst

    Elm : CSet → Set
    Elm = １ →̇_
```

```agda
    -- Definition 2.3.6
    ∀[∈]-syntax : (X : CSet) (P : Elm X → Set) → Set
    ∀[∈]-syntax X P = (x : Elm X) → P x

    infix 3 ∀[∈]-syntax
    syntax ∀[∈]-syntax X (λ x → A) = ∀[ x ∈ X ] A
```

```agda
    infix 15 _⦅_⦆
    _⦅_⦆ : (f : X →̇ Y) → ∀[ x ∈ X ] Elm Y
    f ⦅ x ⦆ = f ∘ x

    -- Axiom 3
    field AxFunExt : (∀[ x ∈ X ] f ⦅ x ⦆ ≡ g ⦅ x ⦆) → f ≡ g
```

```agda
    -- Definition 2.5.1
    empty : CSet → Set
    empty X = ∀[ x ∈ X ] ⊥

    -- Axiom 4
    field AxEmpty : Σ CSet empty
```

### Axiom 5

```agda
    Commuter : (A : Set ℓ) (ℓ′ : Level) → Set (ℓ ⊔ suc ℓ′)
    Commuter A ℓ′ = Σ (A → CSet) λ π → (a b : A) (j : π a →̇ π b) → Set ℓ′

    universal⟨_⟩ : {A : Set ℓ} → Commuter A ℓ′ → A → Set _
    universal⟨_⟩ {ℓ} {ℓ′} {A} C a = let (π , comm) = C in universal A (λ x → π x →̇ π a) λ x → comm x a
```

```agda
    ProductDiagram : (X Y : CSet) → Set
    ProductDiagram X Y = Σ CSet λ P → P →̇ X × P →̇ Y

    ProductCommuter : Commuter (ProductDiagram X Y) _
    ProductCommuter = fst , λ { (A , f , g) (P , p , q) h → p ∘ h ≡ f × q ∘ h ≡ g }

    -- Definition 2.6.2
    isProduct : ProductDiagram X Y → Set
    isProduct = universal⟨ ProductCommuter ⟩

    -- Axiom 5
    field AxProd : Σ (ProductDiagram X Y) isProduct
```

```agda
    infixr 15 _×̇_
    _×̇_ : CSet → CSet → CSet
    X ×̇ Y = AxProd {X} {Y} .fst .fst

    pr₁ : X ×̇ Y →̇ X
    pr₁ {X} {Y} = AxProd {X} {Y} .fst .snd .fst

    pr₂ : X ×̇ Y →̇ Y
    pr₂ {X} {Y} = AxProd {X} {Y} .fst .snd .snd

    infixr 5 _,̇_
    _,̇_ : A →̇ X → A →̇ Y → A →̇ X ×̇ Y
    f ,̇ g = AxProd .snd (_ , f , g) .fst .fst

    pr₁-≡ : pr₁ ∘ ( f ,̇ g ) ≡ f
    pr₁-≡ {f} {g} = AxProd .snd (_ , f , g) .fst .snd .fst

    pr₂-≡ : pr₂ ∘ ( f ,̇ g ) ≡ g
    pr₂-≡ {f} {g} = AxProd .snd (_ , f , g) .fst .snd .snd

    ×̇-η : {h : A →̇ X ×̇ Y} → h ≡ pr₁ ∘ h ,̇ pr₂ ∘ h
    ×̇-η {h} = AxProd .snd (_ , (pr₁ ∘ h) , (pr₂ ∘ h)) .snd (refl , refl) (pr₁-≡ , pr₂-≡)
```

```agda
record ETCS : Set₁ where
  field
    etcs : Σ Data Data.Axiom
  open Data (etcs .fst) public
  open Data.Axiom (etcs .snd) public
```
