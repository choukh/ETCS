```agda
module Axiom where

open import Level public using (Level; suc)
open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤; tt)
open import Data.Product public using (Σ; _×_; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Function public using (case_of_) renaming (id to id⒨)
open import Relation.Binary.PropositionalEquality public
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
    ℓ ℓ′ ℓ′′ : Level
    A W X Y Z X′ Y′ : CSet
    f g h f′ g′ : X →̇ Y
```

```agda
  unique : {A : Set ℓ} (P : A → Set ℓ′) → Set _
  unique P = ∀ {a b} → P a → P b → a ≡ b

  ∀∃! : {A : Set ℓ} (B : A → Set ℓ′) (P : ∀ x → B x → Set ℓ′′) → Set _
  ∀∃! B P = ∀ x → (Σ (B x) (P x)) × unique (P x)

  Commuter : (A : Set ℓ) → Set _
  Commuter A = Σ (A → CSet) λ π → (a b : A) (j : π a →̇ π b) → Set

  universal : {A : Set ℓ} → Commuter A → A → Set _
  universal {ℓ} {A} C a = let (π , comm) = C in
    ∀∃! (λ x → π x →̇ π a) λ x → comm x a
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
    TerminalDiagram : Set
    TerminalDiagram = CSet

    TerminalCommuter : Commuter TerminalDiagram
    TerminalCommuter = id⒨ , λ X T j → ⊤

    isTerminal : CSet → Set
    isTerminal = universal TerminalCommuter

    -- Axiom 2
    field AxTml : Σ CSet isTerminal
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
    -- Definition 2.6.2
    ProductDiagram : (X Y : CSet) → Set
    ProductDiagram X Y = Σ CSet λ P → P →̇ X × P →̇ Y

    ProductCommuter : Commuter (ProductDiagram X Y)
    ProductCommuter = fst , λ { (A , f , g) (P , p , q) h → p ∘ h ≡ f × q ∘ h ≡ g }

    isProduct : ProductDiagram X Y → Set
    isProduct = universal ProductCommuter
```

```agda
    -- Axiom 5
    field AxProd : Σ (ProductDiagram X Y) isProduct
```

```agda
    infixr 15 _×̇_
    _×̇_ : CSet → CSet → CSet
    X ×̇ Y = AxProd {X} {Y} .fst .fst

    infixr 5 _,̇_
    _,̇_ : A →̇ X → A →̇ Y → A →̇ X ×̇ Y
    f ,̇ g = AxProd .snd (_ , f , g) .fst .fst
```

### Axiom 6

```agda
    -- Definition 2.7.3
    FuncSetDiagram : (X Y : CSet) → Set
    FuncSetDiagram X Y = Σ CSet λ F → F ×̇ X →̇ Y

    FuncSetCommuter : Commuter (FuncSetDiagram X Y)
    FuncSetCommuter {X} = fst , λ { (A , q) (F , e) q̅ →
      ∀[ a ∈ A ] ∀[ x ∈ X ] q ⦅ a ,̇ x ⦆ ≡ e ⦅ q̅ ⦅ a ⦆ ,̇ x ⦆ }

    isFuncSet : FuncSetDiagram X Y → Set
    isFuncSet = universal FuncSetCommuter
```

```agda
    -- Axiom 6
    field AxFuncSet : Σ (FuncSetDiagram X Y) isFuncSet
```

### Axiom 7

```agda
    -- Definition 3.1.4
    _is-a-fibre-of_over_ : {U : CSet} (i : U →̇ X) (f : X →̇ Y) (y : Elm Y) → Set
    i is-a-fibre-of f over y = ∀[ u ∈ _ ] f ⦅ i ⦅ u ⦆ ⦆ ≡ y

    FibreDiagram : (f : X →̇ Y) (y : Elm Y) → Set
    FibreDiagram {X} f y = Σ CSet λ U → Σ (U →̇ X) λ i → i is-a-fibre-of f over y

    FibreCommuter : {f : X →̇ Y} {y : Elm Y} → Commuter (FibreDiagram f y)
    FibreCommuter = fst , λ { (A , q , fqa) (U , i , fiu) q̅ → q ≡ i ∘ q̅ }

    isFibre : {f : X →̇ Y} {y : Elm Y} → FibreDiagram f y → Set
    isFibre = universal FibreCommuter
```

```agda
    -- Axiom 7
    field AxFibre : {f : X →̇ Y} {y : Elm Y} → Σ (FibreDiagram f y) isFibre
```

### Axiom 8

```agda
    -- Definition 3.2.1
    SubClsDiagram : Set
    SubClsDiagram = Σ CSet λ Ω → Σ CSet λ T → T →̇ Ω

    SubClsCommuter : Commuter SubClsDiagram
    SubClsCommuter = fst , λ { (A , X , i) (Ω , T , t) χ → (eq : T ≡ １) →
      case eq of λ { refl → i is-a-fibre-of χ over t } }

    isSubCls : SubClsDiagram → Set
    isSubCls = universal SubClsCommuter
```

```agda
    -- Axiom 8
    field AxSubCls : Σ SubClsDiagram λ d@(_ , T , _) → T ≡ １ × isSubCls d
```

### Axiom 9

```agda
    -- Definition 3.3.2
    NatDiagram : Set
    NatDiagram = Σ CSet λ N → Elm N × N →̇ N

    NatCommuter : Commuter NatDiagram
    NatCommuter = fst , λ (N , z , σ) (X , a , r) x →
      ∀[ n ∈ N ] (x ⦅ z ⦆ ≡ a × x ⦅ σ ⦅ n ⦆ ⦆ ≡ r ⦅ x ⦅ n ⦆ ⦆)

    isNat : NatDiagram → Set
    isNat = universal NatCommuter
```

```agda
    -- Axiom 9
    field AxNat : Σ NatDiagram isNat
```

### Axiom 10

```agda
    ∃[∈]-syntax : (X : CSet) (P : Elm X → Set) → Set
    ∃[∈]-syntax X P = Σ (Elm X) P

    infix 3 ∃[∈]-syntax
    syntax ∃[∈]-syntax X (λ x → A) = ∃[ x ∈ X ] A
```

```agda
    -- Definition 3.1.8 ii
    surjective : (f : X →̇ Y) → Set
    surjective {X} {Y} f = ∀[ y ∈ Y ] ∃[ x ∈ X ] f ⦅ x ⦆ ≡ y

    -- Definition 3.4.1
    section : (f : X →̇ Y) (i : Y →̇ X) → Set
    section f i = f ∘ i ≡ id

    -- Axiom 10
    field AxChoice : surjective f → Σ (Y →̇ X) (section f)
```

```agda
record ETCS : Set₁ where
  field
    etcs : Σ Data Data.Axiom
  open Data (etcs .fst) public
  open Data.Axiom (etcs .snd) public
```
