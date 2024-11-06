---
title: 公理化结构集合论 (1 - 公理)
zhihu-tags: Agda, 集合论, 范畴论, 数学基础
---

# 公理化结构集合论 (1 - 公理)

> 交流Q群: 893531731  
> 本文源码: [Axiom.lagda.md](https://github.com/choukh/ETCS/blob/main/src/Axiom.lagda.md)  
> 高亮渲染: [Axiom.html](https://choukh.github.io/ETCS/Axiom.html)  

## 前言

本系列文章是 Tom Leinster 在爱丁堡大学讲授的公理化结构集合论 (ETCS) 本科课程[讲义](https://www.maths.ed.ac.uk/~tl/ast/ast.pdf) (以下简称讲义) 的 Agda 形式化. 符号和定义基本上遵循讲义, 定理编号与讲义完全一致, 但由于 Agda 的特性而稍微调整了顺序.

我们采用原味 Agda 加 stdlib 标准库, 这是我们的元语言, 而 ETCS 将是我们的对象语言. 由于两层语言的高度相似性, 它们的符号/命名冲突我们主要采用如下两种方式解决.

1. 如果一个符号已经用于元语言 (如 `→`), 则在上面加点表示对象语言的相应概念 (如 `→̇`).
2. 如果一个符号优先用于对象语言 (如 `id`), 则在后面加上 `⒨` 表示元语言的相应概念 (如 `id⒨`).

```agda
module Axiom where

open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤; tt)
open import Data.Product public using (Σ; _×_; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Function public using (case_of_) renaming (id to id⒨)
open import Relation.Binary.PropositionalEquality public
```

本文是系列的第一篇, 我们引入 ETCS 的10条公理. 为了表示公理, 首先需要引入 ETCS 的原始概念, 讲义中称它们为资料 (the data), 也有称之为原语 (primitives) , 语言 (language) 或签名 (signature) 的.

## 原始概念

形式地, 我们的公理将在如下原始概念上展开表述.

- 一些称为集合的东西, 这样的集合 `X` 记作 `X : CSet`, 其中 C 来自范畴 (category).
- 对每个集合 `X` 和 `Y`, 一些称为「`X` 到 `Y` 的函数」的东西, 这样的函数 `f` 记作 `f : X →̇ Y`.
- 对每个集合 `X`, `Y` 和 `Z`, 一个称为「复合」的运算, 将每个 `f : X →̇ Y` 和 `g : Y →̇ Z` 赋值为一个函数 `g ∘ f : X →̇ Z`.
- 对每个集合 `X`, 一个称为「恒等函数」的东西, 记作 `id⟨ X ⟩ : X →̇ X`, `X` 可以从上下文推断出来时简记作 `id : X →̇ X`.

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
  unique : {A : Set} (P : A → Set) → Set
  unique P = ∀ {a b} → P a → P b → a ≡ b

  ∀∃! : {A : Set} (B : A → Set) (P : ∀ x → B x → Set ) → Set
  ∀∃! B P = ∀ x → (Σ (B x) (P x)) × unique (P x)

  Commuter : (A : Set) → Set₁
  Commuter A = Σ (A → CSet) λ π → (a b : A) (j : π a →̇ π b) → Set

  universal : {A : Set} → Commuter A → A → Set
  universal (π , comm) a = ∀∃! (λ x → π x →̇ π a) λ x → comm x a
```

我们约定用 `A W X Y Z X′ Y′` 表示集合, 用 `f g h f′ g′` 表示函数.

```agda
  variable
    A W X Y Z X′ Y′ : CSet
    f g h f′ g′ : X →̇ Y
```

## Axioms

```agda
  record Axiom : Set where
```

### Axiom 1

```agda
    field
      -- Axiom 1
      AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      AxIdˡ : id ∘ f ≡ f
      AxIdʳ : f ∘ id ≡ f
```

### Axiom 2

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

### Axiom 3

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

### Axiom 4

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
    _isFibreOf_over_ : {U : CSet} (i : U →̇ X) (f : X →̇ Y) (y : Elm Y) → Set
    i isFibreOf f over y = ∀[ u ∈ _ ] f ⦅ i ⦅ u ⦆ ⦆ ≡ y

    FibreDiagram : (f : X →̇ Y) (y : Elm Y) → Set
    FibreDiagram {X} f y = Σ CSet λ U → Σ (U →̇ X) (_isFibreOf f over y)

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
      case eq of λ { refl → i isFibreOf χ over t } }

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

## Summary

```agda
record ETCS : Set₁ where
  field
    etcs : Σ Data Data.Axiom
  open Data (etcs .fst) public
  open Data.Axiom (etcs .snd) public
```
