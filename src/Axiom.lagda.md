---
title: 公理化结构集合论 (1 公理)
zhihu-tags: Agda, 集合论, 范畴论, 数学基础
---

# 公理化结构集合论 (1 公理)

> 交流Q群: 893531731  
> 本文源码: [Axiom.lagda.md](https://github.com/choukh/ETCS/blob/main/src/Axiom.lagda.md)  
> 高亮渲染: [Axiom.html](https://choukh.github.io/ETCS/Axiom.html)  

## 前言

本系列文章是对 Tom Leinster 在爱丁堡大学教授的本科课程「公理化结构集合论（ETCS）」讲义（以下简称「讲义」）的 Agda 形式化。 我们的符号选取和定义表述基本上遵循讲义, 而定理编号与讲义完全一致, 但由于 Agda 的特性而稍微调整了顺序.

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

本文是系列的第一篇, 我们引入 ETCS 的10条公理. 为了表示公理, 首先需要引入 ETCS 的原始概念, 讲义中称它们为资料 (the data), 有的地方也称之为原语 (primitives) , 语言 (language) 或签名 (signature).

## 原始概念

形式地, 我们的公理将在如下原始概念上展开表述.

- 一些称为集合的东西, 这样的集合 `X` 记作 `X : CSet`, 其中 C 来自范畴 (category).
- 对每个集合 `X` 和 `Y`, 一些称为「`X` 到 `Y` 的函数」的东西, 这样的函数 `f` 记作 `f : X →̇ Y`.
- 对每个集合 `X`, `Y` 和 `Z`, 一个称为「复合」的运算, 将每个 `f : X →̇ Y` 和 `g : Y →̇ Z` 赋值为一个函数 `g ∘ f : X →̇ Z`.
- 对每个集合 `X`, 一个称为「恒等函数」的东西, 记作 `id⟨ X ⟩ : X →̇ X`, `X` 可以从上下文推断出来时简记作 `id`.

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

我们会形式化讲义中没有编号的概念, 这些概念我们编号为 -1.

**定义 -1.1** 我们把关于集合的性质称为箭头模式 `Arrow`. 给定这样的性质 `A : Arrow`, 如果某集合 `X` 满足 `A`, 我们就把 `a : A X` 称为集合 `X` 的一套 `A`-箭头.

```agda
  Arrow : Set₁
  Arrow = CSet → Set
```

**定义 -1.2** 给定箭头模式 `A`, 由以下资料组成的东西称为 `A`-图式 (diagram), 记作 `Diagram A`.

- 一个集合 `X`
- `X` 的一套 `A`-箭头

其中 `X` 叫做图式的底集 (underlying set).

```agda
  Diagram : Arrow → Set
  Diagram = Σ CSet
```

**定义 -1.3** 给定箭头模式 `A`, 我们把关于两个 `A`-图式以及它们的底集间映射 `j` 的性质称为 `A`-交换模式, 记作 `Commuter A`. 对任意两个 `A`-图式 `a` `b` 以及它们的底集间映射 `j`, 如果它们满足一个 `A`-交换模式 `C : Commuter A`, 我们就称它们 `C`-交换, 记作 `C a b j`.

```agda
  Commuter : (A : Arrow) → Set₁
  Commuter A = ((X , _) (Y , _) : Diagram A) (j : X →̇ Y) → Set
```

**定义 -1.4** 给定一个 `A`-交换模式 `C` 和一个 `A`-图式 `b`, 我们称 `b` 满足 `C`-泛性质, 当且仅当对任意 `A`-图式 `a`, 存在唯一的底集间映射 `j` 使得 `a` `b` `j` 满足 `C`-交换.

```agda
  unique : {A : Set} (P : A → Set) → Set
  unique P = ∀ {a b} → P a → P b → a ≡ b

  universal : {A : Arrow} → Commuter A → Diagram A → Set
  universal {A} C b@(Y , _) = (a@(X , _) : Diagram A) →
    (Σ (X →̇ Y) λ j → C a b j) × unique (C a b)
```

我们约定用 `A` `W` `X` `Y` `Z` `X′` `Y′` 表示集合, 用 `f` `g` `h` `f′` `g′` 表示函数.

```agda
  variable
    A W X Y Z X′ Y′ : CSet
    f g h f′ g′ : X →̇ Y
```

## 公理

我们现在可以引入 ETCS 的10条公理.

```agda
  record Axiom : Set where
```

**公理 1** 以下三个命题成立.

1. 复合运算满足结合律.
2. 恒等函数是复合运算的左单位元.
3. 恒等函数是复合运算的右单位元.

```agda
    field
      -- Axiom 1
      AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      AxIdˡ : id ∘ f ≡ f
      AxIdʳ : f ∘ id ≡ f
```

**定义 2.3.1** 我们说一个集合 `T` 是终集合, 当且仅当对任意集合 `X`, 存在唯一的 `j : X →̇ T`. 注意终集合的图式没有箭头, 只有一个集合, 且终集合的交换模式是恒真.

```agda
    -- Definition 2.3.1
    Terminal : Arrow
    Terminal = λ _ → ⊤

    TerminalCommuter : Commuter Terminal
    TerminalCommuter = λ _ _ _ → ⊤

    isTerminal : Diagram Terminal → Set
    isTerminal = universal TerminalCommuter
```

**公理 2** 存在一个终集合.

```agda
    -- Axiom 2
    field AxTml : Σ (Diagram Terminal) isTerminal
```

我们把公理2承诺的集合记作 `１`, 因为它里面只有一个元素, 这会在下一章证明.

```agda
    １ : CSet
    １ = AxTml .fst .fst
```

**定义 2.3.6** 给定集合 `X`, 我们把 `１` 到 `X` 的函数称为 `X` 的元素, 其类型记作 `Elm X`. 我们将 `x : Elm X` 简记为 `x ∈ X`.

```agda
    -- Definition 2.3.6
    Elm : CSet → Set
    Elm = １ →̇_

    ∀[∈]-syntax : (X : CSet) (P : Elm X → Set) → Set
    ∀[∈]-syntax X P = (x : Elm X) → P x

    infix 3 ∀[∈]-syntax
    syntax ∀[∈]-syntax X (λ x → A) = ∀[ x ∈ X ] A
```

注意 `x ∈ X` 是一个声明而不是可以讨论真假的命题, 这一点与质料集合论 (ZFC等) 不同.

给定函数 `f : X →̇ Y` 和一个元素 `x ∈ X`, 我们把复合函数 `f ∘ x` 记作 `f ⦅ x ⦆`.

```agda
    infix 15 _⦅_⦆
    _⦅_⦆ : (f : X →̇ Y) → ∀[ x ∈ X ] Elm Y
    f ⦅ x ⦆ = f ∘ x
```

**公理 3** 对任意集合 `X Y : CSet` 以及函数 `f g : X →̇ Y`, 如果对任意 `x ∈ X` 都有 `f ⦅ x ⦆ ≡ g ⦅ x ⦆`, 那么 `f ≡ g`.

```agda
    -- Axiom 3
    field AxFunExt : (∀[ x ∈ X ] f ⦅ x ⦆ ≡ g ⦅ x ⦆) → f ≡ g
```

**定义 2.5.1** 我们称一个集合 `X` 为空集, 当且仅当对任意 `x ∈ X` 都有 `⊥`.

```agda
    -- Definition 2.5.1
    empty : CSet → Set
    empty X = ∀[ x ∈ X ] ⊥
```

**公理 4** 存在一个空集.

```agda
    -- Axiom 4
    field AxEmpty : Σ CSet empty
```

**定义 2.6.2** 给定集合 `X Y : CSet`, 我们按如下三步定义它们的积的泛性质.

第一步, 定义积的箭头, 它包含如下资料:

- 一个函数 `p : P →̇ X`
- 一个函数 `q : P →̇ Y`

于是一个积图式具有如下形式

![Image](https://pic4.zhimg.com/80/v2-4102e695eae0d63c5a11e9aef1af1ee5.png)

我们将这样的积图式简记作 `(P , p , q)`.

第二步, 定义积图式的交换: 我们说两个积图式 `(P , p , q)` 和 `(A , f , g)` 以及底集间映射 `h : P →̇ A` 交换, 当且仅当 `p ∘ h ≡ f` 且 `q ∘ h ≡ g`.

第三步, 定义积的泛性质: 我们说一个积图式 `(P , p , q)` 满足积的泛性质, 当且仅当对任意积图式 `(A , f , g)`, 存在唯一的底集间映射 `h : A →̇ P` 使得它们交换.

```agda
    -- Definition 2.6.2
    Product : (X Y : CSet) → Arrow
    Product X Y = λ P → P →̇ X × P →̇ Y

    ProductCommuter : Commuter (Product X Y)
    ProductCommuter = λ (A , f , g) (P , p , q) h → p ∘ h ≡ f × q ∘ h ≡ g

    isProduct : Diagram (Product X Y) → Set
    isProduct = universal ProductCommuter
```

**公理 5** 对任意集合 `X Y : CSet`, 存在积图式满足积的泛性质.

```agda
    -- Axiom 5
    field AxProd : Σ (Diagram (Product X Y)) isProduct
```

给定集合 `X Y : CSet`, 我们把公理5所承诺的积图式的底集称为 `X` 和 `Y` 的积, 记作 `X ×̇ Y`.

```agda
    infixr 15 _×̇_
    _×̇_ : CSet → CSet → CSet
    X ×̇ Y = AxProd {X} {Y} .fst .fst
```

给定集合 `X Y A : CSet` 和函数 `f : A →̇ X` `g : A →̇ Y`, 公理5承诺了积图示 `(A , f , g)` 到积图示 `(X ×̇ Y , p , q)` 的底集间唯一映射, 我们记作 `f ,̇ g : A →̇ X ×̇ Y`. 特别地, 当 `A ≡ １` 时, 我们记作 `f` 是 `X` 的元素, `g` 是 `Y` 的元素, `f ,̇ g` 是 `X ×̇ Y` 的元素.

```agda
    infixr 5 _,̇_
    _,̇_ : A →̇ X → A →̇ Y → A →̇ X ×̇ Y
    f ,̇ g = AxProd .snd (_ , f , g) .fst .fst
```

```agda
    -- Definition 2.7.3
    FuncSet : (X Y : CSet) → Arrow
    FuncSet X Y = λ F → F ×̇ X →̇ Y

    FuncSetCommuter : Commuter (FuncSet X Y)
    FuncSetCommuter {X} = λ (A , q) (F , e) q̅ →
      ∀[ a ∈ A ] ∀[ x ∈ X ] q ⦅ a ,̇ x ⦆ ≡ e ⦅ q̅ ⦅ a ⦆ ,̇ x ⦆

    isFuncSet : Diagram (FuncSet X Y) → Set
    isFuncSet = universal FuncSetCommuter
```

```agda
    -- Axiom 6
    field AxFuncSet : Σ (Diagram (FuncSet X Y)) isFuncSet
```

```agda
    -- Definition 3.1.4
    _isFibreOf_over_ : {U : CSet} (i : U →̇ X) (f : X →̇ Y) (y : Elm Y) → Set
    i isFibreOf f over y = ∀[ u ∈ _ ] f ⦅ i ⦅ u ⦆ ⦆ ≡ y

    Fibre : (f : X →̇ Y) (y : Elm Y) → Arrow
    Fibre {X} f y = λ U → Σ (U →̇ X) (_isFibreOf f over y)

    FibreCommuter : {f : X →̇ Y} {y : Elm Y} → Commuter (Fibre f y)
    FibreCommuter = λ (A , q , fqa) (U , i , fiu) q̅ → q ≡ i ∘ q̅

    isFibre : {f : X →̇ Y} {y : Elm Y} → Diagram (Fibre f y) → Set
    isFibre = universal FibreCommuter
```

```agda
    -- Axiom 7
    field AxFibre : {f : X →̇ Y} {y : Elm Y} → Σ (Diagram (Fibre f y)) isFibre
```

```agda
    -- Definition 3.2.1
    SubCls : Arrow
    SubCls = λ Ω → Σ CSet λ T → T →̇ Ω

    SubClsCommuter : Commuter SubCls
    SubClsCommuter = λ (A , X , i) (Ω , T , t) χ → (eq : T ≡ １) →
      case eq of λ { refl → i isFibreOf χ over t }

    isSubCls : Diagram SubCls → Set
    isSubCls = universal SubClsCommuter
```

```agda
    -- Axiom 8
    field AxSubCls : Σ (Diagram SubCls) λ d@(_ , T , _) → T ≡ １ × isSubCls d
```

```agda
    -- Definition 3.3.2
    Nat : Arrow
    Nat = λ N → Elm N × N →̇ N

    NatCommuter : Commuter Nat
    NatCommuter = λ (N , z , σ) (X , a , r) x →
      ∀[ n ∈ N ] (x ⦅ z ⦆ ≡ a × x ⦅ σ ⦅ n ⦆ ⦆ ≡ r ⦅ x ⦅ n ⦆ ⦆)

    isNat : Diagram Nat → Set
    isNat = universal NatCommuter
```

```agda
    -- Axiom 9
    field AxNat : Σ (Diagram Nat) isNat
```

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

## 总结

```agda
record ETCS : Set₁ where
  field
    etcs : Σ Data Data.Axiom
  open Data (etcs .fst) public
  open Data.Axiom (etcs .snd) public
```
