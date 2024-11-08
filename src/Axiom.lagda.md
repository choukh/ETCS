---
title: 公理化结构集合论 (1 公理)
zhihu-tags: Agda, 集合论, 范畴论, 数学基础
zhihu-url: https://zhuanlan.zhihu.com/p/5630540119
---

# 公理化结构集合论 (1 公理)

> 交流Q群: 893531731  
> 本文源码: [Axiom.lagda.md](https://github.com/choukh/ETCS/blob/main/src/Axiom.lagda.md)  
> 高亮渲染: [Axiom.html](https://choukh.github.io/ETCS/Axiom.html)  

## 前言

本系列文章是对 Tom Leinster 在爱丁堡大学教授的本科课程「公理化结构集合论（ETCS）」[讲义](https://www.maths.ed.ac.uk/~tl/ast/ast.pdf)（以下简称「讲义」）的 Agda 形式化. 我们的符号选取和定义表述基本上遵循讲义, 而定理编号与讲义完全一致, 但由于 Agda 的特性而稍微调整了顺序. 注意我们讲的是一种可以作为数学基础的集合论而不是范畴论, 虽然借用了一些范畴论的术语和思想, 但不需要先掌握范畴论.

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

我们会形式化讲义中没有编号的定义和命题, 这些内容我们编号为负数.

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

**公理 1 (范畴)** 以下三个命题成立.

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

**公理 2 (终集)** 存在一个终集合.

```agda
    -- Axiom 2
    field AxTml : Σ (Diagram Terminal) isTerminal
```

我们将在后篇证明这样的终集合是唯一的. 实际上, 我们会证明所有用泛性质框定的集合都是唯一的. 所以定义了一种泛性质就唯一定义了一种集合, 所以我们后面会直接说「定义某种集合的泛性质」, 这应该理解为就是在「定义某种集合」.

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

    ∃[∈]-syntax : (X : CSet) (P : Elm X → Set) → Set
    ∃[∈]-syntax X P = Σ (Elm X) P

    infix 3 ∃[∈]-syntax
    syntax ∃[∈]-syntax X (λ x → A) = ∃[ x ∈ X ] A
```

**注意** `x ∈ X` 是一个声明而不是可以讨论真假的命题, 这一点与质料集合论 (ZFC等) 不同. 就像我们说「任意/存在集合 `X`, 怎么怎么样」一样, 这里不存在 「`X` 是不是集合」的问题, 我们也只能说「任意/存在元素 `x ∈ X`, 怎么怎么样」, 而不存在 「`x` 是不是 `X` 的元素」的问题.

给定函数 `f : X →̇ Y` 和一个元素 `x ∈ X`, 我们把复合函数 `f ∘ x` 记作 `f ⦅ x ⦆`.

```agda
    infix 15 _⦅_⦆
    _⦅_⦆ : (f : X →̇ Y) → ∀[ x ∈ X ] Elm Y
    f ⦅ x ⦆ = f ∘ x
```

**公理 3 (函数外延)** 对任意集合 `X Y : CSet` 以及函数 `f g : X →̇ Y`, 如果对任意 `x ∈ X` 都有 `f ⦅ x ⦆ ≡ g ⦅ x ⦆`, 那么 `f ≡ g`.

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

**公理 4 (空集)** 存在一个空集.

```agda
    -- Axiom 4
    field AxEmpty : Σ CSet empty
```

**定义 2.6.2** 给定集合 `X Y : CSet`, 我们按以下三步定义它们的积的泛性质.

第一步, 定义积图式, 它包含如下资料:

- 一个集合 `P`
- 一个函数 `p : P →̇ X`
- 一个函数 `q : P →̇ Y`

于是一个积图式具有如下形式

![积图式](https://pic4.zhimg.com/80/v2-7e2a8ae22d3645250a1f82970ba78df1.png)

我们将这样的积图式简记作 `(P , p , q)`.

第二步, 定义积图式的交换: 我们说两个积图式 `(A , f , g)` 和 `(P , p , q)` 以及底集间映射 `h : A →̇ P` 交换, 当且仅当 `p ∘ h ≡ f` 且 `q ∘ h ≡ g`.

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

**公理 5 (积)** 对任意集合 `X Y : CSet`, 存在积图式满足积的泛性质.

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

给定集合 `X Y A : CSet` 和函数 `f : A →̇ X` `g : A →̇ Y`, 公理5承诺了积图示 `(A , f , g)` 到积图示 `(X ×̇ Y , p , q)` 的底集间唯一映射, 我们记作 `f ,̇ g : A →̇ X ×̇ Y`. 如下图所示, 其中虚线表示唯一. 特别地, 当 `A ≡ １` 时, `f` 是 `X` 的元素, `g` 是 `Y` 的元素, `f ,̇ g` 是 `X ×̇ Y` 的元素.

![积的元素](https://pic4.zhimg.com/80/v2-2cfcd05207f77e2d965658d158731767.png)

```agda
    infixr 5 _,̇_
    _,̇_ : A →̇ X → A →̇ Y → A →̇ X ×̇ Y
    f ,̇ g = AxProd .snd (_ , f , g) .fst .fst
```

**定义 2.7.3** 给定集合 `X Y : CSet`, 我们按以下三步定义它们的函数集 (简称幂) 的泛性质.

第一步, 定义幂图式, 它包含如下资料:

- 一个集合 `F`
- 一个函数 `e : F ×̇ X →̇ Y`

简记作 `(F , e)`.

第二步, 定义幂图式的交换: 我们说两个幂图式 `(A , q)` 和 `(F , e)` 以及底集间映射 `q̅ : A →̇ F` 交换, 当且仅当对任意 `a ∈ A` 和 `x ∈ X` 都有 `q ⦅ a ,̇ x ⦆ ≡ e ⦅ q̅ ⦅ a ⦆ ,̇ x ⦆`.

第三步, 定义幂的泛性质: 我们说一个幂图式 `(F , e)` 满足幂的泛性质, 当且仅当对任意幂图式 `(A , q)`, 存在唯一的底集间映射 `q̅ : A →̇ F` 使得它们交换.

![幂的泛性质](https://pic4.zhimg.com/80/v2-2874a6ccdc996e99f8027e4b11e2383d.png)

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

**公理 6 (幂)** 对任意集合 `X Y : CSet`, 存在幂图式满足幂的泛性质.

```agda
    -- Axiom 6
    field AxFuncSet : Σ (Diagram (FuncSet X Y)) isFuncSet
```

**定义 3.1.4** 给定函数 `f : X →̇ Y` 和元素 `y ∈ Y`, 我们按以下四步定义关于 `f` 和 `y` 的纤维的泛性质.

第零步, 定义什么叫纤维: 我们说一个集合 `U` 配合上一个包含函数 `i : U →̇ X` 是 `f` 在 `y` 上的纤维, 记作 `U withInclusion i isFibreOf f over y`, 当且仅当对任意 `u ∈ U` 都有 `f ⦅ i ⦅ u ⦆ ⦆ ≡ y`, 也就是下图交换. 由于这样的 `U` 一般又记作 $f^{-1}(y)$, 图中用此记法.

第一步, 定义纤维图式, 它包含如下资料:

- 一个集合 `U`
- 一个函数 `i : U →̇ X`
- 一个证明: `U` 配合上一个包含函数 `i : U →̇ X` 是 `f` 在 `y` 上的纤维

简记作 `(U , i , fiu)`.

![纤维图式](https://pic4.zhimg.com/80/v2-bcacd8638c0c142fb4422fe291b632f7.png)

第二步, 定义纤维图式的交换: 我们说两个纤维图式 `(A , q , fqa)` 和 `(U , i , fiu)` 以及底集间映射 `q̅ : A →̇ U` 交换, 当且仅当 `q ≡ i ∘ q̅`.

第三步, 定义纤维的泛性质: 我们说一个纤维图式 `(U , i , fiu)` 满足纤维的泛性质, 当且仅当对任意纤维图式 `(A , q , fqa)`, 存在唯一的底集间映射 `q̅ : A →̇ U` 使得它们交换.

![纤维的泛性质](https://pic4.zhimg.com/80/v2-0f5d1b447ca9b15abfd4df13ad044223.png)

```agda
    -- Definition 3.1.4
    _withInclusion_isFibreOf_over_ : (U : CSet) (i : U →̇ X) (f : X →̇ Y) (y : Elm Y) → Set
    U withInclusion i isFibreOf f over y = ∀[ u ∈ _ ] f ⦅ i ⦅ u ⦆ ⦆ ≡ y

    Fibre : (f : X →̇ Y) (y : Elm Y) → Arrow
    Fibre {X} f y = λ U → Σ (U →̇ X) λ i → U withInclusion i isFibreOf f over y

    FibreCommuter : {f : X →̇ Y} {y : Elm Y} → Commuter (Fibre f y)
    FibreCommuter = λ (A , q , fqa) (U , i , fiu) q̅ → q ≡ i ∘ q̅

    isFibre : {f : X →̇ Y} {y : Elm Y} → Diagram (Fibre f y) → Set
    isFibre = universal FibreCommuter
```

**公理 7 (纤维)** 对任意 `f : X →̇ Y` 和元素 `y ∈ Y`, 存在纤维图式满足纤维的泛性质.

```agda
    -- Axiom 7
    field AxFibre : {f : X →̇ Y} {y : Elm Y} → Σ (Diagram (Fibre f y)) isFibre
```

**定义 3.2.1** 我们按以下三步定义子集分类器的泛性质.

第一步, 我们定义子集分类器图式, 它包含如下资料:

- 一个集合 `Ω`
- 一个集合 `T`
- 一个函数 `t : T →̇ Ω`

简记作 `(Ω , T , t)`.

第二步, 定义子集分类器图式的交换: 我们说两个子集分类器图式 `(A , X , i)` 和 `(Ω , T , t)` 以及底集间映射 `χ : A →̇ Ω` 交换, 当且仅当如果 `T ≡ １`, 那么 `X` 配合上 `i` 是 `χ` 在 `t` 上的纤维.

第三步, 定义子集分类器的泛性质: 我们说一个子集分类器图式 `(Ω , T , t)` 满足子集分类器的泛性质, 当且仅当对任意子集分类器图式 `(A , X , i)`, 存在唯一的底集间映射 `χ : A →̇ Ω` 使得它们交换.

![子集分类器的泛性质](https://pic4.zhimg.com/80/v2-f1f7a1eec3df674886ffa5161566c82b.png)

```agda
    -- Definition 3.2.1
    SubCls : Arrow
    SubCls = λ Ω → Σ CSet λ T → T →̇ Ω

    SubClsCommuter : Commuter SubCls
    SubClsCommuter = λ (A , X , i) (Ω , T , t) χ → (eq : T ≡ １) →
      case eq of λ { refl → X withInclusion i isFibreOf χ over t }

    isSubCls : Diagram SubCls → Set
    isSubCls = universal SubClsCommuter
```

**公理 8 (子集)** 存在一个子集分类器图式 `(Ω , １ , t)` 满足子集分类器的泛性质.

```agda
    -- Axiom 8
    field AxSubCls : Σ (Diagram SubCls) λ d@(_ , T , _) → T ≡ １ × isSubCls d
```

**定义 3.3.2** 我们按以下三步定义自然数集的泛性质.

第一步, 定义自然数图式, 它包含如下资料:

- 一个集合 `N`
- 一个元素 `z ∈ N`
- 一个函数 `σ : N →̇ N`

第二步, 定义自然数图式的交换: 我们说两个自然数图式 `(N , z , σ)` 和 `(X , a , r)` 以及底集间映射 `x : N →̇ X` 交换, 当且仅当对任意 `n ∈ N` 都有 `x ⦅ z ⦆ ≡ a` 且 `x ⦅ σ ⦅ n ⦆ ⦆ ≡ r ⦅ x ⦅ n ⦆ ⦆`.

第三步, 定义自然数的泛性质: 我们说一个自然数图式 `(N , z , σ)` 满足自然数的泛性质, 当且仅当对任意自然数图式 `(X , a , r)`, 存在唯一的底集间映射 `x : N →̇ X` 使得它们交换.

![自然数的泛性质](https://pic4.zhimg.com/80/v2-a643f6546c3ea362bb62336c01d46535.png)

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

**公理 9 (自然数)** 存在一个自然数图式满足自然数的泛性质.

```agda
    -- Axiom 9
    field AxNat : Σ (Diagram Nat) isNat
```

**定义 3.1.8 ii** 给定函数 `f : X →̇ Y`, 我们称 `f` 是满射, 当且仅当对任意 `y ∈ Y` 都存在 `x ∈ X` 使得 `f ⦅ x ⦆ ≡ y`.

```agda
    -- Definition 3.1.8 ii
    surjective : (f : X →̇ Y) → Set
    surjective {X} {Y} f = ∀[ y ∈ Y ] ∃[ x ∈ X ] f ⦅ x ⦆ ≡ y
```

**定义 3.4.1** 给定函数 `f : X →̇ Y` 和 `i : Y →̇ X`, 我们称 `i` 是 `f` 的截面, 当且仅当 `f ∘ i ≡ id`.

```agda
    -- Definition 3.4.1
    section : (f : X →̇ Y) (i : Y →̇ X) → Set
    section f i = f ∘ i ≡ id
```

**公理 10 (选择)** 如果 `f : X →̇ Y` 是满射, 那么存在 `f` 的一个截面 `i : Y →̇ X`.

```agda
    -- Axiom 10
    field AxChoice : surjective f → Σ (Y →̇ X) (section f)
```

## 总结

以下是对公理化的总结. 我们的公理适用于以下资料：

- 一些称为集合的东西;
- 对于每个集合 `X` 和集合 `Y`, 一些称为从 `X` 到 `Y` 的函数, 我们用 `f : X →̇ Y` 表示从 `X` 到 `Y` 的函数 `f`;
- 对于每个集合 `X`, 集合 `Y` 和集合 `X`, 一个称为复合的运算, 将每对函数 `f : X →̇ Y` 和 `g : Y →̇ Z` 赋予一个函数 `f ∘ g : X →̇ Z`;
- 对于每个集合 `X`， 一个函数 `id : X →̇ X`, 称为 `X` 的恒等函数.

公理：

1. 函数的复合满足结合律, 并且恒等函数起到恒等作用.
2. 存在一个终集.
3. 函数外延性成立.
4. 存在一个空集.
5. 给定集合 `X` 和 `Y`, 存在 `X` 和 `Y` 的积.
6. 给定集合 `X` 和 `Y`, 存在 `X` 到 `Y` 的函数集.
7. 给定函数 `f : X →̇ Y` 和元素 `y ∈ Y`, 存在 `f` 在 `y` 上的纤维.
8. 存在一个子集分类器.
9. 存在一个自然数系统.
10. 每个满射都有一个截面.

公理 3, 4 和 7 都涉及到元素, 它定义为定义域为终集 `１` 的函数. 公理 2 以及 5–9 都涉及到泛性质, 并且所有这些公理唯一地刻画了涉及的集合 (在同构意义上), 这将在接下来的几篇中证明.

为了方便后面引用, 我们将以上资料和公理统称为 `ETCS` 理论.

```agda
record ETCS : Set₁ where
  field
    etcs : Σ Data Data.Axiom
  open Data (etcs .fst) public
  open Data.Axiom (etcs .snd) public
```
