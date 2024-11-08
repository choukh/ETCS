---
title: 公理化结构集合论 (2 同构)
zhihu-tags: Agda, 集合论, 范畴论, 数学基础
zhihu-url: https://zhuanlan.zhihu.com/p/5704241251
---

# 公理化结构集合论 (2 同构)

> 交流Q群: 893531731  
> 本文源码: [Isomorphism.lagda.md](https://github.com/choukh/ETCS/blob/main/src/Basic/Isomorphism.lagda.md)  
> 高亮渲染: [Isomorphism.html](https://choukh.github.io/ETCS/Basic.Isomorphism.html)  

上一篇我们引入了 `ETCS` 的10条公理, 本篇我们关注公理1的结论. 公理1包含三部分, 重新给出如下.

- 复合运算满足结合律 `AxAss : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)`
- 恒等函数是复合运算的左单位元 `AxIdˡ : id ∘ f ≡ f`
- 恒等函数是复合运算的右单位元 `AxIdʳ : f ∘ id ≡ f`

```agda
open import Axiom
module Basic.Isomorphism (ℳ : ETCS) where
open ETCS ℳ
```

**引理 -2.1** 以下两条等式成立, 它们会在后面经常用到.

- 如果 $h ∘ g = \text{id}$, 那么 $h ∘ (g ∘ f) = f$
- 如果 $g ∘ h ≡ \text{id}$, 那么 $(f ∘ g) ∘ h ≡ f$

**(证明)** 公理1的直接推论, 如代码所示.

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

**定义 2.2.2** 给定函数 `f : X →̇ Y`, 我们说一个函数 `g : Y →̇ X` 是 `f` 的逆, 记作 `isInv f g`, 当且仅当 `f ∘ g ≡ id` 且 `g ∘ f ≡ id`.

```agda
-- Definition 2.2.2
isInv : (f : X →̇ Y) (g : Y →̇ X) → Set
isInv f g = f ∘ g ≡ id × g ∘ f ≡ id
```

**引理 2.2.4** 任意函数的逆 (如果存在) 是唯一的.  
**(证明)** 给定函数 `f : X →̇ Y` 及其逆 `g g′ : Y →̇ X`, 要证 `g ≡ g′`. 由引理 -2.1 及逆的定义有

$$
g = g ∘ \text{id} = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = \text{id} ∘ g' = g' \quad \square
$$

```agda
-- Lemma 2.2.4
unique-isInv : unique (isInv f)
unique-isInv {f} {a = g} {b = g′} (_ , p) (q , _) = begin
  g             ≡˘⟨ AssIdʳ q ⟩
  (g ∘ f) ∘ g′  ≡⟨ AxAss ⟩
  g ∘ (f ∘ g′)  ≡⟨ AssIdˡ p ⟩
  g′            ∎ where open ≡-Reasoning
```

**定义 2.2.5** 给定函数 `f : X →̇ Y`, 我们说 `f` 是同构, 当且仅当存在函数 `g : Y →̇ X` 是 `f` 的逆, 记作 `isIso f`.

```agda
-- Definition 2.2.5
isIso : (f : X →̇ Y) → Set
isIso {X} {Y} f = Σ (Y →̇ X) λ g → isInv f g
```

**定义 2.2.8** 我们说两个集合 `X` 和 `Y` 同构, 记作 `X ≅ Y`, 当且仅当存在一个同构函数 `f : X →̇ Y`.

```agda
-- Definition 2.2.8
infix 10 _≅_
_≅_ : CSet → CSet → Set
X ≅ Y = Σ (X →̇ Y) isIso
```

**引理 2.2.6** 以下命题成立.

- i.   恒等函数 `id` 是同构.
- ii.  如果 `f` 和 `g` 是同构, 那么 `g ∘ f` 也是同构.
- iii. 如果 `f` 是同构, 那么它的逆, 记作 `f⁻¹`, 也是同构.

**(证明)** 对于 i, 由公理1的 `AxIdˡ` 或 `AxIdʳ` 均可得 `id ∘ id ≡ id`, 所以 `id` 是 `id` 的逆.

```agda
-- Lemma 2.2.6
isIso-id : isIso id⟨ X ⟩
isIso-id = id , AxIdˡ , AxIdˡ
```

对于 ii, 给定同构 `f` 和 `g`, 将它们的逆分别记作 `f⁻¹` 和 `g⁻¹`, 则 `f⁻¹ ∘ g⁻¹` 就是 `(g ∘ f)` 的逆, 只需证

- $(g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) = \text{id}$
- $(f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) = \text{id}$

反复应用公理1和逆的定义即可, 如代码所示.

```agda
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
```

对于 iii, 给定同构 `f` 及其逆 `f⁻¹`, 则 `f⁻¹` 的逆就是 `f`, 只需调换证据的顺序即可. □

```agda
isIso-⁻¹ : ((f⁻¹ , _) : isIso f) → isIso f⁻¹
isIso-⁻¹ {f} (f⁻¹ , p , q) = f , q , p
```

**引理 2.2.9** 以下命题成立.

- i.   同构关系是自反的: $X ≅ X$
- ii.  同构关系是传递的: 如果 $X ≅ Y$ 且 $Y ≅ Z$, 那么 $X ≅ Z$
- iii. 同构关系是对称的: 如果 $X ≅ Y$, 那么 $Y ≅ X$

**(证明)** 引理 2.2.6 的直接推论. □

```agda
-- Lemma 2.2.9
≅-refl : X ≅ X
≅-refl = id , isIso-id

≅-trans : X ≅ Y → Y ≅ Z → X ≅ Z
≅-trans (f , if) (g , ig) = g ∘ f , isIso-∘ if ig

≅-sym : X ≅ Y → Y ≅ X
≅-sym (f , i@(f⁻¹ , _)) = f⁻¹ , isIso-⁻¹ i
```

有了同构的概念, 就可以定义什么叫「在同构意义下不变」和「在同构意义下唯一」. 后篇将会证明上一篇用泛性质表述的公理所涉及的概念都满足这两个性质.

**定义 -2.2** 给定一个 `A`-交换模式 `C`, 我们说关于 `A`-图式的性质 `P` (如果存在见证) 在 `C`-同构意义下不变, 记作 `isoInvariant⟨ C ⟩ P`, 当且仅当对任意 `A`-图式 `a` 和 `b` 以及它们的底集间同构 `j` 有: 如果 `a` `b` `j` 满足 `C`-交换, 那么 `a` 满足 `P` 蕴含 `b` 满足 `P`.

```agda
isoInvariant⟨_⟩ : {A : Arrow} (C : Commuter A) (P : Diagram A → Set) → Set
isoInvariant⟨_⟩ {A} C P = {a@(X , _) b@(Y , _) : Diagram A}
  (j : X →̇ Y) → isIso j → C a b j → P a → P b
```

**定义 -2.3** 给定一个 `A`-交换模式 `C`, 我们说关于 `A`-图式的性质 `P` (如果存在见证) 在 `C`-同构意义下唯一, 记作 `isoUnique⟨ C ⟩ P`, 当且仅当对任意 `A`-图式 `a` 和 `b` 有: 如果 `a` 满足 `P` 且 `b` 满足 `P`, 那么存在唯一的底集间同构 `j` 使得 `a` `b` `j` 满足 `C`-交换.

```agda
isoUnique⟨_⟩ : {A : Arrow} (C : Commuter A) (P : Diagram A → Set) → Set
isoUnique⟨_⟩ {A} C P = {a@(X , _) b@(Y , _) : Diagram A} →
  P a → P b → Σ (X →̇ Y) λ j → isIso j × C a b j × unique (C a b)
```
