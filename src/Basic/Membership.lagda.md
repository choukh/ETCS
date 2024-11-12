---
title: 公理化结构集合论 (3 元素)
zhihu-tags: Agda, 集合论, 范畴论, 数学基础
zhihu-url: https://zhuanlan.zhihu.com/p/6444134432
---

# 公理化结构集合论 (3 元素)

> 交流Q群: 893531731  
> 本文源码: [Membership.lagda.md](https://github.com/choukh/ETCS/blob/main/src/Basic/Membership.lagda.md)  
> 高亮渲染: [Membership.html](https://choukh.github.io/ETCS/Basic.Membership.html)  

我们知道, 质料集合论 (material set theory), 如 ZFC 等, 以命题性的全局成员关系 (membership) $\in$ 为原始概念. 而这里讲的结构集合论 ETCS, 其成员关系从作为原始概念的函数箭头 `→̇` 导出, 并且不是一个可以讨论真假的命题.

回顾第一篇[公理化结构集合论 (1 公理)](https://zhuanlan.zhihu.com/p/5630540119): 公理2承诺终集 (terminal set) 存在, 我们把它记作 `１`, 而 `１` 到 `X` 的函数则称为 `X` 的元素. 本篇将说明这一公理和定义的合理性.

```agda
open import Axiom
module Basic.Membership (ℳ : ETCS) where
open ETCS ℳ

open import Basic.Isomorphism ℳ
open import Function using (_$_)
open import Relation.Nullary using (¬_)
```

**引理 2.3.7** 元素的定义与公理1「相容」.

- 恒等函数的良定性: `id` 作用于任意元素都等于该元素自身.
- 复合运算的良定性: $(g ∘ f)( x ) = g ( f ( x ) )$.

**(证明)** 由公理1和元素的定义即得. □

```agda
-- Lemma 2.3.7
id-wellDefined : ∀[ x ∈ X ] id ⦅ x ⦆ ≡ x
id-wellDefined x = AxIdˡ

∘-wellDefined : ∀[ x ∈ X ] (g ∘ f) ⦅ x ⦆ ≡ g ⦅ f ⦅ x ⦆ ⦆
∘-wellDefined _ = AxAss
```

**引理 2.3.3** 终集在同构意义下不变: 与终集同构的集合也是终集.  
**(证明)** 假设 `T` 是终集且 `T ≅ T″`, 给定集合 `X`. 要证 `T′` 是终极, 只要证存在唯一的函数 `T′ →̇ X`.

存在性: 由于 `T` 是终集, 有唯一的函数 `X →̇ T`, 记作 `f`. `j ∘ f : T′ →̇ X` 就是所需函数, 其中 `j : T →̇ T′` 是假设的同构.

唯一性: 设 `f′ g′ : T′ →̇ X`. 由于 `X →̇ T` 唯一, 所以 $j^{-1} ∘ f' = j^{-1} ∘ g'$, 所以

$$
\begin{aligned}
f' &= j ∘ (j^{-1} ∘ f') \\
&= j ∘ (j^{-1} ∘ g') \\
&= g' \quad \square
\end {aligned}
$$

```agda
-- Lemma 2.3.3
isoInvariant-isTerminal : isoInvariant⟨ TerminalCommuter ⟩ isTerminal
isoInvariant-isTerminal {a = T} {b = T′} j (j⁻¹ , jj⁻¹ , _) tt tml X =
  let (f , tt) , f! = tml X in
  (j ∘ f , tt) , λ {f′ g′} _ _ → begin
    f′                      ≡˘⟨ AssIdˡ jj⁻¹ ⟩
    j ∘ (j⁻¹ ∘ f′)          ≡⟨ cong (j ∘_) (f! tt tt) ⟩
    j ∘ (j⁻¹ ∘ g′)          ≡⟨ AssIdˡ jj⁻¹ ⟩
    g′                      ∎ where open ≡-Reasoning
```

**引理 2.3.4** 终集在同构意义下唯一: 任意两个终集存在唯一同构.  
**(证明)** 令 `T` `T′` 是终集, 由终集的定义, 存在 `f : T →̇ T′` 与 `f′ : T′ →̇ T`. 且由终集的定义, 某终集到其自身的函数 `id` 也是唯一的, 所以 `f ∘ f′ ≡ id` 且 `f′ ∘ f ≡ id`. 因此 `f` 是 `T` 与 `T′` 的同构. 其唯一性由终集的定义即得. □

```agda
-- Lemma 2.3.4
isoUnique-isTerminal : isoUnique⟨ TerminalCommuter ⟩ isTerminal
isoUnique-isTerminal a@{T , _} b@{T′ , _} ta tb =
  let f : T →̇ T′
      f = tb a .fst .fst
      f′ : T′ →̇ T
      f′ = ta b .fst .fst
      ff′ : f ∘ f′ ≡ id
      ff′ = tb b .snd tt tt
      f′f : f′ ∘ f ≡ id
      f′f = ta a .snd tt tt
      f≡g : {f g : T →̇ T′} → f ≡ g
      f≡g = tb a .snd tt tt
  in f , (f′ , ff′ , f′f) , tt , λ _ _ → f≡g
```

我们把到终集的唯一函数记作 `!`, 特别地, 终集的元素记作 `*`.

```agda
!⟨_⟩ : (X : CSet) → X →̇ １
!⟨ X ⟩ = AxTml .snd (X , tt) .fst .fst

! : X →̇ １
! {X} = !⟨ X ⟩

* : Elm １
* = !
```

**例 2.5.2** `１` 不是空集.

```agda
-- Example 2.5.2
_ : ¬ empty １
_ = λ p → p *
```

我们说一个集合 `X` 是单集, 记作 `isSingleton X`, 当且仅当存在 `Elm X` 且对任意 `x y : Elm X` 有 `x ≡ y`. 显然, `１` 是单集.

```agda
isSingleton : CSet → Set
isSingleton X = Elm X × ∀ {x y : Elm X} → x ≡ y

isSingleton-１ : isSingleton １
isSingleton-１ = * , AxTml .snd (１ , tt) .snd tt tt
```

**引理 2.4.1** 终集是单集, 反之亦然.  
**(证明)** 左到右显然成立. 右到左, 给定单集 `X`, 将其唯一元素记作 `x`. 由引理 2.3.3, 我们证 `X` 与 `１` 同构即可. 我们有 `x : １ →̇ X` 和 `! : １ →̇ X`, 只需证它们互逆. 由终集的定义可得 `! ∘ x ≡ id`. 最后用公理3证 `x ∘ ! ≡ id`, 即证对任意 `y ∈ X` 有 `(x ∘ !) ⦅ y ⦆ ≡ id ⦅ y ⦆`. 由公理1, 左边等于 `x`, 右边等于 `y`. 由于 `x` 唯一, 所以 `x ≡ y`. □

```agda
-- Lemma 2.4.1
isTerminal→isSingleton : isTerminal (X , tt) → isSingleton X
isTerminal→isSingleton tml = tml (１ , tt) .fst .fst , tml (１ , tt) .snd tt tt

isSingleton→isTerminal : isSingleton X → isTerminal (X , tt)
isSingleton→isTerminal (x , x!) = isoInvariant-isTerminal
  x (! , AxFunExt q , p) tt (AxTml .snd) where
    p : {x y : Elm １} → x ≡ y
    p = AxTml .snd (１ , tt) .snd tt tt
    q = λ y →         begin
      (x ∘ !) ⦅ y ⦆   ≡⟨ AssIdʳ p ⟩
      x               ≡⟨ x! ⟩
      y               ≡˘⟨ AxIdˡ ⟩
      id ⦅ y ⦆        ∎ where open ≡-Reasoning
```
