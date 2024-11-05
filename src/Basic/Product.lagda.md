```agda
open import Axiom
module Basic.Product (ℳ : ETCS) where
open ETCS ℳ

open import Basic.Isomorphism ℳ
open import Basic.Membership ℳ
open import Function using (_$_)
```

```agda
-- Lemma 2.6.6
isoInvariant-isProduct : isoInvariant⟨ ProductCommuter ⟩ (isProduct {X} {Y})
isoInvariant-isProduct {a = P , p , q} {b = P′ , p′ , q′}
  j (j⁻¹ , jj⁻¹ , j⁻¹j) (p′j , q′j) Pa c@(A , f , g) =
    let open ≡-Reasoning
        ((h , ph , qh) , u) = Pa c
        p′jh =                      begin
          p′ ∘ (j ∘ h)              ≡˘⟨ AxAss ⟩
          (p′ ∘ j) ∘ h              ≡⟨ cong (_∘ h) p′j ⟩
          p ∘ h                     ≡⟨ ph ⟩
          f                         ∎
        q′jh =                      begin
          q′ ∘ (j ∘ h)              ≡˘⟨ AxAss ⟩
          (q′ ∘ j) ∘ h              ≡⟨ cong (_∘ h) q′j ⟩
          q ∘ h                     ≡⟨ qh ⟩
          g                         ∎
    in
    (j ∘ h , p′jh , q′jh) , λ {h′₁} {h′₂} (p′h′₁ , q′h′₁) (p′h′₂ , q′h′₂) →
      let open ≡-Reasoning
          pj⁻¹h′₁ =                 begin
            p ∘ (j⁻¹ ∘ h′₁)         ≡˘⟨ AxAss ⟩
            (p ∘ j⁻¹) ∘ h′₁         ≡˘⟨ cong (_∘ h′₁) $ cong (_∘ j⁻¹) p′j ⟩
            ((p′ ∘ j) ∘ j⁻¹) ∘ h′₁  ≡⟨ cong (_∘ h′₁) (AssIdʳ jj⁻¹) ⟩
            p′ ∘ h′₁                ≡⟨ p′h′₁ ⟩
            f                       ∎
          qj⁻¹h′₁ =                 begin
            q ∘ (j⁻¹ ∘ h′₁)         ≡˘⟨ AxAss ⟩
            (q ∘ j⁻¹) ∘ h′₁         ≡˘⟨ cong (_∘ h′₁) $ cong (_∘ j⁻¹) q′j ⟩
            ((q′ ∘ j) ∘ j⁻¹) ∘ h′₁  ≡⟨ cong (_∘ h′₁) (AssIdʳ jj⁻¹) ⟩
            q′ ∘ h′₁                ≡⟨ q′h′₁ ⟩
            g                       ∎
          pj⁻¹h′₂ =                 begin
            p ∘ (j⁻¹ ∘ h′₂)         ≡˘⟨ AxAss ⟩
            (p ∘ j⁻¹) ∘ h′₂         ≡˘⟨ cong (_∘ h′₂) $ cong (_∘ j⁻¹) p′j ⟩
            ((p′ ∘ j) ∘ j⁻¹) ∘ h′₂  ≡⟨ cong (_∘ h′₂) (AssIdʳ jj⁻¹) ⟩
            p′ ∘ h′₂                ≡⟨ p′h′₂ ⟩
            f                       ∎
          qj⁻¹h′₂ =                 begin
            q ∘ (j⁻¹ ∘ h′₂)         ≡˘⟨ AxAss ⟩
            (q ∘ j⁻¹) ∘ h′₂         ≡˘⟨ cong (_∘ h′₂) $ cong (_∘ j⁻¹) q′j ⟩
            ((q′ ∘ j) ∘ j⁻¹) ∘ h′₂  ≡⟨ cong (_∘ h′₂) (AssIdʳ jj⁻¹) ⟩
            q′ ∘ h′₂                ≡⟨ q′h′₂ ⟩
            g                       ∎
      in
      h′₁                           ≡˘⟨ AssIdˡ jj⁻¹ ⟩
      j ∘ (j⁻¹ ∘ h′₁)               ≡⟨ cong (j ∘_) (u (pj⁻¹h′₁ , qj⁻¹h′₁) (pj⁻¹h′₂ , qj⁻¹h′₂)) ⟩
      j ∘ (j⁻¹ ∘ h′₂)               ≡⟨ AssIdˡ jj⁻¹ ⟩
      h′₂                           ∎
```

```agda
-- Exercise 2.6.7
isoInvariant-isProduct-XY : (a@(P , p , q) : ProductDiagram X Y)
  ((j , _) : X ≅ X′) ((k , _) : Y ≅ Y′) →
  isProduct a → isProduct (P , j ∘ p , k ∘ q)
isoInvariant-isProduct-XY a@(P , p , q) (j , j⁻¹ , jj⁻¹ , j⁻¹j) (k , k⁻¹ , kk⁻¹ , k⁻¹k) Pa c@(A , f , g) =
  let open ≡-Reasoning
      ((h , ph , qh) , u) = Pa (A , j⁻¹ ∘ f , k⁻¹ ∘ g)
      jph =                         begin
        (j ∘ p) ∘ h                 ≡⟨ AxAss ⟩
        j ∘ (p ∘ h)                 ≡⟨ cong (j ∘_) ph ⟩
        j ∘ (j⁻¹ ∘ f)               ≡⟨ AssIdˡ jj⁻¹ ⟩
        f                           ∎
      kqh =                         begin
        (k ∘ q) ∘ h                 ≡⟨ AxAss ⟩
        k ∘ (q ∘ h)                 ≡⟨ cong (k ∘_) qh ⟩
        k ∘ (k⁻¹ ∘ g)               ≡⟨ AssIdˡ kk⁻¹ ⟩
        g                           ∎
  in
  (h , jph , kqh) , λ {a = h₁} {b = h₂} (jph₁ , kqh₁) (jph₂ , kqh₂) →
    let open ≡-Reasoning
        ph₁ =                       begin
          p ∘ h₁                    ≡˘⟨ AssIdˡ j⁻¹j ⟩
          j⁻¹ ∘ (j ∘ (p ∘ h₁))      ≡˘⟨ cong (j⁻¹ ∘_) AxAss ⟩
          j⁻¹ ∘ ((j ∘ p) ∘ h₁)      ≡⟨ cong (j⁻¹ ∘_) jph₁ ⟩
          j⁻¹ ∘ f                   ∎
        qh₁ =                       begin
          q ∘ h₁                    ≡˘⟨ AssIdˡ k⁻¹k ⟩
          k⁻¹ ∘ (k ∘ (q ∘ h₁))      ≡˘⟨ cong (k⁻¹ ∘_) AxAss ⟩
          k⁻¹ ∘ ((k ∘ q) ∘ h₁)      ≡⟨ cong (k⁻¹ ∘_) kqh₁ ⟩
          k⁻¹ ∘ g                   ∎
        ph₂ =                       begin
          p ∘ h₂                    ≡˘⟨ AssIdˡ j⁻¹j ⟩
          j⁻¹ ∘ (j ∘ (p ∘ h₂))      ≡˘⟨ cong (j⁻¹ ∘_) AxAss ⟩
          j⁻¹ ∘ ((j ∘ p) ∘ h₂)      ≡⟨ cong (j⁻¹ ∘_) jph₂ ⟩
          j⁻¹ ∘ f                   ∎
        qh₂ =                       begin
          q ∘ h₂                    ≡˘⟨ AssIdˡ k⁻¹k ⟩
          k⁻¹ ∘ (k ∘ (q ∘ h₂))      ≡˘⟨ cong (k⁻¹ ∘_) AxAss ⟩
          k⁻¹ ∘ ((k ∘ q) ∘ h₂)      ≡⟨ cong (k⁻¹ ∘_) kqh₂ ⟩
          k⁻¹ ∘ g                   ∎
    in
    u (ph₁ , qh₁) (ph₂ , qh₂)
```

```agda
-- Lemma 2.6.8
isoUnique-isProduct : isoUnique⟨ ProductCommuter ⟩ (isProduct {X} {Y})
isoUnique-isProduct a@{a = P , p , q} b@{b = P′ , p′ , q′} Pa Pb =
  let open ≡-Reasoning
      ((j , p′j , q′j) , _) = Pb a
      ((j′ , pj′ , qj′) , _) = Pa b
      p′jj′ =                       begin
        p′ ∘ (j ∘ j′)               ≡˘⟨ AxAss ⟩
        (p′ ∘ j) ∘ j′               ≡⟨ cong (_∘ j′) p′j ⟩
        p ∘ j′                      ≡⟨ pj′ ⟩
        p′                          ∎
      q′jj′ =                       begin
        q′ ∘ (j ∘ j′)               ≡˘⟨ AxAss ⟩
        (q′ ∘ j) ∘ j′               ≡⟨ cong (_∘ j′) q′j ⟩
        q ∘ j′                      ≡⟨ qj′ ⟩
        q′                          ∎
      pj′j =                        begin
        p ∘ (j′ ∘ j)                ≡˘⟨ AxAss ⟩
        (p ∘ j′) ∘ j                ≡⟨ cong (_∘ j) pj′ ⟩
        p′ ∘ j                      ≡⟨ p′j ⟩
        p                           ∎
      qj′j =                        begin
        q ∘ (j′ ∘ j)                ≡˘⟨ AxAss ⟩
        (q ∘ j′) ∘ j                ≡⟨ cong (_∘ j) qj′ ⟩
        q′ ∘ j                      ≡⟨ q′j ⟩
        q                           ∎
      jj′ : j ∘ j′ ≡ id
      jj′ = Pb b .snd (p′jj′ , q′jj′) (AxIdʳ , AxIdʳ)
      j′j : j′ ∘ j ≡ id
      j′j = Pa a .snd (pj′j , qj′j) (AxIdʳ , AxIdʳ)
      c : p′ ∘ j ≡ p × q′ ∘ j ≡ q
      c = Pb a .fst .snd
      u : unique (λ j → p′ ∘ j ≡ p × q′ ∘ j ≡ q)
      u = Pb a .snd
  in j , (j′ , jj′ , j′j) , c , u
```

```agda
-- Lemma 2.6.10
,̇-distrib-∘ : {a : Elm A} → (f ,̇ g) ∘ a ≡ f ⦅ a ⦆ ,̇ g ⦅ a ⦆
,̇-distrib-∘ {f} {g} {a} = AxProd .snd (_ , f ⦅ a ⦆ , g ⦅ a ⦆) .snd (p , q) (pr₁-≡ , pr₂-≡) where
  p =                       begin
    pr₁ ∘ ((f ,̇ g) ∘ a)     ≡˘⟨ AxAss ⟩
    (pr₁ ∘ (f ,̇ g)) ∘ a     ≡⟨ cong (_∘ a) pr₁-≡ ⟩
    f ∘ a                   ∎ where open ≡-Reasoning
  q =                       begin
    pr₂ ∘ ((f ,̇ g) ∘ a)     ≡˘⟨ AxAss ⟩
    (pr₂ ∘ (f ,̇ g)) ∘ a     ≡⟨ cong (_∘ a) pr₂-≡ ⟩
    g ∘ a                   ∎ where open ≡-Reasoning
```

```agda
-- Examples 2.6.11 i
Δ⟨_⟩ : (X : CSet) → X →̇ X ×̇ X
Δ⟨ X ⟩ = id ,̇ id
```

```agda
-- Exercise 2.6.12
,̇-inj₁ : (f ,̇ g) ≡ (f′ ,̇ g′) → f ≡ f′
,̇-inj₁ {f} {g} {f′} {g′} eq = begin
  f                         ≡˘⟨ pr₁-≡ ⟩
  pr₁ ∘ (f ,̇ g)             ≡⟨ cong (pr₁ ∘_) eq ⟩
  pr₁ ∘ (f′ ,̇ g′)           ≡⟨ pr₁-≡ ⟩
  f′                        ∎ where open ≡-Reasoning

,̇-inj₂ : (f ,̇ g) ≡ (f′ ,̇ g′) → g ≡ g′
,̇-inj₂ {f} {g} {f′} {g′} eq = begin
  g                         ≡˘⟨ pr₂-≡ ⟩
  pr₂ ∘ (f ,̇ g)             ≡⟨ cong (pr₂ ∘_) eq ⟩
  pr₂ ∘ (f′ ,̇ g′)           ≡⟨ pr₂-≡ ⟩
  g′                        ∎ where open ≡-Reasoning
```

```agda
-- Lemma 2.6.13
module _ {X X′ Y Y′ : CSet} where
  _⟨×⟩_ : (f : X →̇ X′) (g : Y →̇ Y′) → X ×̇ Y →̇ X′ ×̇ Y′
  f ⟨×⟩ g = AxProd .snd (X ×̇ Y , f ∘ pr₁ , g ∘ pr₂) .fst .fst

  is⟨×⟩ : (f : X →̇ X′) (g : Y →̇ Y′) → X ×̇ Y →̇ X′ ×̇ Y′ → Set
  is⟨×⟩ f g k = ∀[ x ∈ X ] ∀[ y ∈ Y ] k ⦅ x ,̇ y ⦆ ≡ f ⦅ x ⦆ ,̇ g ⦅ y ⦆

  ⟨×⟩-unique : (f : X →̇ X′) (g : Y →̇ Y′) → unique (is⟨×⟩ f g)
  ⟨×⟩-unique f g {a = k} {b = k′} eq eq′ = AxFunExt λ p → begin
    k ∘ p                               ≡⟨ cong (k ∘_) ×̇-η ⟩
    k ⦅ pr₁ ⦅ p ⦆ ,̇ pr₂ ⦅ p ⦆ ⦆         ≡⟨ eq _ _ ⟩
    f ⦅ pr₁ ⦅ p ⦆ ⦆ ,̇ g ⦅ pr₂ ⦅ p ⦆ ⦆   ≡˘⟨ eq′ _ _ ⟩
    k′ ⦅ pr₁ ⦅ p ⦆ ,̇ pr₂ ⦅ p ⦆ ⦆        ≡˘⟨ cong (k′ ∘_) ×̇-η ⟩
    k′ ∘ p                              ∎ where open ≡-Reasoning

  ⟨×⟩-≡ : is⟨×⟩ f g (f ⟨×⟩ g)
  ⟨×⟩-≡ {f} {g} x y =             begin
    (f ⟨×⟩ g) ⦅ x ,̇ y ⦆           ≡⟨ ×̇-η ⟩
    pr₁ ∘ (f ⟨×⟩ g) ⦅ x ,̇ y ⦆ ,̇
    pr₂ ∘ (f ⟨×⟩ g) ⦅ x ,̇ y ⦆     ≡⟨ cong₂ _,̇_ eq₁ eq₂ ⟩
    f ⦅ x ⦆ ,̇ g ⦅ y ⦆             ∎ where
      open ≡-Reasoning
      eq₁ =                       begin
        pr₁ ∘ (f ⟨×⟩ g) ⦅ x ,̇ y ⦆ ≡˘⟨ AxAss ⟩
        (pr₁ ∘ f ⟨×⟩ g) ∘ (x ,̇ y) ≡⟨ cong (_∘ (x ,̇ y)) (AxProd .snd _ .fst .snd .fst) ⟩
        (f ∘ pr₁) ∘ (x ,̇ y)       ≡⟨ AxAss ⟩
        f ⦅ pr₁ ⦅ x ,̇ y ⦆ ⦆       ≡⟨ cong (f ∘_) pr₁-≡ ⟩
        f ⦅ x ⦆                   ∎
      eq₂ =                       begin
        pr₂ ∘ (f ⟨×⟩ g) ⦅ x ,̇ y ⦆ ≡˘⟨ AxAss ⟩
        (pr₂ ∘ f ⟨×⟩ g) ∘ (x ,̇ y) ≡⟨ cong (_∘ (x ,̇ y)) (AxProd .snd _ .fst .snd .snd) ⟩
        (g ∘ pr₂) ∘ (x ,̇ y)       ≡⟨ AxAss ⟩
        g ⦅ pr₂ ⦅ x ,̇ y ⦆ ⦆       ≡⟨ cong (g ∘_) pr₂-≡ ⟩
        g ⦅ y ⦆                   ∎
```

```agda
-- Proposition 2.6.15 i / Exercise 2.6.16
×̇-sym : X ×̇ Y ≅ Y ×̇ X
×̇-sym = {!   !}
```

```agda
-- Proposition 2.6.15 ii
×̇-idʳ : X ×̇ １ ≅ X
×̇-idʳ {X} = pr₁ , (id ,̇ !) , pr₁-≡ , AxFunExt λ p →
  let x = pr₁ ⦅ p ⦆
      * = pr₂ ⦅ p ⦆ in            begin
  ((id ,̇ !) ∘ pr₁) ∘ p            ≡⟨ AxAss ⟩
  (id ,̇ !) ⦅ x ⦆                  ≡⟨ ,̇-distrib-∘ ⟩
  id ⦅ x ⦆ ,̇ ! ⦅ x ⦆              ≡⟨ cong₂ _,̇_ AxIdˡ (oneElement-１ .snd) ⟩
  x ,̇ *                           ≡˘⟨ ×̇-η ⟩
  p                               ≡˘⟨ AxIdˡ ⟩
  id ∘ p                          ∎ where open ≡-Reasoning
```

```agda
-- Proposition 2.6.15 iii
×̇-assoc : X ×̇ (Y ×̇ Z) ≅ (X ×̇ Y) ×̇ Z
×̇-assoc = {!   !}
```
