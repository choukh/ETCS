```agda
open import Axiom
module Axiom.PartOne (ℳ : ETCS) where
open ETCS ℳ

open import Function
  using (_$_) renaming (id to idᴹ)
open import Relation.Nullary using (¬_)
```

```agda
AssIdˡ : {f : X ⇒ Y} {g : Y ⇒ Z} {h : Z ⇒ Y} → h ∘ g ≡ id → h ∘ (g ∘ f) ≡ f
AssIdˡ {f} {g} {h} hg = begin
  h ∘ (g ∘ f)           ≡˘⟨ AxAss ⟩
  (h ∘ g) ∘ f           ≡⟨ cong (_∘ f) hg ⟩
  id ∘ f                ≡⟨ AxIdˡ ⟩
  f                     ∎ where open ≡-Reasoning

AssIdʳ : {f : X ⇒ Y} {g : W ⇒ X} {h : X ⇒ W} → g ∘ h ≡ id → (f ∘ g) ∘ h ≡ f
AssIdʳ {f} {g} {h} hg = begin
  (f ∘ g) ∘ h           ≡⟨ AxAss ⟩
  f ∘ (g ∘ h)           ≡⟨ cong (f ∘_) hg ⟩
  f ∘ id                ≡⟨ AxIdʳ ⟩
  f                     ∎ where open ≡-Reasoning
```

```agda
-- Definition 2.2.2
isInv : (f : X ⇒ Y) (g : Y ⇒ X) → Set
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
isoInvariant⟨_⟩ : {A : Set ℓ} (C : Commuter A ℓ′) (P : A → Set ℓ′′) → Set _
isoInvariant⟨_⟩ (π , comm) P = ∀ {a b} (j : π a ⇒ π b) → isIso j → comm a b j → P a → P b

isoUnique⟨_⟩ : {A : Set ℓ} (C : Commuter A ℓ′) (P : A → Set ℓ′′) → Set _
isoUnique⟨_⟩ (π , comm) P = ∀ {a b} → P a → P b → Σ (π a ⇒ π b) λ j → isIso j × comm a b j

isoInvariant : (P : CSet → Set) → Set
isoInvariant P = isoInvariant⟨ idᴹ , (λ _ _ _ → ⊤) ⟩ P

isoUnique : (P : CSet → Set) → Set
isoUnique P = isoUnique⟨ idᴹ , (λ _ _ _ → ⊤) ⟩ P
```

```agda
-- Lemma 2.3.3
isoInvariant-terminal : isoInvariant terminal
isoInvariant-terminal {a = T} {b = T′} j (j⁻¹ , jj⁻¹ , _) tt tml X =
  let (f , tt) , f! = tml X in
  (j ∘ f , tt) , λ {f′ g′} _ _ → begin
    f′                      ≡˘⟨ AssIdˡ jj⁻¹ ⟩
    j ∘ (j⁻¹ ∘ f′)          ≡⟨ cong (j ∘_) (f! tt tt) ⟩
    j ∘ (j⁻¹ ∘ g′)          ≡⟨ AssIdˡ jj⁻¹ ⟩
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
      (x ∘ !) ∘ y     ≡⟨ AssIdʳ p ⟩
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
