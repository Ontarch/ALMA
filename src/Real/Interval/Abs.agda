------------------------------------------------------------------------
-- Absolute value on rational intervals
--
-- 有理区间上的绝对值
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Abs where

open import Data.Rational using (ℚ; 0ℚ; _⊔_; _+_; _-_; _≤_; _<_; _÷_)
  renaming (-_ to neg)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational.Properties using
  (neg-antimono-≤; neg-antimono-<; ≤-refl; ≤-trans; <⇒≤; ≤-total; <-cmp
  ; +-mono-≤; +-comm; +-identityʳ; +-inverseʳ; ≤-antisym; ≮⇒≥; p≤p⊔q; p≤q⊔p
  ; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p; ⊔-lub; ⊔-mono-≤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Real using (embed)
open import Real.Interval using (RealI; double-half)
open import Real.IntervalEquiv using (mono-half)
open import Real.Interval.Rational using (neg-sub)
open import Real.Interval.Reasoning using
  (begin≤_; begin<_; _≤∎; _≈⟨_⟩_; _≤⟨_⟩_; _<⟨_⟩≤[_])

------------------------------------------------------------------------
-- The two endpoints of |x|
--
-- Definitionally equal to the expressions appearing in the definition:
--   absLo l u = (l ⊔ - u) ⊔ 0          absHi l u = u ⊔ - l
--
-- |x| 的两个端点
--
-- 与定义中出现的表达式定义性相等：
--   absLo l u = (l ⊔ - u) ⊔ 0          absHi l u = u ⊔ - l

absLo : ℚ → ℚ → ℚ
absLo l u = (l ⊔ neg u) ⊔ 0ℚ

absHi : ℚ → ℚ → ℚ
absHi l u = u ⊔ neg l

------------------------------------------------------------------------
-- Case analysis on endpoint signs
--
-- 按端点符号分情形化简

lo-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → 0ℚ ≤ u → absLo l u ≡ l
lo-pos {l} {u} 0≤l 0≤u =
  begin
    absLo l u
  ≡⟨ p≥q⇒p⊔q≡p {p = l ⊔ neg u} {q = 0ℚ}
            (≤-trans 0≤l (p≤p⊔q l (neg u))) ⟩
    l ⊔ neg u
  ≡⟨ p≥q⇒p⊔q≡p {p = l} {q = neg u}
            (≤-trans (neg-antimono-≤ 0≤u) 0≤l) ⟩
    l
  ∎

hi-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → 0ℚ ≤ u → absHi l u ≡ u
hi-pos {l} {u} 0≤l 0≤u =
  begin
    absHi l u
  ≡⟨ p≥q⇒p⊔q≡p {p = u} {q = neg l}
            (≤-trans (neg-antimono-≤ 0≤l) 0≤u) ⟩
    u
  ∎

lo-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ → absLo l u ≡ neg u
lo-neg {l} {u} l≤u u≤0 =
  begin
    absLo l u
  ≡⟨ p≥q⇒p⊔q≡p {p = l ⊔ neg u} {q = 0ℚ}
            (≤-trans (neg-antimono-≤ u≤0) (p≤q⊔p l (neg u))) ⟩
    l ⊔ neg u
  ≡⟨ p≤q⇒p⊔q≡q {p = l} {q = neg u}
             (≤-trans (≤-trans l≤u u≤0) (neg-antimono-≤ u≤0)) ⟩
    neg u
  ∎

hi-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ → absHi l u ≡ neg l
hi-neg {l} {u} l≤u u≤0 =
  begin
    absHi l u
  ≡⟨ p≤q⇒p⊔q≡q {p = u} {q = neg l}
             (≤-trans u≤0 (neg-antimono-≤ (≤-trans l≤u u≤0))) ⟩
    neg l
  ∎

lo-mid : ∀ {l u : ℚ} → l ≤ 0ℚ → 0ℚ ≤ u → absLo l u ≡ 0ℚ
lo-mid {l} {u} l≤0 0≤u =
  begin
    absLo l u
  ≡⟨ p≤q⇒p⊔q≡q {p = l ⊔ neg u} {q = 0ℚ}
             (⊔-lub l≤0 (neg-antimono-≤ 0≤u)) ⟩
    0ℚ
  ∎

------------------------------------------------------------------------
-- Shared: absolute width as a difference
--
-- 共享：绝对值宽度之差

abs-width-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → 0ℚ ≤ u →
  absHi l u - absLo l u ≡ u - l
abs-width-pos {l} {u} 0≤l 0≤u =
  begin
    absHi l u - absLo l u
  ≡⟨ cong₂ _-_ (hi-pos 0≤l 0≤u) (lo-pos 0≤l 0≤u) ⟩
    u - l
  ∎

abs-width-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ →
  absHi l u - absLo l u ≡ u - l
abs-width-neg {l} {u} l≤u u≤0 =
  begin
    absHi l u - absLo l u
  ≡⟨ cong₂ _-_ (hi-neg l≤u u≤0) (lo-neg l≤u u≤0) ⟩
    neg l - neg u
  ≡⟨ neg-sub l u ⟩
    u - l
  ∎

abs-width-mid : ∀ {l u : ℚ} → l ≤ 0ℚ → 0ℚ ≤ u →
  absHi l u - absLo l u ≡ u ⊔ neg l
abs-width-mid {l} {u} l≤0 0≤u =
  begin
    absHi l u - absLo l u
  ≡⟨ cong (λ z → absHi l u - z) (lo-mid l≤0 0≤u) ⟩
    absHi l u - 0ℚ
  ≡⟨ +-identityʳ (absHi l u) ⟩
    u ⊔ neg l
  ∎

------------------------------------------------------------------------
-- Helpers for abs-width≤
--
-- abs-width≤ 的辅助引理

abs-width≤-mid-h1 : ∀ {l u : ℚ} → l ≤ 0ℚ → u ≤ u - l
abs-width≤-mid-h1 {l} {u} l≤0 =
  begin≤
    u
      ≈⟨ sym (+-identityʳ u) ⟩
    u + 0ℚ
      ≤⟨ +-mono-≤ (≤-refl {u}) (neg-antimono-≤ l≤0) ⟩
    u + neg l
  ≤∎

abs-width≤-mid-h2 : ∀ {l u : ℚ} → 0ℚ ≤ u → neg l ≤ u - l
abs-width≤-mid-h2 {l} {u} 0≤u =
  begin≤
    neg l
      ≈⟨ sym (+-identityʳ (neg l)) ⟩
    neg l + 0ℚ
      ≤⟨ +-mono-≤ (≤-refl {neg l}) 0≤u ⟩
    neg l + u
      ≈⟨ +-comm (neg l) u ⟩
    u + neg l
  ≤∎

------------------------------------------------------------------------
-- Helpers for abs-width≥
--
-- abs-width≥ 的辅助引理

abs-width≥-0≤diff : ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
abs-width≥-0≤diff {a} {b} a≤b =
  begin≤
    0ℚ
      ≈⟨ sym (+-inverseʳ a) ⟩
    a + neg a
      ≤⟨ +-mono-≤ a≤b (≤-refl {neg a}) ⟩
    b + neg a
  ≤∎

double-≤ : ∀ {x : ℚ} → 0ℚ ≤ x → x ≤ x + x
double-≤ {x} 0≤x =
  begin≤
    x
      ≈⟨ sym (+-identityʳ x) ⟩
    x + 0ℚ
      ≤⟨ +-mono-≤ (≤-refl {x}) 0≤x ⟩
    x + x
  ≤∎

abs-width≥-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → l ≤ u →
  0ℚ ≤ absHi l u - absLo l u
abs-width≥-pos {l} {u} 0≤l l≤u =
  begin≤
    0ℚ
      ≤⟨ abs-width≥-0≤diff l≤u ⟩
    u - l
      ≈⟨ sym (abs-width-pos 0≤l (≤-trans 0≤l l≤u)) ⟩
    absHi l u - absLo l u
  ≤∎

abs-width≥-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ →
  0ℚ ≤ absHi l u - absLo l u
abs-width≥-neg {l} {u} l≤u u≤0 =
  begin≤
    0ℚ
      ≤⟨ abs-width≥-0≤diff l≤u ⟩
    u - l
      ≈⟨ sym (abs-width-neg l≤u u≤0) ⟩
    absHi l u - absLo l u
  ≤∎

------------------------------------------------------------------------
-- The two width inequalities
--
--   w(|X|) ≤ w(X) ≤ 2 · w(|X|)
--
-- 宽度的两个不等式

abs-width≤ : ∀ {l u : ℚ} → l ≤ u → absHi l u - absLo l u ≤ u - l
abs-width≤ {l} {u} l≤u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      begin≤
        absHi l u - absLo l u
          ≈⟨ abs-width-pos 0≤l (≤-trans 0≤l l≤u) ⟩
        u - l
      ≤∎
... | inj₁ l≤0 | inj₁ u≤0 =
      begin≤
        absHi l u - absLo l u
          ≈⟨ abs-width-neg l≤u u≤0 ⟩
        u - l
      ≤∎
... | inj₁ l≤0 | inj₂ 0≤u =
      begin≤
        absHi l u - absLo l u
          ≈⟨ abs-width-mid l≤0 0≤u ⟩
        u ⊔ neg l
          ≤⟨ ⊔-lub (abs-width≤-mid-h1 {l = l} {u = u} l≤0)
                   (abs-width≤-mid-h2 {l = l} {u = u} 0≤u) ⟩
        u - l
      ≤∎

abs-width≥ : ∀ {l u : ℚ} → l ≤ u →
  u - l ≤ (absHi l u - absLo l u) + (absHi l u - absLo l u)
abs-width≥ {l} {u} l≤u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      begin≤
        u - l
          ≈⟨ sym (abs-width-pos 0≤l (≤-trans 0≤l l≤u)) ⟩
        absHi l u - absLo l u
          ≤⟨ double-≤ (abs-width≥-pos 0≤l l≤u) ⟩
        (absHi l u - absLo l u) + (absHi l u - absLo l u)
      ≤∎
... | inj₁ l≤0 | inj₁ u≤0 =
      begin≤
        u - l
          ≈⟨ sym (abs-width-neg l≤u u≤0) ⟩
        absHi l u - absLo l u
          ≤⟨ double-≤ (abs-width≥-neg l≤u u≤0) ⟩
        (absHi l u - absLo l u) + (absHi l u - absLo l u)
      ≤∎
... | inj₁ l≤0 | inj₂ 0≤u =
      begin≤
        u - l
          ≤⟨ +-mono-≤ (p≤p⊔q u (neg l)) (p≤q⊔p u (neg l)) ⟩
        (u ⊔ neg l) + (u ⊔ neg l)
          ≈⟨ sym (cong₂ _+_ (abs-width-mid l≤0 0≤u)
                            (abs-width-mid l≤0 0≤u)) ⟩
        (absHi l u - absLo l u) + (absHi l u - absLo l u)
      ≤∎

------------------------------------------------------------------------
-- Strictness: l < u ⟹ absLo l u < absHi l u
--
-- 严格性：l < u ⟹ absLo l u < absHi l u

abs-lo<-mid-pos : ∀ {l u : ℚ} → l ≤ 0ℚ → l < u → 0ℚ < u ⊔ neg l
abs-lo<-mid-pos {l} {u} l≤0 l<u with <-cmp l 0ℚ
... | tri< l<0 _ _ =
      begin<
        0ℚ
          <⟨ neg-antimono-< l<0 ⟩≤[ p≤q⊔p u (neg l) ]
... | tri≈ _ l≡0 _ =
      begin<
        0ℚ
          <⟨ subst (λ z → z < u) l≡0 l<u ⟩≤[ p≤p⊔q u (neg l) ]
... | tri> ¬l<0 _ _ =
      begin<
        0ℚ
          <⟨ subst (λ z → z < u)
                   (≤-antisym l≤0 (≮⇒≥ ¬l<0)) l<u ⟩≤[ p≤p⊔q u (neg l) ]

abs-lo< : ∀ {l u : ℚ} → l < u → absLo l u < absHi l u
abs-lo< {l} {u} l<u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      subst (λ z → z < absHi l u)
            (sym (lo-pos 0≤l (≤-trans 0≤l (<⇒≤ l<u))))
            (subst (λ z → l < z)
                   (sym (hi-pos 0≤l (≤-trans 0≤l (<⇒≤ l<u))))
                   l<u)
... | inj₁ l≤0 | inj₁ u≤0 =
      subst (λ z → z < absHi l u) (sym (lo-neg (<⇒≤ l<u) u≤0))
            (subst (λ z → neg u < z) (sym (hi-neg (<⇒≤ l<u) u≤0))
                   (neg-antimono-< l<u))
... | inj₁ l≤0 | inj₂ 0≤u =
      subst (λ z → z < absHi l u) (sym (lo-mid l≤0 0≤u))
            (abs-lo<-mid-pos l≤0 l<u)

------------------------------------------------------------------------
-- Nest helpers
--
-- nest 的辅助引理

abs-nest1 : ∀ {l u l₂ u₂ : ℚ} → l ≤ l₂ → u₂ ≤ u →
  (l ⊔ neg u) ⊔ 0ℚ ≤ (l₂ ⊔ neg u₂) ⊔ 0ℚ
abs-nest1 l≤l₂ u₂≤u =
  ⊔-mono-≤ (⊔-mono-≤ l≤l₂ (neg-antimono-≤ u₂≤u)) ≤-refl

abs-nest2 : ∀ {l u l₂ u₂ : ℚ} → l ≤ l₂ → u₂ ≤ u →
  u₂ ⊔ neg l₂ ≤ u ⊔ neg l
abs-nest2 l≤l₂ u₂≤u =
  ⊔-mono-≤ u₂≤u (neg-antimono-≤ l≤l₂)

abs-nest3-step2 : ∀ (u l u₁ l₁ u₂ l₂ : ℚ)
                → u₁ - l₁ ≤ (u - l) ÷ embed 2
                → u₂ - l₂ ≤ (u₁ - l₁) ÷ embed 2
                → u₂ - l₂ ≤ ((u - l) ÷ embed 2) ÷ embed 2
abs-nest3-step2 u l u₁ l₁ u₂ l₂ w₁≤ w₂≤ =
  begin≤
    u₂ - l₂
      ≤⟨ w₂≤ ⟩
    (u₁ - l₁) ÷ embed 2
      ≤⟨ mono-half w₁≤ ⟩
    ((u - l) ÷ embed 2) ÷ embed 2
  ≤∎

abs-nest3-step3 : ∀ (l u : ℚ) → l ≤ u →
  ((u - l) ÷ embed 2) ÷ embed 2
    ≤ ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ)) ÷ embed 2
abs-nest3-step3 l u l≤u =
  begin≤
    ((u - l) ÷ embed 2) ÷ embed 2
      ≤⟨ mono-half (mono-half (abs-width≥ l≤u)) ⟩
    ((((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ))
      + ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ))) ÷ embed 2) ÷ embed 2
      ≈⟨ cong (_÷ embed 2)
              (double-half ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ))) ⟩
    ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ)) ÷ embed 2
  ≤∎

abs-nest3 : ∀ (l u l₁ u₁ l₂ u₂ : ℚ)
          → l ≤ u → l₂ ≤ u₂
          → u₁ - l₁ ≤ (u - l) ÷ embed 2
          → u₂ - l₂ ≤ (u₁ - l₁) ÷ embed 2
          → (u₂ ⊔ neg l₂) - ((l₂ ⊔ neg u₂) ⊔ 0ℚ)
            ≤ ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ)) ÷ embed 2
abs-nest3 l u l₁ u₁ l₂ u₂ l≤u l₂≤u₂ w₁≤ w₂≤ =
  begin≤
    (u₂ ⊔ neg l₂) - ((l₂ ⊔ neg u₂) ⊔ 0ℚ)
      ≤⟨ abs-width≤ l₂≤u₂ ⟩
    u₂ - l₂
      ≤⟨ abs-nest3-step2 u l u₁ l₁ u₂ l₂ w₁≤ w₂≤ ⟩
    ((u - l) ÷ embed 2) ÷ embed 2
      ≤⟨ abs-nest3-step3 l u l≤u ⟩
    ((u ⊔ neg l) - ((l ⊔ neg u) ⊔ 0ℚ)) ÷ embed 2
  ≤∎

------------------------------------------------------------------------
-- Node-level nest witnesses for |x|
--
-- The three fields of Nest for |x| at x, extracted from the two-level
-- nesting of x itself.
--
-- |x| 的节点层 nest 见证
--
-- |x| 的 Nest 三字段，从 x 自身两级嵌套中提取。

abs-nest1-of : (x : RealI) →
  (RealI.l x ⊔ neg (RealI.u x)) ⊔ 0ℚ ≤
  (RealI.l (RealI.next (RealI.next x)) ⊔
   neg (RealI.u (RealI.next (RealI.next x)))) ⊔ 0ℚ
abs-nest1-of x = abs-nest1
  (≤-trans (proj₁ (RealI.nest x))
           (proj₁ (RealI.nest (RealI.next x))))
  (≤-trans (proj₁ (proj₂ (RealI.nest (RealI.next x))))
           (proj₁ (proj₂ (RealI.nest x))))

abs-nest2-of : (x : RealI) →
  RealI.u (RealI.next (RealI.next x)) ⊔
      neg (RealI.l (RealI.next (RealI.next x)))
  ≤ RealI.u x ⊔ neg (RealI.l x)
abs-nest2-of x = abs-nest2
  (≤-trans (proj₁ (RealI.nest x))
           (proj₁ (RealI.nest (RealI.next x))))
  (≤-trans (proj₁ (proj₂ (RealI.nest (RealI.next x))))
           (proj₁ (proj₂ (RealI.nest x))))

abs-nest3-of : (x : RealI) →
  (RealI.u (RealI.next (RealI.next x)) ⊔
   neg (RealI.l (RealI.next (RealI.next x))))
  - ((RealI.l (RealI.next (RealI.next x)) ⊔
      neg (RealI.u (RealI.next (RealI.next x)))) ⊔ 0ℚ)
  ≤ ((RealI.u x ⊔ neg (RealI.l x))
       - ((RealI.l x ⊔ neg (RealI.u x)) ⊔ 0ℚ)) ÷ embed 2
abs-nest3-of x = abs-nest3
  (RealI.l x) (RealI.u x)
  (RealI.l (RealI.next x)) (RealI.u (RealI.next x))
  (RealI.l (RealI.next (RealI.next x)))
  (RealI.u (RealI.next (RealI.next x)))
  (<⇒≤ (RealI.lo x))
  (<⇒≤ (RealI.lo (RealI.next (RealI.next x))))
  (proj₂ (proj₂ (RealI.nest x)))
  (proj₂ (proj₂ (RealI.nest (RealI.next x))))

------------------------------------------------------------------------
-- Absolute value
--
-- 绝对值

∣_∣ℝ : RealI → RealI
RealI.l (∣ x ∣ℝ) =
  (RealI.l x ⊔ neg (RealI.u x)) ⊔ 0ℚ
RealI.u (∣ x ∣ℝ) =
  RealI.u x ⊔ neg (RealI.l x)
RealI.lo (∣ x ∣ℝ) = abs-lo< (RealI.lo x)
RealI.next (∣ x ∣ℝ) =
  ∣ RealI.next (RealI.next x) ∣ℝ
RealI.nest (∣ x ∣ℝ) = abs-nest1-of x , abs-nest2-of x , abs-nest3-of x
