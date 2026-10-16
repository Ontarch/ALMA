------------------------------------------------------------------------
-- Absolute value on rational intervals
--
-- Defines the interval absolute value |x| and establishes its endpoint
-- expressions, the case analysis on endpoint signs, the two width
-- inequalities w(|X|) ≤ w(X) ≤ 2·w(|X|), and strictness l < u ⇒
-- absLo l u < absHi l u.
--
-- 有理区间上的绝对值
--
-- 定义区间绝对值 |x|，建立其端点表达式、按端点符号的分情形化简、
-- 宽度的两个不等式 w(|X|) ≤ w(X) ≤ 2·w(|X|)，以及严格性
-- l < u ⇒ absLo l u < absHi l u。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Abs where

open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _≤_; _<_)
open import Data.Rational.Base using (_÷_) renaming (-_ to neg)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational.Properties using
  (neg-antimono-≤; neg-antimono-<; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-total
  ; <-cmp; +-mono-≤; +-comm; +-identityʳ; +-inverseʳ; <-≤-trans; ≤-antisym)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import ALMA.Base.Real using (embed)
open import ALMA.Base.Real.Interval using (RealI; double-half)
open import ALMA.Base.Real.IntervalEquiv using (mono-half)
open import ALMA.Base.Real.Interval.Rational using
  (max; ≤maxˡ; ≤maxʳ; max-le; max-ge; max≤; max-mono; neg-sub; ¬<⇒≥; cong-plus; cong-minus)

------------------------------------------------------------------------
-- The two endpoints of |x|
--
-- Definitionally equal to the expressions appearing in the definition:
--   absLo l u = max (max l (- u)) 0        absHi l u = max u (- l)
--
-- |x| 的两个端点
--
-- 与定义中出现的表达式定义性相等：
--   absLo l u = max (max l (- u)) 0        absHi l u = max u (- l)

absLo : ℚ → ℚ → ℚ
absLo l u = max (max l (neg u)) 0ℚ

absHi : ℚ → ℚ → ℚ
absHi l u = max u (neg l)

------------------------------------------------------------------------
-- Case analysis on endpoint signs
--
-- 按端点符号分情形化简

lo-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → 0ℚ ≤ u → absLo l u ≡ l
lo-pos {l} {u} 0≤l 0≤u =
  begin
    absLo l u
  ≡⟨ max-ge {a = max l (neg u)} {b = 0ℚ}
            (≤-trans 0≤l (≤maxˡ l (neg u))) ⟩
    max l (neg u)
  ≡⟨ max-ge {a = l} {b = neg u}
            (≤-trans (neg-antimono-≤ 0≤u) 0≤l) ⟩
    l
  ∎

hi-pos : ∀ {l u : ℚ} → 0ℚ ≤ l → 0ℚ ≤ u → absHi l u ≡ u
hi-pos {l} {u} 0≤l 0≤u = begin
    absHi l u
  ≡⟨ max-ge {a = u} {b = neg l} (≤-trans (neg-antimono-≤ 0≤l) 0≤u) ⟩
    u
  ∎

lo-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ → absLo l u ≡ neg u
lo-neg {l} {u} l≤u u≤0 = begin
    absLo l u
  ≡⟨ max-ge {a = max l (neg u)} {b = 0ℚ}
            (≤-trans 0≤-u (≤maxʳ l (neg u))) ⟩
    max l (neg u)
  ≡⟨ max-le {a = l} {b = neg u} l≤-u ⟩
    neg u
  ∎
  where
    0≤-u : 0ℚ ≤ neg u
    0≤-u = neg-antimono-≤ u≤0

    l≤0 : l ≤ 0ℚ
    l≤0 = ≤-trans l≤u u≤0

    l≤-u : l ≤ neg u
    l≤-u = ≤-trans l≤0 0≤-u

hi-neg : ∀ {l u : ℚ} → l ≤ u → u ≤ 0ℚ → absHi l u ≡ neg l
hi-neg {l} {u} l≤u u≤0 = begin
    absHi l u
  ≡⟨ max-le {a = u} {b = neg l} (≤-trans u≤0 0≤-l) ⟩
    neg l
  ∎
  where
    l≤0 : l ≤ 0ℚ
    l≤0 = ≤-trans l≤u u≤0

    0≤-l : 0ℚ ≤ neg l
    0≤-l = neg-antimono-≤ l≤0

lo-mid : ∀ {l u : ℚ} → l ≤ 0ℚ → 0ℚ ≤ u → absLo l u ≡ 0ℚ
lo-mid {l} {u} l≤0 0≤u = begin
    absLo l u
  ≡⟨ max-le {a = max l (neg u)} {b = 0ℚ}
             (max≤ {a = l} {b = neg u} {c = 0ℚ} l≤0 (neg-antimono-≤ 0≤u)) ⟩
    0ℚ
  ∎

------------------------------------------------------------------------
-- The two width inequalities
--
--   w(|X|) ≤ w(X) ≤ 2 · w(|X|)
--
-- The former gives the first step of nest3; the latter says that a
-- two-level jump suffices (a one-level jump does not).
--
-- 宽度的两个不等式
--
--   w(|X|) ≤ w(X) ≤ 2 · w(|X|)
--
-- 前者给出 nest3 的第一步；后者说明两级跳跃足够（单级不够）。

abs-width≤ : ∀ {l u : ℚ} → l ≤ u → absHi l u - absLo l u ≤ u - l
abs-width≤ {l} {u} l≤u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      ≤-reflexive
        (begin
           absHi l u - absLo l u
         ≡⟨ cong-minus (hi-pos 0≤l 0≤u) (lo-pos 0≤l 0≤u) ⟩
           u - l
         ∎)
  where
    0≤u : 0ℚ ≤ u
    0≤u = ≤-trans 0≤l l≤u
... | inj₁ l≤0 | inj₁ u≤0 =
      ≤-reflexive
        (begin
           absHi l u - absLo l u
         ≡⟨ cong-minus (hi-neg l≤u u≤0) (lo-neg l≤u u≤0) ⟩
           neg l - neg u
         ≡⟨ neg-sub l u ⟩
           u - l
         ∎)
... | inj₁ l≤0 | inj₂ 0≤u =
      ≤-trans (≤-reflexive step)
              (max≤ {a = u} {b = neg l} {c = u - l} h1 h2)
  where
    0≤-l : 0ℚ ≤ neg l
    0≤-l = neg-antimono-≤ l≤0

    h1 : u ≤ u - l
    h1 = subst (λ z → z ≤ u + neg l) (+-identityʳ u)
               (+-mono-≤ (≤-refl {u}) 0≤-l)

    h2 : neg l ≤ u - l
    h2 = subst (λ z → neg l ≤ z) (+-comm (neg l) u)
               (subst (λ z → z ≤ neg l + u) (+-identityʳ (neg l))
                      (+-mono-≤ (≤-refl {neg l}) 0≤u))

    step : absHi l u - absLo l u ≡ max u (neg l)
    step = begin
        absHi l u - absLo l u
      ≡⟨ cong (λ z → absHi l u - z) (lo-mid l≤0 0≤u) ⟩
        absHi l u - 0ℚ
      ≡⟨ +-identityʳ (max u (neg l)) ⟩
        max u (neg l)
      ∎

abs-width≥ : ∀ {l u : ℚ} → l ≤ u →
  u - l ≤ (absHi l u - absLo l u) + (absHi l u - absLo l u)
abs-width≥ {l} {u} l≤u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      subst (λ z → u - l ≤ z + z) (sym A≡)
            (subst (λ z → z ≤ (u - l) + (u - l)) (+-identityʳ (u - l))
                   (+-mono-≤ (≤-refl {u - l}) 0≤w))
  where
    0≤u : 0ℚ ≤ u
    0≤u = ≤-trans 0≤l l≤u

    A≡ : absHi l u - absLo l u ≡ u - l
    A≡ = begin
        absHi l u - absLo l u
      ≡⟨ cong-minus (hi-pos 0≤l 0≤u) (lo-pos 0≤l 0≤u) ⟩
        u - l
      ∎

    0≤w : 0ℚ ≤ u - l
    0≤w = subst (λ z → z ≤ u + neg l) (+-inverseʳ l)
                (+-mono-≤ l≤u (≤-refl {neg l}))
... | inj₁ l≤0 | inj₁ u≤0 =
      subst (λ z → u - l ≤ z + z) (sym A≡)
            (subst (λ z → z ≤ (u - l) + (u - l)) (+-identityʳ (u - l))
                   (+-mono-≤ (≤-refl {u - l}) 0≤w))
  where
    A≡ : absHi l u - absLo l u ≡ u - l
    A≡ = begin
        absHi l u - absLo l u
      ≡⟨ cong-minus (hi-neg l≤u u≤0) (lo-neg l≤u u≤0) ⟩
        neg l - neg u
      ≡⟨ neg-sub l u ⟩
        u - l
      ∎

    0≤w : 0ℚ ≤ u - l
    0≤w = subst (λ z → z ≤ u + neg l) (+-inverseʳ l)
                (+-mono-≤ l≤u (≤-refl {neg l}))
... | inj₁ l≤0 | inj₂ 0≤u =
      subst (λ z → u - l ≤ z) (sym (cong-plus A≡ A≡))
            (+-mono-≤ (≤maxˡ u (neg l)) (≤maxʳ u (neg l)))
  where
    A≡ : absHi l u - absLo l u ≡ max u (neg l)
    A≡ = begin
        absHi l u - absLo l u
      ≡⟨ cong (λ z → absHi l u - z) (lo-mid l≤0 0≤u) ⟩
        absHi l u - 0ℚ
      ≡⟨ +-identityʳ (max u (neg l)) ⟩
        max u (neg l)
      ∎

------------------------------------------------------------------------
-- Strictness: l < u ⟹ absLo l u < absHi l u
--
-- 严格性：l < u ⟹ absLo l u < absHi l u

abs-lo< : ∀ {l u : ℚ} → l < u → absLo l u < absHi l u
abs-lo< {l} {u} l<u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      subst (λ z → z < absHi l u) (sym (lo-pos 0≤l 0≤u))
            (subst (λ z → l < z) (sym (hi-pos 0≤l 0≤u)) l<u)
  where
    0≤u : 0ℚ ≤ u
    0≤u = ≤-trans 0≤l (<⇒≤ l<u)
... | inj₁ l≤0 | inj₁ u≤0 =
      subst (λ z → z < absHi l u) (sym (lo-neg l≤u u≤0))
            (subst (λ z → neg u < z) (sym (hi-neg l≤u u≤0))
                   (neg-antimono-< l<u))
  where
    l≤u : l ≤ u
    l≤u = <⇒≤ l<u
... | inj₁ l≤0 | inj₂ 0≤u =
      subst (λ z → z < absHi l u) (sym (lo-mid l≤0 0≤u)) 0<absHi
  where
    0<absHi : 0ℚ < absHi l u
    0<absHi with <-cmp l 0ℚ
    ... | tri< l<0 _ _ =
          <-≤-trans (neg-antimono-< l<0) (≤maxʳ u (neg l))
    ... | tri≈ _ l≡0 _ =
          <-≤-trans (subst (λ z → z < u) l≡0 l<u) (≤maxˡ u (neg l))
    ... | tri> ¬l<0 _ _ =
          <-≤-trans (subst (λ z → z < u) l≡0 l<u) (≤maxˡ u (neg l))
      where
        l≡0 : l ≡ 0ℚ
        l≡0 = ≤-antisym l≤0 (¬<⇒≥ ¬l<0)

------------------------------------------------------------------------
-- Absolute value
--
-- 绝对值

∣_∣ℝ : RealI → RealI
RealI.l (∣ x ∣ℝ) =
  max (max (RealI.l x) (neg (RealI.u x))) 0ℚ
RealI.u (∣ x ∣ℝ) =
  max (RealI.u x) (neg (RealI.l x))
RealI.lo (∣ x ∣ℝ) = abs-lo< (RealI.lo x)
RealI.next (∣ x ∣ℝ) =
  ∣ RealI.next (RealI.next x) ∣ℝ
RealI.nest (∣ x ∣ℝ) = nest1 , nest2 , nest3
  where
    l u l₁ u₁ l₂ u₂ : ℚ
    l = RealI.l x
    u = RealI.u x
    l₁ = RealI.l (RealI.next x)
    u₁ = RealI.u (RealI.next x)
    l₂ = RealI.l (RealI.next (RealI.next x))
    u₂ = RealI.u (RealI.next (RealI.next x))

    l≤l₁ : l ≤ l₁
    l≤l₁ = proj₁ (RealI.nest x)

    u₁≤u : u₁ ≤ u
    u₁≤u = proj₁ (proj₂ (RealI.nest x))

    l₁≤l₂ : l₁ ≤ l₂
    l₁≤l₂ = proj₁ (RealI.nest (RealI.next x))

    u₂≤u₁ : u₂ ≤ u₁
    u₂≤u₁ = proj₁ (proj₂ (RealI.nest (RealI.next x)))

    l≤l₂ : l ≤ l₂
    l≤l₂ = ≤-trans l≤l₁ l₁≤l₂

    u₂≤u : u₂ ≤ u
    u₂≤u = ≤-trans u₂≤u₁ u₁≤u

    nest1 : max (max l (neg u)) 0ℚ ≤ max (max l₂ (neg u₂)) 0ℚ
    nest1 = max-mono (max-mono l≤l₂ (neg-antimono-≤ u₂≤u)) ≤-refl

    nest2 : max u₂ (neg l₂) ≤ max u (neg l)
    nest2 = max-mono u₂≤u (neg-antimono-≤ l≤l₂)

    nest3 : max u₂ (neg l₂) - max (max l₂ (neg u₂)) 0ℚ
          ≤ (max u (neg l) - max (max l (neg u)) 0ℚ) ÷ embed 2
    nest3 = ≤-trans step1 (≤-trans step2 step3)
      where
        A : ℚ
        A = max u (neg l) - max (max l (neg u)) 0ℚ

        l≤u : l ≤ u
        l≤u = <⇒≤ (RealI.lo x)

        l₂≤u₂ : l₂ ≤ u₂
        l₂≤u₂ = <⇒≤ (RealI.lo (RealI.next (RealI.next x)))

        step1 : max u₂ (neg l₂) - max (max l₂ (neg u₂)) 0ℚ ≤ u₂ - l₂
        step1 = abs-width≤ l₂≤u₂

        w₁≤ : u₁ - l₁ ≤ (u - l) ÷ embed 2
        w₁≤ = proj₂ (proj₂ (RealI.nest x))

        w₂≤ : u₂ - l₂ ≤ (u₁ - l₁) ÷ embed 2
        w₂≤ = proj₂ (proj₂ (RealI.nest (RealI.next x)))

        step2 : u₂ - l₂ ≤ ((u - l) ÷ embed 2) ÷ embed 2
        step2 = ≤-trans w₂≤ (mono-half w₁≤)

        step3 : ((u - l) ÷ embed 2) ÷ embed 2 ≤ A ÷ embed 2
        step3 = mono-half h3
          where
            h : u - l ≤ A + A
            h = abs-width≥ l≤u

            h2 : (u - l) ÷ embed 2 ≤ (A + A) ÷ embed 2
            h2 = mono-half h

            h3 : (u - l) ÷ embed 2 ≤ A
            h3 = ≤-trans h2 (≤-reflexive (double-half A))
