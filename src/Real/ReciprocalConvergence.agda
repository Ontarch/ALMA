------------------------------------------------------------------------
-- Reciprocal law for arbitrary-tolerance convergence
--
-- A sequence converging to a limit bounded away from zero has a
-- reciprocal sequence converging to the reciprocal of the limit.
--
-- 任意容差收敛的倒数极限律
--
-- 收敛到远离零之极限的序列，其倒数序列收敛到极限的倒数。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.ReciprocalConvergence where

open import Data.Nat using (_⊔_; ≢-nonZero⁻¹)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
  renaming (≤-trans to ≤-trans-ℕ)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _<_; _≤_; ∣_∣; ↥_; NonZero)
open import Data.Rational.Base using
  (1/_; Positive; positive; nonNegative; ≢-nonZero; toℚᵘ)
open import Data.Rational.Unnormalised.Base using () renaming (↥_ to ↥ᵘ_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; <⇒≤; <-irrefl; +-mono-<-≤
  ; +-monoʳ-<; +-comm; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-inverseʳ
  ; *-monoˡ-<-pos; *-monoʳ-<-pos; *-monoˡ-≤-nonNeg; pos*pos⇒pos; positive⁻¹
  ; 1/pos⇒pos; pos⇒nonZero; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; ∣p+q∣≤∣p∣+∣q∣
  ; ∣p∣≡0⇒p≡0; ∣p∣≡p∨∣p∣≡-p; 0≤p⇒∣p∣≡p; ∣-p∣≡∣p∣; nonNeg∧nonZero⇒pos
  ; p*q≡0⇒p≡0∨q≡0; p≡0⇒↥p≡0; ↥ᵘ-toℚᵘ; neg-injective)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (0ℤ) renaming (∣_∣ to absℤ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-neg-mul; *ʳ-sub)
open import Real using (half)
open import Real.Convergence using (Converges)
open import Real.Interval.Kit using (two-half; strict-recip; 0<half; abs-swap)
open import Real.Interval.Mul using (cancel-z; cancelʳ)
open import Real.Interval.Rational using (recip-*-hom)

------------------------------------------------------------------------
-- Uniqueness of a reciprocal
--
-- Two reciprocals of the same nonzero element are equal, using only
-- ring identities and no decision procedure.
--
-- 倒数的唯一性
--
-- 同一非零元素的两个倒数相等，仅用环恒等式，无需任何判定过程。

unique-recip : ∀ a z w → a * z ≡ 1ℚ → a * w ≡ 1ℚ → z ≡ w
unique-recip a z w az aw = begin
  z
    ≡⟨ sym (*-identityʳ z) ⟩
  z * 1ℚ
    ≡⟨ cong (z *_) (sym aw) ⟩
  z * (a * w)
    ≡⟨ sym (*-assoc z a w) ⟩
  (z * a) * w
    ≡⟨ cong (_* w) (*-comm z a) ⟩
  (a * z) * w
    ≡⟨ cong (_* w) az ⟩
  1ℚ * w
    ≡⟨ *-identityˡ w ⟩
  w ∎

------------------------------------------------------------------------
-- Negation of a nonzero; reciprocal of a negation
--
-- 非零元素取负；取负的倒数

-- A NonZero witness wraps the numerator's inequivalence to zero; apply it
-- to the contradiction obtained from a rational equality with zero.
--
-- NonZero 见证封装了分子非零的反证，将其作用于有理等于零的矛盾。
contradict-nonzero : ∀ {p} → NonZero p → p ≡ 0ℚ → ⊥
contradict-nonzero {p} nz p≡0 =
  let n = absℤ (↥ᵘ_ (toℚᵘ p))
      num0 : n ≡ 0
      num0 = begin
        absℤ (↥ᵘ_ (toℚᵘ p))
          ≡⟨ cong (λ z → absℤ z) (↥ᵘ-toℚᵘ p) ⟩
        absℤ (↥_ p)
          ≡⟨ cong (λ z → absℤ z) (p≡0⇒↥p≡0 p p≡0) ⟩
        absℤ 0ℤ
          ≡⟨ refl ⟩
        0 ∎
  in ≢-nonZero⁻¹ n ⦃ nz ⦄ num0

neg-0 : - 0ℚ ≡ 0ℚ
neg-0 = refl

neg-nonzero : ∀ {y} → NonZero y → NonZero (- y)
neg-nonzero {y} ny = ≢-nonZero λ eq →
  contradict-nonzero ny (neg-injective {p = y} {q = 0ℚ} (trans eq (sym neg-0)))

1/-neg : ∀ y → {{ny : NonZero y}} →
  1/_ (- y) ⦃ neg-nonzero {y = y} ny ⦄ ≡ - (1/_ y)
1/-neg y {{ny}} = unique-recip (- y) z w eq1 eq2
  where
  nz-neg : NonZero (- y)
  nz-neg = neg-nonzero {y = y} ny

  iy : ℚ
  iy = 1/_ y ⦃ ny ⦄

  z : ℚ
  z = 1/_ (- y) ⦃ nz-neg ⦄

  w : ℚ
  w = - iy

  eq1 : (- y) * z ≡ 1ℚ
  eq1 = *-inverseʳ (- y) ⦃ nz-neg ⦄

  eq2 : (- y) * w ≡ 1ℚ
  eq2 = trans (neg-neg-mul y iy) (*-inverseʳ y ⦃ ny ⦄)

------------------------------------------------------------------------
-- Absolute value of a reciprocal
--
-- 倒数的绝对值

recip-≡ : ∀ {a b} (eq : a ≡ b) →
  {{na : NonZero a}} → {{nb : NonZero b}} →
  1/_ a ⦃ na ⦄ ≡ 1/_ b ⦃ nb ⦄
recip-≡ refl = refl

abs-recip : ∀ x → {{nx : NonZero x}} →
  ∣ 1/_ x ⦃ nx ⦄ ∣ ≡ 1/_ ∣ x ∣ ⦃ ≢-nonZero λ eq →
    contradict-nonzero nx (∣p∣≡0⇒p≡0 x eq) ⦄
abs-recip x {{nx}} =
  let rx = 1/_ x ⦃ nx ⦄
      ra-nz = ≢-nonZero λ eq →
        contradict-nonzero nx (∣p∣≡0⇒p≡0 x eq)
      ra = 1/_ ∣ x ∣ ⦃ ra-nz ⦄
  in case ∣p∣≡p∨∣p∣≡-p x of λ where
  (inj₁ ∣x∣≡x) →
    let 0≤x : 0ℚ ≤ x
        0≤x = subst (λ z → 0ℚ ≤ z) ∣x∣≡x (0≤∣p∣ x)
        x-pos : Positive x
        x-pos = nonNeg∧nonZero⇒pos x ⦃ nonNegative 0≤x ⦄ ⦃ nx ⦄
        rx-pos : Positive rx
        rx-pos = 1/pos⇒pos x ⦃ x-pos ⦄
    in begin
      ∣ rx ∣
        ≡⟨ 0≤p⇒∣p∣≡p (<⇒≤ (positive⁻¹ rx ⦃ rx-pos ⦄)) ⟩
      rx
        ≡⟨ recip-≡ (sym ∣x∣≡x) ⦃ nx ⦄ ⦃ ra-nz ⦄ ⟩
      ra ∎
  (inj₂ ∣x∣≡-x) →
    let 0≤-x : 0ℚ ≤ - x
        0≤-x = subst (λ z → 0ℚ ≤ z) ∣x∣≡-x (0≤∣p∣ x)
        
        -x-pos : Positive (- x)
        -x-pos = nonNeg∧nonZero⇒pos (- x) 
                   ⦃ nonNegative 0≤-x ⦄ 
                   ⦃ neg-nonzero {y = x} nx ⦄
                   
        -rx-pos : Positive (- rx)
        -rx-pos = subst Positive (1/-neg x ⦃ nx ⦄)
                    (1/pos⇒pos (- x) ⦃ -x-pos ⦄)
                    
        rx-nn : 0ℚ ≤ - rx
        rx-nn = <⇒≤ (positive⁻¹ (- rx) ⦃ -rx-pos ⦄)
    in begin
      ∣ rx ∣
        ≡⟨ sym (∣-p∣≡∣p∣ rx) ⟩
      ∣ - rx ∣
        ≡⟨ 0≤p⇒∣p∣≡p rx-nn ⟩
      - rx
        ≡⟨ sym (1/-neg x ⦃ nx ⦄) ⟩
      1/_ (- x) ⦃ neg-nonzero {y = x} nx ⦄
        ≡⟨ recip-≡ {a = - x} {b = ∣ x ∣} (sym ∣x∣≡-x) 
             ⦃ neg-nonzero {y = x} nx ⦄ ⦃ ra-nz ⦄ ⟩
      ra ∎

------------------------------------------------------------------------
-- Difference of two reciprocals
--
-- 两个倒数之差

prod-nonzero : ∀ x y → NonZero x → NonZero y → NonZero (x * y)
prod-nonzero x y nx ny = ≢-nonZero λ eq →
  case p*q≡0⇒p≡0∨q≡0 {p = x} {q = y} eq of λ
  { (inj₁ x≡0) → contradict-nonzero {p = x} nx x≡0
  ; (inj₂ y≡0) → contradict-nonzero {p = y} ny y≡0
  }

recip-diff : ∀ x y → {{nx : NonZero x}} → {{ny : NonZero y}} →
  1/_ x ⦃ nx ⦄ - 1/_ y ⦃ ny ⦄
    ≡ (y - x) * 1/_ (x * y) ⦃ prod-nonzero x y nx ny ⦄
recip-diff x y {{nx}} {{ny}} =
  begin
    ix - iy
      ≡⟨ sym step ⟩
    (y - x) * (ix * iy)
      ≡⟨ cong ((y - x) *_)
             (sym (recip-*-hom x y ⦃ nx ⦄ ⦃ ny ⦄
                    ⦃ prod-nonzero x y nx ny ⦄)) ⟩
    (y - x) * ixy ∎
  where
  ix = 1/_ x ⦃ nx ⦄
  iy = 1/_ y ⦃ ny ⦄
  ixy = 1/_ (x * y) ⦃ prod-nonzero x y nx ny ⦄

  t1 : y * ix * iy ≡ ix
  t1 = begin
    y * ix * iy
      ≡⟨ *-assoc y ix iy ⟩
    y * (ix * iy)
      ≡⟨ cong (y *_) (*-comm ix iy) ⟩
    y * (iy * ix)
      ≡⟨ sym (*-assoc y iy ix) ⟩
    (y * iy) * ix
      ≡⟨ cong (_* ix) (*-inverseʳ y ⦃ ny ⦄) ⟩
    1ℚ * ix
      ≡⟨ *-identityˡ ix ⟩
    ix ∎

  t2 : x * ix * iy ≡ iy
  t2 = begin
    (x * ix) * iy
      ≡⟨ cong (_* iy) (*-inverseʳ x ⦃ nx ⦄) ⟩
    1ℚ * iy
      ≡⟨ *-identityˡ iy ⟩
    iy ∎

  step : (y - x) * (ix * iy) ≡ ix - iy
  step = begin
    (y - x) * (ix * iy)
      ≡⟨ *ʳ-sub y x (ix * iy) ⟩
    y * (ix * iy) - x * (ix * iy)
      ≡⟨ cong₂ _-_ (sym (*-assoc y ix iy)) (sym (*-assoc x ix iy)) ⟩
    y * ix * iy - x * ix * iy
      ≡⟨ cong₂ _-_ t1 t2 ⟩
    ix - iy ∎

------------------------------------------------------------------------
-- Reciprocal convergence law
--
-- The limit is nonzero because the bound b is positive and lies below
-- ∣ l ∣. Past a first modulus the reverse triangle inequality places
-- every ∣ g n ∣ above b * half; the reciprocal difference is then the
-- numerator error divided by a denominator bounded below, so a second
-- modulus shrinking the numerator closes the target tolerance.
--
-- 倒数极限律
--
-- 正界 b 位于 ∣ l ∣ 之下，故极限非零。越过第一个模数后，反三角不等式
-- 使每项 ∣ g n ∣ 高于 b * half；倒数之差即分子误差除以有下界的分母，
-- 因而用第二个模数收紧分子即可闭合目标容差。

-- The limit is nonzero because the positive bound b lies below ∣ l ∣.
--
-- 正界 b 位于 ∣ l ∣ 之下，故极限非零。
limit-nonzero : ∀ {l} (0<∣l∣ : 0ℚ < ∣ l ∣) → NonZero l
limit-nonzero {l} 0<∣l∣ = ≢-nonZero λ eq →
  let abs0 : ∣ l ∣ ≡ 0ℚ
      abs0 = trans (cong ∣_∣ eq) (0≤p⇒∣p∣≡p ≤-refl)
  in <-irrefl (sym abs0) 0<∣l∣

recip-converges :
  ∀ {g l} (b : ℚ) (0<b : 0ℚ < b) (b≤l : b ≤ ∣ l ∣)
  (nz : ∀ n → NonZero (g n))
  (cg : Converges g l)
  → Converges (λ n → 1/_ (g n) ⦃ nz n ⦄)
              (1/_ l ⦃ limit-nonzero (<-≤-trans 0<b b≤l) ⦄)
recip-converges {g} {l} b 0<b b≤l nz cg e 0<e =
  let 0<∣l∣ : 0ℚ < ∣ l ∣
      0<∣l∣ = <-≤-trans 0<b b≤l

      l-nz : NonZero l
      l-nz = limit-nonzero 0<∣l∣

      hb = b * half
      hb-pos : Positive hb
      hb-pos = pos*pos⇒pos b ⦃ positive 0<b ⦄ half ⦃ positive 0<half ⦄
      0<hb : 0ℚ < hb
      0<hb = positive⁻¹ hb ⦃ hb-pos ⦄
      hb2 : hb + hb ≡ b
      hb2 = two-half b

      D = hb * b
      D-pos : Positive D
      D-pos = pos*pos⇒pos hb ⦃ hb-pos ⦄ b ⦃ positive 0<b ⦄
      0<D : 0ℚ < D
      0<D = positive⁻¹ D ⦃ D-pos ⦄
      D-nz : NonZero D
      D-nz = pos⇒nonZero D ⦃ D-pos ⦄

      t = e * D
      t-pos : Positive t
      t-pos = pos*pos⇒pos e ⦃ positive 0<e ⦄ D ⦃ D-pos ⦄
      0<t : 0ℚ < t
      0<t = positive⁻¹ t ⦃ t-pos ⦄

      N1 , p1 = cg hb 0<hb
      N2 , p2 = cg t 0<t
      N = N1 ⊔ N2
  in N , λ n n≥N →
    let d1 : ∣ g n - l ∣ < hb
        d1 = p1 n (≤-trans-ℕ (m≤m⊔n N1 N2) n≥N)
        d2 : ∣ g n - l ∣ < t
        d2 = p2 n (≤-trans-ℕ (m≤n⊔m N1 N2) n≥N)

        gn = ∣ g n ∣
        lm = ∣ l ∣

        ig : ℚ
        ig = 1/_ (g n) ⦃ nz n ⦄
        il : ℚ
        il = 1/_ l ⦃ l-nz ⦄

        -- Triangle: ∣l∣ ≤ ∣g n∣ + ∣g n - l∣
        --
        -- 三角不等式给出极限绝对值的上界。
        idl : g n + (l - g n) ≡ l
        idl = trans (sym (+-comm (l - g n) (g n))) (cancelʳ l (g n))
        tri : ∣ l ∣ ≤ ∣ g n ∣ + ∣ l - g n ∣
        tri = subst (λ z → ∣ z ∣ ≤ ∣ g n ∣ + ∣ l - g n ∣) idl
                (∣p+q∣≤∣p∣+∣q∣ (g n) (l - g n))
        sw : ∣ l - g n ∣ ≡ ∣ g n - l ∣
        sw = abs-swap l (g n)
        tri' : ∣ l ∣ ≤ ∣ g n ∣ + ∣ g n - l ∣
        tri' = subst (λ z → ∣ l ∣ ≤ ∣ g n ∣ + z) sw tri

        up : gn + ∣ g n - l ∣ < gn + hb
        up = +-monoʳ-< gn d1
        b< : b < gn + hb
        b< = ≤-<-trans (≤-trans b≤l tri') up

        shifted : b - hb < (gn + hb) - hb
        shifted = +-mono-<-≤ b< (≤-refl { - hb })
        lhs≡ : b - hb ≡ hb
        lhs≡ = begin
          b - hb
            ≡⟨ cong (λ z → z - hb) (sym hb2) ⟩
          (hb + hb) - hb
            ≡⟨ cancel-z hb hb ⟩
          hb ∎
        rhs≡ : (gn + hb) - hb ≡ gn
        rhs≡ = trans (cong (λ z → z - hb) (+-comm gn hb)) (cancel-z hb gn)
        gn< : hb < gn
        gn< = subst₂ _<_ lhs≡ rhs≡ shifted

        -- Denominator scale: ∣g n∣ * ∣l∣ is strictly above D.
        --
        -- 分母刻度严格高于 D。
        p-a : hb * lm < gn * lm
        p-a = *-monoˡ-<-pos lm ⦃ positive 0<∣l∣ ⦄ gn<
        p-b : hb * b ≤ hb * lm
        p-b = *-monoˡ-≤-nonNeg hb ⦃ nonNegative (<⇒≤ (positive⁻¹ hb ⦃ hb-pos ⦄)) ⦄ b≤l
        
        absp : gn * lm ≡ ∣ g n * l ∣
        absp = sym (∣p*q∣≡∣p∣*∣q∣ (g n) l)

        q = ∣ g n * l ∣

        D< : D < q
        D< = subst (λ z → D < z) absp (≤-<-trans p-b p-a)

        gl-nz : NonZero (g n * l)
        gl-nz = prod-nonzero (g n) l (nz n) l-nz
        
        q-nz : NonZero q
        q-nz = ≢-nonZero λ eq → 
                 contradict-nonzero gl-nz (∣p∣≡0⇒p≡0 (g n * l) eq)

        recip1< : 1/_ q ⦃ q-nz ⦄ < 1/_ D ⦃ D-nz ⦄
        recip1< = strict-recip D q 0<D D<

        1D-pos : Positive (1/_ D ⦃ D-nz ⦄)
        1D-pos = 1/pos⇒pos D ⦃ D-pos ⦄

        -- Absolute value of the reciprocal difference.
        --
        -- 倒数之差的绝对值。
        main-eq : ∣ ig - il ∣ ≡ ∣ g n - l ∣ * (1/_ q ⦃ q-nz ⦄)
        main-eq = begin
          ∣ ig - il ∣
            ≡⟨ cong ∣_∣ (recip-diff (g n) l ⦃ nz n ⦄ ⦃ l-nz ⦄) ⟩
          ∣ (l - g n) * 1/_ (g n * l) ⦃ gl-nz ⦄ ∣
            ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (l - g n) (1/_ (g n * l) ⦃ gl-nz ⦄) ⟩
          ∣ l - g n ∣ * ∣ 1/_ (g n * l) ⦃ gl-nz ⦄ ∣
            ≡⟨ cong (∣ l - g n ∣ *_) (abs-recip (g n * l) ⦃ gl-nz ⦄) ⟩
          ∣ l - g n ∣ * 1/_ q ⦃ q-nz ⦄
            ≡⟨ cong (λ z → z * (1/_ q ⦃ q-nz ⦄)) (abs-swap l (g n)) ⟩
          ∣ g n - l ∣ * (1/_ q ⦃ q-nz ⦄) ∎

        -- The first step is non-strict because the numerator factor may
        -- be zero; the second step stays strict from the numerator bound.
        --
        -- 第一步非严格（分子因子可能为零），第二步由分子界保持严格。
        s1 : ∣ g n - l ∣ * (1/_ q ⦃ q-nz ⦄) ≤ ∣ g n - l ∣ * (1/_ D ⦃ D-nz ⦄)
        s1 = *-monoˡ-≤-nonNeg ∣ g n - l ∣
               ⦃ nonNegative (0≤∣p∣ (g n - l)) ⦄ (<⇒≤ recip1<)
               
        s2 : ∣ g n - l ∣ * (1/_ D ⦃ D-nz ⦄) < t * (1/_ D ⦃ D-nz ⦄)
        s2 = let
               e1 : (1/_ D ⦃ D-nz ⦄) * ∣ g n - l ∣ ≡ ∣ g n - l ∣ * (1/_ D ⦃ D-nz ⦄)
               e1 = *-comm (1/_ D ⦃ D-nz ⦄) ∣ g n - l ∣
               
               e2 : (1/_ D ⦃ D-nz ⦄) * t ≡ t * (1/_ D ⦃ D-nz ⦄)
               e2 = *-comm (1/_ D ⦃ D-nz ⦄) t
               
               step : (1/_ D ⦃ D-nz ⦄) * ∣ g n - l ∣ < (1/_ D ⦃ D-nz ⦄) * t
               step = *-monoʳ-<-pos (1/_ D ⦃ D-nz ⦄) ⦃ 1D-pos ⦄ d2
             in subst₂ _<_ e1 e2 step

        cancelD : t * 1/_ D ⦃ D-nz ⦄ ≡ e
        cancelD = begin
          (e * D) * 1/_ D ⦃ D-nz ⦄
            ≡⟨ *-assoc e D (1/_ D ⦃ D-nz ⦄) ⟩
          e * (D * 1/_ D ⦃ D-nz ⦄)
            ≡⟨ cong (e *_) (*-inverseʳ D ⦃ D-nz ⦄) ⟩
          e * 1ℚ
            ≡⟨ *-identityʳ e ⟩
          e ∎

        goal : ∣ ig - il ∣ < e
        goal = subst (λ z → ∣ ig - il ∣ < z) cancelD
                 (≤-<-trans (≤-reflexive main-eq)
                            (≤-<-trans s1 s2))
    in goal
