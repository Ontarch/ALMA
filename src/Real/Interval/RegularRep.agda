------------------------------------------------------------------------
-- Regular rational representatives of interval reals
--
-- 区间实数的正则有理代表
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.RegularRep where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _^_; _∸_)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<N_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m+[n∸m]≡n; ^-monoʳ-≤)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl; +-comm to +-commℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Rational using (ℚ; _*_; _<_; _≤_; ∣_∣; _-_; positive)
open import Data.Rational.Properties using (<⇒≤; pos⇒nonNeg; *-monoʳ-≤-nonNeg)

open import Real using (CauchySeq; ε; embed)
open CauchySeq using (μ)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using
  (centre; width; width-n; recipPow2; bound-w; realI→cauchy; B<2^sucB
  ; frac-strict; 0<width)
open import Real.Interval.Kit using (0<recipPow2)
open import Real.Interval.Reasoning using (begin≤_; begin<_; _≤∎; _≤⟨_⟩_; _≤⟨_⟩<_)

------------------------------------------------------------------------
-- The regular index
--
-- Fold the modulus of realI→cauchy r into a running maximum over
-- successor levels, so that i r k ≥ μ (suc k).
--
-- 正则下标
--
-- 把 realI→cauchy r 的模数在后继层折叠为运行最大值，
-- 使 i r k ≥ μ (suc k)。

i : RealI → ℕ → ℕ
i r zero    = μ (realI→cauchy r) (suc zero)
i r (suc t) = i r t ⊔ μ (realI→cauchy r) (suc (suc t))

i-mono : ∀ r k → i r k ≤N i r (suc k)
i-mono r k = m≤m⊔n (i r k) (μ (realI→cauchy r) (suc (suc k)))

i≥μ : ∀ r k → μ (realI→cauchy r) (suc k) ≤N i r k
i≥μ r zero    = ≤N-refl
i≥μ r (suc k) = m≤n⊔m (i r k) (μ (realI→cauchy r) (suc (suc k)))

i-step : ∀ r k d → i r k ≤N i r (d +ℕ k)
i-step r k zero    = ≤N-refl
i-step r k (suc d) = ≤N-trans (i-step r k d) (i-mono r (d +ℕ k))

i≤ : ∀ r k a → k ≤N a → i r k ≤N i r a
i≤ r k a le with i-step r k (a ∸ k)
... | ih rewrite +-commℕ (a ∸ k) k | m+[n∸m]≡n le = ih

------------------------------------------------------------------------
-- Regular rational representative
--
-- reg r k = centre r (i r k).
--
-- 正则有理代表
--
-- reg r k = centre r (i r k)。

reg : RealI → ℕ → ℚ
reg r t = centre r (i r t)

------------------------------------------------------------------------
-- Width at the regular index
--
-- width r (i r k) < ε (suc k), via frac-strict at the folded
-- precision.
--
-- 正则下标处的宽度
--
-- width r (i r k) < ε (suc k)，在折叠精度处由 frac-strict 得出。

width-i-M : (r : RealI) → ℕ
width-i-M r = proj₁ (bound-w (width r 0) (<⇒≤ (0<width r)))

width-i-M-bound : (r : RealI) → width r 0 ≤ embed (width-i-M r)
width-i-M-bound r = proj₂ (bound-w (width r 0) (<⇒≤ (0<width r)))

width-i-B : (r : RealI) (k : ℕ) →
  width-i-M r *ℕ suc (suc k) <N 2 ^ i r k
width-i-B r k =
  ≤N-trans (B<2^sucB (width-i-M r *ℕ suc (suc k)))
           (^-monoʳ-≤ 2 (i≥μ r k))

width-i-w≤ : (r : RealI) (k : ℕ) →
  width r (i r k) ≤ embed (width-i-M r) * recipPow2 (i r k)
width-i-w≤ r k =
  begin≤
    width r (i r k)
      ≤⟨ width-n r (i r k) ⟩
    width r 0 * recipPow2 (i r k)
      ≤⟨ *-monoʳ-≤-nonNeg
           (recipPow2 (i r k))
           {{pos⇒nonNeg (recipPow2 (i r k))
              {{positive (0<recipPow2 (i r k))}}}}
           (width-i-M-bound r) ⟩
    embed (width-i-M r) * recipPow2 (i r k)
  ≤∎

width-i : ∀ r k → width r (i r k) < ε (suc k)
width-i r k =
  begin<
    width r (i r k)
      ≤⟨ width-i-w≤ r k ⟩<
    frac-strict (width-i-M r) (suc k) (i r k) (width-i-B r k)

------------------------------------------------------------------------
-- Same-real regular values agree past any threshold
--
-- 同一实数的正则值在足够深处一致

reg-reg-ia : ∀ r k a → a ≥N k → i r a ≥N μ (realI→cauchy r) (suc k)
reg-reg-ia r k a a≥k = ≤N-trans (i≥μ r k) (i≤ r k a a≥k)

reg-reg-ib : ∀ r k b → b ≥N k → i r b ≥N μ (realI→cauchy r) (suc k)
reg-reg-ib r k b b≥k = ≤N-trans (i≥μ r k) (i≤ r k b b≥k)

reg-reg : ∀ r k a b → a ≥N k → b ≥N k →
  ∣ reg r a - reg r b ∣ < ε (suc k)
reg-reg r k a b a≥k b≥k =
  CauchySeq.cauchy (realI→cauchy r) (suc k) (i r a) (i r b)
    (reg-reg-ia r k a a≥k) (reg-reg-ib r k b b≥k)
