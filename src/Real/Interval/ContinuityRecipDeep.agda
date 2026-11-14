------------------------------------------------------------------------
-- Depth and deep smallness
--
-- 深度与深层小性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipDeep where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Base as NB using (_≤_)
open import Data.Nat.Properties using
  (m≤m+n; +-comm; +-identityʳ; +-suc; +-mono-≤; m∸n+n≡m; m≤m⊔n; m≤n⊔m)
  renaming (≤-refl to ≤-reflℕ; ≤-trans to ≤-transℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Rational using (ℚ; 0ℚ; _<_) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ≤-<-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans; sym)

open import Real.CauchyToInterval using (M; M-mono)
open import Real.IntervalEquiv using (recip2^t; recipPow2)
open import Real.Interval using (RealI; δ; δs≤δ)
open import Real.Interval.ApartnessInvertible using (δ-small; recipPow2-small)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.ContinuityRecipMain using (sample-level)
open import Real.Interval.Kit using (recipPow2-mono)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Recip using (recipCauchy; realI→posCauchy)

------------------------------------------------------------------------
-- Smallness survives any deeper layer
--
-- 小性在任意更深的层仍成立

small-deeper :
  (q : ℚ) → 0ℚ < q →
  Σ ℕ (λ n → (m : ℕ) → n ≤ m → recipPow2 m < q)
small-deeper q q>0 =
  let (n , small) = recipPow2-small q q>0
  in n , (λ m n≤m → ≤-<-trans (recipPow2-mono n≤m) small)

------------------------------------------------------------------------
-- Adding depth never increases the radius
--
-- 加深层数不会放大半径

δ-add : (n k : ℕ) → δ (n + k) ≤ℚ δ n
δ-add n zero =
  subst (λ z → δ z ≤ℚ δ n) (sym (+-identityʳ n)) (≤-refl)
δ-add n (suc k) =
  subst (λ z → δ z ≤ℚ δ n) (sym (+-suc n k))
    (≤-trans (δs≤δ (n + k)) (δ-add n k))

------------------------------------------------------------------------
-- Smallness of the radius survives any added depth
--
-- 半径的小性在任意加深后仍成立

δ-deeper :
  (q : ℚ) → 0ℚ < q →
  Σ ℕ (λ n → (k : ℕ) → δ (n + k) < q)
δ-deeper q q>0 =
  let (n , small) = δ-small q q>0
  in n , (λ k → ≤-<-trans (δ-add n k) small)

------------------------------------------------------------------------
-- Both requirements at one depth
--
-- 同一层上同时满足两条

both-small :
  (qδ qW : ℚ) → 0ℚ < qδ → 0ℚ < qW →
  Σ ℕ (λ n → (δ n < qδ) × (recipPow2 n < qW))
both-small qδ qW qδ>0 qW>0 =
  let (nδ , smallδ) = δ-deeper qδ qδ>0
      (nW , smallW) = small-deeper qW qW>0
  in nδ + nW
   , ( smallδ nW
     , smallW (nδ + nW)
         (subst (λ z → NB._≤_ nW z) (+-comm nW nδ) (m≤m+n nW nδ))
     )

------------------------------------------------------------------------
-- The prefix maximum grows with the level
--
-- 前缀最大值随层号增长

M-iter : (c : _) (n k : ℕ) → M c n ≤ M c (n + k)
M-iter c n zero =
  subst (λ z → M c n ≤ M c z) (sym (+-identityʳ n)) ≤-reflℕ
M-iter c n (suc k) =
  subst (λ z → M c n ≤ M c z) (sym (+-suc n k))
        (≤-transℕ (M-iter c n k) (M-mono c (n + k)))

M-mono-≤ : (c : _) {n m : ℕ} → n ≤ m → M c n ≤ M c m
M-mono-≤ c {n} {m} n≤m =
  let k = m ∸ n
      e : n + k ≡ m
      e = trans (+-comm n k) (m∸n+n≡m {m} {n} n≤m)
  in subst (λ z → M c n ≤ M c z) e (M-iter c n k)

------------------------------------------------------------------------
-- The sampled level grows with the layer index
--
-- 采样层随层号增长

sample-level-mono :
  (x : RealI) (0<x : 0ℝ <ℝ x) {n m : ℕ} → n ≤ m →
  sample-level x 0<x n ≤ sample-level x 0<x m
sample-level-mono x 0<x {n} {m} n≤m =
  +-mono-≤ (≤-reflℕ {proj₁ 0<x})
           (M-mono-≤ (recipCauchy (realI→posCauchy x 0<x)) n≤m)

------------------------------------------------------------------------
-- The radius quota as a depth statement
--
-- 把半径额度改写成深度断言

-- The dyadic tolerance is small at every level beyond a threshold.
-- This is δ-deeper along a full level: a level t beyond n is
-- n + (t ∸ n), so the two agree after rewriting the index.
--
-- 越过某阈值后，二进容差在每一层都小。这是把 δ-deeper 沿完整层号陈述：
-- 超过 n 的层 t 就是 n + (t ∸ n)，改写层号后两者一致。
δ-any :
  (q : ℚ) → 0ℚ < q → Σ ℕ (λ n → (t : ℕ) → n ≤ t → δ t < q)
δ-any q q>0 =
  let (n , deep) = δ-deeper q q>0
  in n , (λ t n≤t →
       let k = t ∸ n
           e : n + k ≡ t
           e = trans (+-comm n k) (m∸n+n≡m {t} {n} n≤t)
       in subst (λ z → δ z < q) e (deep k))

------------------------------------------------------------------------
-- One threshold for both quotas
--
-- 两份额度共用一个阈值

deep-both :
  (q qδ : ℚ) → 0ℚ < q → 0ℚ < qδ →
  Σ ℕ (λ n → (t : ℕ) → n ≤ t → (recip2^t t < q) × (δ t < qδ))
deep-both q qδ 0q 0qδ =
  let (a , sa) = small-deeper q 0q
      (b , sb) = δ-any qδ 0qδ
      n = a ⊔ b
  in n , (λ t n≤t →
       sa t (≤-transℕ (m≤m⊔n a b) n≤t)
       , sb t (≤-transℕ (m≤n⊔m a b) n≤t))
