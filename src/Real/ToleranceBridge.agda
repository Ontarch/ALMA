------------------------------------------------------------------------
-- Arbitrary rational tolerance form of layer-wise convergence
--
-- 逐层收敛的任意正有理容差形态
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.ToleranceBridge where

open import Data.Nat using (ℕ; _≥_)
open import Data.Product using (Σ; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _<_; ∣_∣)
open import Data.Rational.Properties using (<-trans; +-monoʳ-<; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (subst)

open import Real using (ε; ε-half; 0<ε)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (centre)
open import Real.Interval.Complete using (_⟶_)
open import Real.Archimedean using (ε-archimedean)
open import Real.CauchyConvergence using (half-index)

-- The halved tolerance is strictly below the full tolerance.
--
-- 折半容差严格小于完整容差。
half<full : ∀ k → ε (half-index k) < ε k
half<full k =
  let j = half-index k
      base : ε j < ε j + ε j
      base = subst (λ z → z < ε j + ε j) (+-identityʳ (ε j))
               (+-monoʳ-< (ε j) (0<ε j))
  in subst (λ z → ε j < z) (ε-half k) base

-- Layer-wise convergence reflects to a strict full-tolerance bound at
-- the finer centres: reading the sequence at the finer precision and
-- demanding the full bound is guaranteed by f ⟶ L.
--
-- 逐层收敛反映为更细中心处的严格完整容差界：在更细精度处读取序列
-- 并要求完整容差界，由逐层收敛假设保证。
⟶-half-shift : (f : ℕ → RealI) {L : RealI} → f ⟶ L → ∀ k →
  Σ ℕ (λ N → ∀ n → n ≥ N →
    ∣ centre (f n) (half-index k) - centre L (half-index k) ∣ < ε k)
⟶-half-shift f conv k =
  let j = half-index k
      N , witness = conv j
  in N , λ n n≥N → <-trans (witness n n≥N) (half<full k)

-- Layer-wise convergence implies the fully general tolerance
-- statement: for every positive rational e there is an index N after
-- which the centre difference at the selected precision is below e.
--
-- 逐层收敛蕴含完全一般的容差陈述：对每个正有理 e，存在指标 N，此后
-- 所选精度处的中心差严格小于 e。
⟶-tolerance : (f : ℕ → RealI) {L : RealI} → f ⟶ L →
  (e : ℚ) → 0ℚ < e →
  Σ ℕ (λ k → Σ ℕ (λ N → ∀ n → n ≥ N →
    ∣ centre (f n) k - centre L k ∣ < e))
⟶-tolerance f conv e pos =
  let k , ε<e = ε-archimedean e pos
      N , witness = conv k
  in k , N , λ n n≥N → <-trans (witness n n≥N) ε<e
