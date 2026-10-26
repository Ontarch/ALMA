------------------------------------------------------------------------
-- Representation round-trip equivalence
--
-- 表示往返等价
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Retract where

open import Data.Nat using () renaming (_≤_ to _≤N_)
open import Data.Nat.Properties
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _-_; _*_; ∣_∣)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong)

open import Real using (CauchySeq)
open import Real.Interval using (RealI)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Node using (0≤width-n)
open import Real.IntervalEquiv using
  (realI→cauchy; μx-dom; centre; width; recipPow2; centre-diff≤)
open import Real.CauchyToInterval using
  (cauchy→realI; M; K; M≥μK; K≥k; centre-cauchy→realI)
open import Real.Interval.Kit using (≈ℝ-of-rec)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Interval side
--
-- The rebuilt interval is equivalent to the original. At level n its
-- centre is the sampled centre of r = realI→cauchy x at index M r n,
-- which is centre x (M r n). Since M r n ≥ n, the two centres differ
-- by at most the width at level n, bounded by w0 · recipPow2 n.
--
-- 区间侧
--
-- 重建区间与原区间等价。第 n 层中心取柯西序列 r 在相应折叠下标处的
-- 采样中心；该下标不小于 n，故两中心之差不超过第 n 层宽度，并以
-- w0 · recipPow2 n 为界。

cauchy→realI-retract : (x : RealI)
                     → cauchy→realI (realI→cauchy x) ≈ℝ x
cauchy→realI-retract x = ≈ℝ-of-rec y x w0 0≤w0 bound
  where
  r : CauchySeq
  r = realI→cauchy x

  y : RealI
  y = cauchy→realI r

  w0 : ℚ
  w0 = width x 0

  0≤w0 : 0ℚ ≤ w0
  0≤w0 = 0≤width-n x 0

  Mn≥n : ∀ n → n ≤N M r n
  Mn≥n n =
    ≤N-trans (K≥k n)
    (≤N-trans (μx-dom x (K n)) (M≥μK r n))

  eq : ∀ n → centre y n ≡ centre x (M r n)
  eq n = trans (centre-cauchy→realI r n) refl

  bound : ∀ n →
    ∣ centre y n - centre x n ∣ ≤ w0 * recipPow2 n
  bound n = begin≤
    ∣ centre y n - centre x n ∣
      ≈⟨ cong (λ z → ∣ z - centre x n ∣) (eq n) ⟩
    ∣ centre x (M r n) - centre x n ∣
      ≤⟨ centre-diff≤ x n (M r n) n (Mn≥n n) ≤N-refl ⟩
    w0 * recipPow2 n
    ≤∎
