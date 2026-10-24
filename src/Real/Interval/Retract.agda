------------------------------------------------------------------------
-- Representation round-trip equivalence
--
-- 表示往返等价
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Retract where

open import Data.Nat using (ℕ) renaming (_≤_ to _≤N_; _≥_ to _≥N_)
open import Data.Nat.Properties
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _-_; _*_; ∣_∣)
open import Data.Rational.Properties using (≤-trans)
  renaming (≤-refl to ≤Q-refl)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; sym; subst; cong)

open import Real using (CauchySeq)
open CauchySeq using (f)
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
-- Interval side: cauchy→realI (realI→cauchy x) ≈ℝ x
--
-- The centre of the rebuilt interval at level n is the sampled centre
-- of the Cauchy sequence r = realI→cauchy x at index M r n, which is
-- centre x (M r n). Since M r n ≥ n, the two centres differ by at most
-- the width at level n, bounded by w0 · recipPow2 n.
--
-- 区间侧：cauchy→realI (realI→cauchy x) ≈ℝ x
--
-- 重建区间第 n 层中心是柯西序列 r = realI→cauchy x 在下标 M r n 处
-- 的采样中心，即 centre x (M r n)。因 M r n ≥ n，两中心之差至多为
-- 第 n 层宽度，以 w0 · recipPow2 n 为界。

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
