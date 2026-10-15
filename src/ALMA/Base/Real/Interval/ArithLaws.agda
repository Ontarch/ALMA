------------------------------------------------------------------------
-- Additive group laws for RealI
--
-- RealI carries an abelian group structure up to _≈ℝ_. Every law here
-- goes through ≈ℝ-of-eq: addition and negation act componentwise on
-- centres, so the two sides of each equation have pointwise equal
-- centres and the convergence engine trivialises.
--
-- RealI 的加法群律
--
-- RealI 在 _≈ℝ_ 意义下构成阿贝尔群。此处每个定律都走 ≈ℝ-of-eq：
-- 加法与取负对中心逐分量作用，故等式两侧中心逐点相等，收敛引擎
-- 退化为平凡。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.ArithLaws where

open import Data.Rational using (_+_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-assoc; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym)

open import ALMA.Base.Real.IntervalEquiv using (centre)
open import ALMA.Base.Real.Interval using (RealI; neg-invol)
open import ALMA.Base.Real.Interval.Arith using (0ℝ; _+ℝ_; negℝ; _-ℝ_)
open import ALMA.Base.Real.Interval.Equiv using (_≈ℝ_)
open import ALMA.Base.Real.Interval.Kit using (≈ℝ-of-eq)
open import ALMA.Base.Real.Interval.Node using (centre-add; centre-neg; centre-0ℝ)

------------------------------------------------------------------------
-- Associativity
--
-- 结合律

+ℝ-assoc : (x y z : RealI) →
           (x +ℝ y) +ℝ z ≈ℝ x +ℝ (y +ℝ z)
+ℝ-assoc x y z = ≈ℝ-of-eq _ _ λ n →
  let
    cx = centre x n
    cy = centre y n
    cz = centre z n

    lhs : centre ((x +ℝ y) +ℝ z) n ≡ (cx + cy) + cz
    lhs = trans (centre-add (x +ℝ y) z n)
                (cong (λ w → w + cz) (centre-add x y n))

    rhs : centre (x +ℝ (y +ℝ z)) n ≡ cx + (cy + cz)
    rhs = trans (centre-add x (y +ℝ z) n)
                (cong (λ w → cx + w) (centre-add y z n))
  in trans lhs (trans (+-assoc cx cy cz) (sym rhs))

------------------------------------------------------------------------
-- Commutativity
--
-- 交换律

+ℝ-comm : (x y : RealI) → x +ℝ y ≈ℝ y +ℝ x
+ℝ-comm x y = ≈ℝ-of-eq _ _ λ n →
  trans (centre-add x y n)
  (trans (+-comm (centre x n) (centre y n))
         (sym (centre-add y x n)))

------------------------------------------------------------------------
-- Identities
--
-- 单位元

+ℝ-identityˡ : (x : RealI) → 0ℝ +ℝ x ≈ℝ x
+ℝ-identityˡ x = ≈ℝ-of-eq _ _ λ n →
  trans (centre-add 0ℝ x n)
  (trans (cong (λ w → w + centre x n) (centre-0ℝ n))
         (+-identityˡ (centre x n)))

+ℝ-identityʳ : (x : RealI) → x +ℝ 0ℝ ≈ℝ x
+ℝ-identityʳ x = ≈ℝ-of-eq _ _ λ n →
  trans (centre-add x 0ℝ n)
  (trans (cong (λ w → centre x n + w) (centre-0ℝ n))
         (+-identityʳ (centre x n)))

------------------------------------------------------------------------
-- Inverses
--
-- 逆元

+ℝ-inverseˡ : (x : RealI) → x +ℝ negℝ x ≈ℝ 0ℝ
+ℝ-inverseˡ x = ≈ℝ-of-eq _ _ λ n →
  trans (centre-add x (negℝ x) n)
  (trans (cong (λ w → centre x n + w) (centre-neg x n))
  (trans (+-inverseʳ (centre x n))
         (sym (centre-0ℝ n))))

+ℝ-inverseʳ : (x : RealI) → negℝ x +ℝ x ≈ℝ 0ℝ
+ℝ-inverseʳ x = ≈ℝ-of-eq _ _ λ n →
  trans (centre-add (negℝ x) x n)
  (trans (cong (λ w → w + centre x n) (centre-neg x n))
  (trans (+-inverseˡ (centre x n))
         (sym (centre-0ℝ n))))

------------------------------------------------------------------------
-- Negation involution
--
-- 取负对合

negℝ-negℝ : (x : RealI) → negℝ (negℝ x) ≈ℝ x
negℝ-negℝ x = ≈ℝ-of-eq _ _ λ n →
  trans (centre-neg (negℝ x) n)
  (trans (cong neg (centre-neg x n))
         (neg-invol (centre x n)))

negℝ-0ℝ : negℝ 0ℝ ≈ℝ 0ℝ
negℝ-0ℝ = ≈ℝ-of-eq _ _ λ n →
  trans (centre-neg 0ℝ n)
  (trans (cong neg (centre-0ℝ n))
         (sym (centre-0ℝ n)))

------------------------------------------------------------------------
-- Derived laws
--
-- 导出律

x-ℝx : (x : RealI) → x -ℝ x ≈ℝ 0ℝ
x-ℝx x = +ℝ-inverseˡ x

-ℝ-add : (x y z : RealI) → (x -ℝ y) +ℝ z ≈ℝ (x +ℝ z) -ℝ y
-ℝ-add x y z = ≈ℝ-of-eq _ _ λ n →
  let
    cx  = centre x n
    cy  = centre y n
    cz  = centre z n
    ncy = neg cy

    lhs : centre ((x -ℝ y) +ℝ z) n ≡ (cx + ncy) + cz
    lhs = trans (centre-add (x -ℝ y) z n)
          (cong (λ w → w + cz)
            (trans (centre-add x (negℝ y) n)
                   (cong (λ w → cx + w) (centre-neg y n))))

    rhs : centre ((x +ℝ z) -ℝ y) n ≡ (cx + cz) + ncy
    rhs = trans (centre-add (x +ℝ z) (negℝ y) n)
          (trans (cong (λ w → w + centre (negℝ y) n) (centre-add x z n))
                 (cong (λ w → (cx + cz) + w) (centre-neg y n)))

    key : (cx + ncy) + cz ≡ (cx + cz) + ncy
    key =
      trans (+-assoc cx ncy cz)
      (trans (cong (cx +_) (+-comm ncy cz))
             (sym (+-assoc cx cz ncy)))
  in trans lhs (trans key (sym rhs))
