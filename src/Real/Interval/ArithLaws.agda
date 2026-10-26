------------------------------------------------------------------------
-- Additive group laws for RealI
--
-- Every law is proved via ≈ℝ-of-eq: addition and negation act
-- componentwise on centres, so both sides have pointwise equal centres
-- and the convergence engine trivialises.
--
-- RealI 的加法群律
--
-- 每个定律都经 ≈ℝ-of-eq 证明：加法与取负对中心逐分量作用，故等式
-- 两侧中心逐点相等，收敛引擎退化为平凡。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ArithLaws where

open import Data.Rational using (_+_) renaming (-_ to neg)
open import Data.Rational.Base using (0ℚ)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-assoc; +-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive)
open import Real.IntervalEquiv using (centre)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; negℝ; _-ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Kit using (≈ℝ-of-eq)
open import Real.Interval.Node using (centre-add; centre-neg; centre-0ℝ)

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
    lhs = begin
        centre ((x +ℝ y) +ℝ z) n
      ≡⟨ centre-add (x +ℝ y) z n ⟩
        centre (x +ℝ y) n + cz
      ≡⟨ cong (λ w → w + cz) (centre-add x y n) ⟩
        (cx + cy) + cz
      ∎

    rhs : centre (x +ℝ (y +ℝ z)) n ≡ cx + (cy + cz)
    rhs = begin
        centre (x +ℝ (y +ℝ z)) n
      ≡⟨ centre-add x (y +ℝ z) n ⟩
        cx + centre (y +ℝ z) n
      ≡⟨ cong (λ w → cx + w) (centre-add y z n) ⟩
        cx + (cy + cz)
      ∎
  in begin
      centre ((x +ℝ y) +ℝ z) n
    ≡⟨ lhs ⟩
      (cx + cy) + cz
    ≡⟨ +-assoc cx cy cz ⟩
      cx + (cy + cz)
    ≡⟨ sym rhs ⟩
      centre (x +ℝ (y +ℝ z)) n
    ∎

-- Commutativity
--
-- 交换律
+ℝ-comm : (x y : RealI) → x +ℝ y ≈ℝ y +ℝ x
+ℝ-comm x y = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (x +ℝ y) n
  ≡⟨ centre-add x y n ⟩
    centre x n + centre y n
  ≡⟨ +-comm (centre x n) (centre y n) ⟩
    centre y n + centre x n
  ≡⟨ sym (centre-add y x n) ⟩
    centre (y +ℝ x) n
  ∎

-- Identities
--
-- 单位元
+ℝ-identityˡ : (x : RealI) → 0ℝ +ℝ x ≈ℝ x
+ℝ-identityˡ x = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (0ℝ +ℝ x) n
  ≡⟨ centre-add 0ℝ x n ⟩
    centre 0ℝ n + centre x n
  ≡⟨ cong (λ w → w + centre x n) (centre-0ℝ n) ⟩
    0ℚ + centre x n
  ≡⟨ +-identityˡ (centre x n) ⟩
    centre x n
  ∎

+ℝ-identityʳ : (x : RealI) → x +ℝ 0ℝ ≈ℝ x
+ℝ-identityʳ x = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (x +ℝ 0ℝ) n
  ≡⟨ centre-add x 0ℝ n ⟩
    centre x n + centre 0ℝ n
  ≡⟨ cong (λ w → centre x n + w) (centre-0ℝ n) ⟩
    centre x n + 0ℚ
  ≡⟨ +-identityʳ (centre x n) ⟩
    centre x n
  ∎

-- Inverses
--
-- 逆元
+ℝ-inverseˡ : (x : RealI) → x +ℝ negℝ x ≈ℝ 0ℝ
+ℝ-inverseˡ x = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (x +ℝ negℝ x) n
  ≡⟨ centre-add x (negℝ x) n ⟩
    centre x n + centre (negℝ x) n
  ≡⟨ cong (λ w → centre x n + w) (centre-neg x n) ⟩
    centre x n + neg (centre x n)
  ≡⟨ +-inverseʳ (centre x n) ⟩
    0ℚ
  ≡⟨ sym (centre-0ℝ n) ⟩
    centre 0ℝ n
  ∎

+ℝ-inverseʳ : (x : RealI) → negℝ x +ℝ x ≈ℝ 0ℝ
+ℝ-inverseʳ x = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (negℝ x +ℝ x) n
  ≡⟨ centre-add (negℝ x) x n ⟩
    centre (negℝ x) n + centre x n
  ≡⟨ cong (λ w → w + centre x n) (centre-neg x n) ⟩
    neg (centre x n) + centre x n
  ≡⟨ +-inverseˡ (centre x n) ⟩
    0ℚ
  ≡⟨ sym (centre-0ℝ n) ⟩
    centre 0ℝ n
  ∎

-- Negation involution
--
-- 取负对合
negℝ-negℝ : (x : RealI) → negℝ (negℝ x) ≈ℝ x
negℝ-negℝ x = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (negℝ (negℝ x)) n
  ≡⟨ centre-neg (negℝ x) n ⟩
    neg (centre (negℝ x) n)
  ≡⟨ cong neg (centre-neg x n) ⟩
    neg (neg (centre x n))
  ≡⟨ neg-involutive (centre x n) ⟩
    centre x n
  ∎

negℝ-0ℝ : negℝ 0ℝ ≈ℝ 0ℝ
negℝ-0ℝ = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (negℝ 0ℝ) n
  ≡⟨ centre-neg 0ℝ n ⟩
    neg (centre 0ℝ n)
  ≡⟨ cong neg (centre-0ℝ n) ⟩
    neg 0ℚ
  ≡⟨ sym (centre-0ℝ n) ⟩
    centre 0ℝ n
  ∎

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
    lhs = begin
        centre ((x -ℝ y) +ℝ z) n
      ≡⟨ centre-add (x -ℝ y) z n ⟩
        centre (x -ℝ y) n + cz
      ≡⟨ cong (λ w → w + cz) (begin
            centre (x -ℝ y) n
          ≡⟨ centre-add x (negℝ y) n ⟩
            cx + centre (negℝ y) n
          ≡⟨ cong (λ w → cx + w) (centre-neg y n) ⟩
            cx + ncy
          ∎) ⟩
        (cx + ncy) + cz
      ∎

    rhs : centre ((x +ℝ z) -ℝ y) n ≡ (cx + cz) + ncy
    rhs = begin
        centre ((x +ℝ z) -ℝ y) n
      ≡⟨ centre-add (x +ℝ z) (negℝ y) n ⟩
        centre (x +ℝ z) n + centre (negℝ y) n
      ≡⟨ cong (λ w → w + centre (negℝ y) n) (centre-add x z n) ⟩
        (cx + cz) + centre (negℝ y) n
      ≡⟨ cong (λ w → (cx + cz) + w) (centre-neg y n) ⟩
        (cx + cz) + ncy
      ∎

    key : (cx + ncy) + cz ≡ (cx + cz) + ncy
    key = begin
        (cx + ncy) + cz
      ≡⟨ +-assoc cx ncy cz ⟩
        cx + (ncy + cz)
      ≡⟨ cong (cx +_) (+-comm ncy cz) ⟩
        cx + (cz + ncy)
      ≡⟨ sym (+-assoc cx cz ncy) ⟩
        (cx + cz) + ncy
      ∎
  in begin
      centre ((x -ℝ y) +ℝ z) n
    ≡⟨ lhs ⟩
      (cx + ncy) + cz
    ≡⟨ key ⟩
      (cx + cz) + ncy
    ≡⟨ sym rhs ⟩
      centre ((x +ℝ z) -ℝ y) n
    ∎
