------------------------------------------------------------------------
-- Remaining algebraic laws for additive negation
--
-- 加法取负的剩余代数定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.NegLaws where

open import Data.Rational using (_+_) renaming (-_ to neg)
open import Data.Rational.Properties using (neg-distrib-+)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Real.Interval using (RealI)
open import Real.Interval.Arith using (_+ℝ_; negℝ)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.IntervalEquiv using (centre)
open import Real.Interval.Node using (centre-add; centre-neg)
open import Real.Interval.Kit using (≈ℝ-of-eq)

------------------------------------------------------------------------
-- Negation distributes over addition.
--
-- 取负对加法分配。
negℝ-+-distrib : (x y : RealI) →
  negℝ (x +ℝ y) ≈ℝ negℝ x +ℝ negℝ y
negℝ-+-distrib x y = ≈ℝ-of-eq _ _ λ n →
  begin
    centre (negℝ (x +ℝ y)) n
      ≡⟨ centre-neg (x +ℝ y) n ⟩
    neg (centre (x +ℝ y) n)
      ≡⟨ cong neg (centre-add x y n) ⟩
    neg (centre x n + centre y n)
      ≡⟨ neg-distrib-+ (centre x n) (centre y n) ⟩
    neg (centre x n) + neg (centre y n)
      ≡⟨ sym (cong₂ _+_ (centre-neg x n) (centre-neg y n)) ⟩
    centre (negℝ x) n + centre (negℝ y) n
      ≡⟨ sym (centre-add (negℝ x) (negℝ y) n) ⟩
    centre (negℝ x +ℝ negℝ y) n
  ∎
