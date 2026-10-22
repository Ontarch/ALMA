------------------------------------------------------------------------
-- Reasoning combinators for interval equality
--
-- 区间相等的推理组合子
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Reasoning.Equiv where

open import Real.Interval using (RealI)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-trans; ≈ℝ-refl)

infix 1 beginℝ_
infixr 2 _≈ℝ⟨_⟩_
infix 3 _∎ℝ

-- Start an equation chain.
--
-- 开始一条等式链。
beginℝ_ : ∀ {x y : RealI} → x ≈ℝ y → x ≈ℝ y
beginℝ_ x≈y = x≈y

-- One step of an equation chain.
--
-- 等式链的一步。
_≈ℝ⟨_⟩_ : ∀ (x : RealI) {y z : RealI} → x ≈ℝ y → y ≈ℝ z → x ≈ℝ z
x ≈ℝ⟨ p ⟩ q = ≈ℝ-trans p q

-- Close an equation chain.
--
-- 结束一条等式链。
_∎ℝ : ∀ (x : RealI) → x ≈ℝ x
x ∎ℝ = ≈ℝ-refl
