------------------------------------------------------------------------
-- Reasoning about rational inequalities
--
-- This module provides equational reasoning syntax for _≤_ on ℚ,
-- analogous to the Setoid reasoning modules in the standard library.
--
-- 有理数不等式的推理
--
-- 本模块为 ℚ 上的 _≤_ 提供等式链式推理语法，类似于标准库中的
-- Setoid 推理模块。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Reasoning where

open import Data.Rational using (ℚ; _≤_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Reasoning combinators
--
-- 推理组合子

infix 1 begin≤_
infixr 2 _≈⟨_⟩_ _≤⟨_⟩_
infix 3 _≤∎

begin≤_ : ∀ {x y : ℚ} → x ≤ y → x ≤ y
begin≤ x≤y = x≤y

-- Transport along propositional equality on the left.
--
-- 沿左侧的命题相等传输。
_≈⟨_⟩_ : ∀ (x {y z} : ℚ) → x ≡ y → y ≤ z → x ≤ z
x ≈⟨ p ⟩ q = ≤-trans (≤-reflexive p) q

_≤⟨_⟩_ : ∀ (x {y z} : ℚ) → x ≤ y → y ≤ z → x ≤ z
x ≤⟨ p ⟩ q = ≤-trans p q

_≤∎ : ∀ (x : ℚ) → x ≤ x
x ≤∎ = ≤-refl
