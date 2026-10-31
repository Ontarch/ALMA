------------------------------------------------------------------------
-- Reasoning about rational inequalities
--
-- 有理数不等式的推理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Reasoning where

open import Data.Rational using (ℚ; _≤_; _<_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <-trans; <-≤-trans; ≤-<-trans)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Equational reasoning syntax for _≤_ and _<_ on ℚ
--
-- ℚ 上 _≤_ 与 _<_ 的链式推理语法

infix 1 begin≤_ begin<_
infixr 2 _≈⟨_⟩_ _≤⟨_⟩_ _≤⟨_⟩<_ _<⟨_⟩<_ _<⟨_⟩≤[_]
infix 3 _≤∎

begin≤_ : ∀ {x y : ℚ} → x ≤ y → x ≤ y
begin≤ x≤y = x≤y

begin<_ : ∀ {x y : ℚ} → x < y → x < y
begin< x<y = x<y

-- Transport along propositional equality on the left.
--
-- 沿左侧的命题相等传输。
_≈⟨_⟩_ : ∀ (x {y z} : ℚ) → x ≡ y → y ≤ z → x ≤ z
x ≈⟨ p ⟩ q = ≤-trans (≤-reflexive p) q

-- Basic chain step and terminal.
--
-- 基本链步骤与终点。
_≤⟨_⟩_ : ∀ (x {y z} : ℚ) → x ≤ y → y ≤ z → x ≤ z
x ≤⟨ p ⟩ q = ≤-trans p q

_≤∎ : ∀ (x : ℚ) → x ≤ x
x ≤∎ = ≤-refl

-- Mixed chains: each step switches between ≤ and <.
--
-- 混合链：每步在 ≤ 与 < 之间切换。
_≤⟨_⟩<_ : ∀ (x {y z} : ℚ) → x ≤ y → y < z → x < z
x ≤⟨ p ⟩< q = ≤-<-trans p q

_<⟨_⟩<_ : ∀ (x {y z} : ℚ) → x < y → y < z → x < z
x <⟨ p ⟩< q = <-trans p q

-- Termination of a mixed chain: the proof is bracketed explicitly.
--
-- 混合链的收尾：证明用方括号显式给出。
_<⟨_⟩≤[_] : ∀ (x {y z} : ℚ) → x < y → y ≤ z → x < z
x <⟨ p ⟩≤[ q ] = <-≤-trans p q
