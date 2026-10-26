------------------------------------------------------------------------
-- Coinductive reals as a neighbourhood tree
--
-- 余归纳实数作为邻域树
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Neighborhood where

open import Data.Nat using (ℕ; suc)
open import Data.Rational using (ℚ; ∣_∣; _-_; _<_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Base.MCorr using (M; here; below)
open import Real.Interval using (δ)
------------------------------------------------------------------------
-- Instantiation of Base.MCorr.M over I = ℚ × ℕ
--
-- With A _ = ⊤ and
--   E (x , k) _ (y , k') = k' ≡ suc k × ∣y - x∣ < δ k,
-- where δ k = 1 / 2^(k+1) is a summable dyadic tolerance. A point of
-- this tree is a coinductive nested sequence of rational centres; the
-- native E-M bisimulation compares nested centres pointwise.
--
-- 在 I = ℚ × ℕ 上实例化 Base.MCorr.M
--
-- 取 A _ = ⊤，边关系如英文所述。δ 为可求和的二进容差。树的一点
-- 即余归纳嵌套有理中心序列；原生 E-M 互模拟逐点比较中心。

-- Index: current rational centre and precision level.
--
-- 索引由当前有理中心与精度层构成。
I : Set
I = ℚ × ℕ

A : I → Set
A _ = ⊤

-- Neighbourhood edge: next level carries any centre within the current
-- dyadic tolerance.
--
-- 邻域边：下一层可取当前二进容差内的任一中心。
E : (i : I) (a : A i) (j : I) → Set
E (x , k) _ (y , k') = k' ≡ suc k × ∣ y - x ∣ < δ k

-- A coinductive real is a point of the neighbourhood tree rooted at a
-- rational starting centre.
--
-- 余归纳实数是以某有理起点为根的邻域树的一点。
RealC : Set
RealC = Σ ℚ λ x → M A E (x , 0)

-- Total nested tree rooted at (q, k): at the next level, whichever
-- centre y is chosen within δ k, the subtree stays at y. The branch
-- y = q gives the constant nested centres equal q.
--
-- 以 (q, k) 为根的全嵌套树：下一层任取容差内的中心 y，子树停在 y；
-- 取 y = q 得到常嵌套中心等于 q。
const-tree : (q : ℚ) (k : ℕ) → M A E (q , k)
const-tree q k .here = tt
const-tree q k .below (y , .(suc k)) (refl , _) =
  const-tree y (suc k)

-- Embed a rational as a coinductive real.
--
-- 将有理数嵌入为余归纳实数。
embedℚ : ℚ → RealC
embedℚ q = q , const-tree q 0
