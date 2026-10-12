------------------------------------------------------------------------
-- Curvature as the deviation of causal chain counts
--
-- In a causal set the metric is not a field: curvature is detected by
-- how the chain content of an Alexandrov interval departs from a flat
-- reference. This module uses the minimal flat diamond as the reference
-- and checks three finite intervals against it.
--
-- 曲率即因果链计数的偏差
--
-- 因果集中度规不是字段：曲率通过 Alexandrov 区间的链含量相对平坦参考
-- 的偏差来检测。本模块以最小平坦菱形为参考，并对三个有限区间作检验。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.CausalCurvature where

open import Data.Nat using (ℕ; zero; suc) renaming (_≡ᵇ_ to _≡ℕᵇ_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; _∧_; _∨_)
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ALMA.Physics.CausalSet using (diamond)
open ALMA.Physics.CausalSet.Core using (between; interval-volume)
------------------------------------------------------------------------
-- Flat reference values for the minimal diamond
--
-- A smallest 1+1 interval has two spacelike interior events, so it has
--
--   three-chain count  between 3 x y = 2 ,
--   interval volume    interval-volume x y = 4 .
--
-- 最小菱形的平坦参考值
--
-- 最小的 1+1 区间有两个类空内部事件，故
--
--   三链数  between 3 x y = 2 ，
--   区间体积 interval-volume x y = 4 。

flat-between3 : ℕ
flat-between3 = 2

flat-volume : ℕ
flat-volume = 4

------------------------------------------------------------------------
-- Integer curvature deviations
--
-- The curvature signals are the integer deviations
--
--   dev3 x y = between 3 x y − 2 ,
--   devV x y = interval-volume x y − 4 .
--
-- The sign convention is combinatorial: more interior chains than the
-- flat reference give a positive deviation, fewer give a negative one.
-- The dimension-specific physical calibration is the coefficient
-- argument of CausalSet.curvatureAt and is not fixed here.
--
-- 整数曲率偏差
--
-- 曲率信号为整数偏差
--
--   dev3 x y = between 3 x y − 2 ，
--   devV x y = interval-volume x y − 4 。
--
-- 符号约定是组合性的：内部链比平坦参考多则偏差为正，少则为负。维度
-- 相关的物理标定是 CausalSet.curvatureAt 的系数参数，不在此固定。

dev3 : ∀ n (o : Fin n → Fin n → Bool) → Fin n → Fin n → ℤ
dev3 n o x y = + (between n o 3 x y) - + flat-between3

devV : ∀ n (o : Fin n → Fin n → Bool) → Fin n → Fin n → ℤ
devV n o x y = + (interval-volume n o x y) - + flat-volume

------------------------------------------------------------------------
-- Curved reference intervals
--
-- 弯曲参考区间

-- Five events: bottom 0, top 4, three spacelike interior events.
--
-- 五事件：底 0，顶 4，三个类空内部事件。
curved5 : Fin 5 → Fin 5 → Bool
curved5 x y =
  let a = toℕ x; b = toℕ y in
  ((a ≡ℕᵇ 0)
     ∧ ((b ≡ℕᵇ 1) ∨ (b ≡ℕᵇ 2) ∨ (b ≡ℕᵇ 3) ∨ (b ≡ℕᵇ 4)))
  ∨ (((a ≡ℕᵇ 1) ∨ (a ≡ℕᵇ 2) ∨ (a ≡ℕᵇ 3))
       ∧ (b ≡ℕᵇ 4))

-- Three events: bottom 0, one interior 1, top 2 (a pure chain).
--
-- 三事件：底 0，一个内部 1，顶 2（纯链）。
curved3 : Fin 3 → Fin 3 → Bool
curved3 x y =
  let a = toℕ x; b = toℕ y in
  ((a ≡ℕᵇ 0) ∧ ((b ≡ℕᵇ 1) ∨ (b ≡ℕᵇ 2)))
  ∨ ((a ≡ℕᵇ 1) ∧ (b ≡ℕᵇ 2))

------------------------------------------------------------------------
-- Endpoint shorthands
--
-- 端点简写

d4 : Fin 5
d4 = Data.Fin.fromℕ 4

d2 : Fin 3
d2 = Data.Fin.fromℕ 2

d3 : Fin 4
d3 = Data.Fin.fromℕ 3

------------------------------------------------------------------------
-- Flat interval: zero curvature
--
-- 平坦区间：零曲率

flat-dev3 : dev3 4 diamond Data.Fin.zero d3 ≡ + 0
flat-dev3 = refl
flat-devV : devV 4 diamond Data.Fin.zero d3 ≡ + 0
flat-devV = refl

------------------------------------------------------------------------
-- Five-event interval: positive deviation one
--
-- 五事件区间：正偏差一

c5-dev3 : dev3 5 curved5 Data.Fin.zero d4 ≡ + 1
c5-dev3 = refl
c5-devV : devV 5 curved5 Data.Fin.zero d4 ≡ + 1
c5-devV = refl

------------------------------------------------------------------------
-- Three-event interval: negative deviation one
--
-- 三事件区间：负偏差一

c3-dev3 : dev3 3 curved3 Data.Fin.zero d2 ≡ + 0 - + 1
c3-dev3 = refl
c3-devV : devV 3 curved3 Data.Fin.zero d2 ≡ + 0 - + 1
c3-devV = refl
