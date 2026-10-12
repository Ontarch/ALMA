------------------------------------------------------------------------
-- Einstein–Hilbert action as a combinatorial chain functional
--
-- On a causal set the Einstein–Hilbert action has no integral over a
-- continuum volume: it is a finite sum over chain counts. Every k-chain
-- has a unique least and greatest event, so summing the endpoint-fixed
-- chain count between over all event pairs recovers the total number of
-- k-chains:
--
--   Σ_{x, y} between k x y = chains k .
--
-- The action is therefore the integer weighted sum
--
--   action coeffs = Σ_k coeff_k · chains k
--                 = Σ_{x, y} Σ_k coeff_k · between k x y ,
--
-- the causal-set form of the Einstein–Hilbert (Benincasa–Dowker type)
-- action. The coefficients coeff_k carry the dimension and the
-- fundamental-volume calibration and are an argument.
--
-- The discrete variation compares the action of two finite intervals;
-- stationarity, the causal-set analogue of the Einstein equation, is the
-- condition that this variation vanish. Using the three-chain action
-- (coeffs 0,0,1):
--
--   flat diamond   action = 2 ,
--   five-event     action = 3 ,  variation +1 ,
--   three-event    action = 1 ,  variation −1 .
--
-- The identity Σ between = chains is checked on all three reference
-- intervals, alongside the action values and variations. This module
-- supplies the action, its interval form, and the variation skeleton; it
-- does not assert a universal coefficient table.
--
-- 爱因斯坦–希尔伯特作用量作为组合链泛函
--
-- 因果集上的爱因斯坦–希尔伯特作用量无需对连续体积积分：它是链计数的有
-- 限和。每条 k-链有唯一的最小与最大事件，故对所有事件对求和端点固定链
-- 数，即恢复 k-链总数：
--
--   Σ_{x, y} between k x y = chains k 。
--
-- 作用量因而是整数加权和
--
--   action coeffs = Σ_k coeff_k · chains k
--                 = Σ_{x, y} Σ_k coeff_k · between k x y ，
--
-- 即爱因斯坦–希尔伯特（Benincasa–Dowker 型）作用量的因果集形式。系数
-- coeff_k 携带维度与基本体积标定，作为参数。
--
-- 离散变分比较两个有限区间的作用量；平稳性（爱因斯坦方程的因果集对应）
-- 即该变分消失的条件。用三链作用量（系数 0,0,1）：
--
--   平坦菱形 action = 2 ，
--   五事件   action = 3 ，变分 +1 ，
--   三事件   action = 1 ，变分 −1 。
--
-- 恒等式 Σ between = chains 在三个参考区间上检验，并附作用量值与变分。本
-- 模块给出作用量、其区间形式与变分骨架；不冒称普适系数表。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.EinsteinAction where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; [])
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ALMA.Physics.CausalSet using (diamond; sumOver)
open ALMA.Physics.CausalSet.Core
  using (chains; between; events)
open import ALMA.Physics.CausalCurvature using (curved5; curved3)

------------------------------------------------------------------------
-- Weighted action over total k-chain counts
--
-- 总 k-链计数上的加权作用量

weighted : List ℤ → ℕ → (ℕ → ℕ) → ℤ
weighted [] k f = + 0
weighted (c ∷ cs) k f = c * + (f k) + weighted cs (suc k) f

action : ∀ n (o : Fin n → Fin n → Bool) → List ℤ → ℤ
action n o coeffs = weighted coeffs 1 (chains n o)

------------------------------------------------------------------------
-- Interval form: summing between over all event pairs
--
-- 区间形式：对所有事件对求和 between

sumBetween : ∀ n (o : Fin n → Fin n → Bool) → ℕ → ℕ
sumBetween n o k =
  sumOver (events n o) λ x →
  sumOver (events n o) λ y → between n o k x y

-- The interval sum equals the total k-chain count on each reference.
--
-- 区间和在每个参考上等于 k-链总数。
sum≡chains-diamond : ∀ k → sumBetween 4 diamond k ≡ chains 4 diamond k
sum≡chains-diamond zero = refl
sum≡chains-diamond 1 = refl
sum≡chains-diamond 2 = refl
sum≡chains-diamond 3 = refl
sum≡chains-diamond (suc (suc (suc (suc _)))) = refl

sum≡chains-curved5 : ∀ k → sumBetween 5 curved5 k ≡ chains 5 curved5 k
sum≡chains-curved5 zero = refl
sum≡chains-curved5 1 = refl
sum≡chains-curved5 2 = refl
sum≡chains-curved5 3 = refl
sum≡chains-curved5 (suc (suc (suc (suc _)))) = refl

sum≡chains-curved3 : ∀ k → sumBetween 3 curved3 k ≡ chains 3 curved3 k
sum≡chains-curved3 zero = refl
sum≡chains-curved3 1 = refl
sum≡chains-curved3 2 = refl
sum≡chains-curved3 3 = refl
sum≡chains-curved3 (suc (suc (suc (suc _)))) = refl

------------------------------------------------------------------------
-- The three-chain action (coeffs 0,0,1) on the reference intervals
--
-- 参考区间上的三链作用量（系数 0,0,1）

c3coeffs : List ℤ
c3coeffs = + 0 ∷ + 0 ∷ + 1 ∷ []

action-diamond : action 4 diamond c3coeffs ≡ + 2
action-diamond = refl
action-curved5 : action 5 curved5 c3coeffs ≡ + 3
action-curved5 = refl
action-curved3 : action 3 curved3 c3coeffs ≡ + 1
action-curved3 = refl

------------------------------------------------------------------------
-- Discrete variation relative to the flat interval
--
-- 相对平坦区间的离散变分

variation5 : action 5 curved5 c3coeffs - action 4 diamond c3coeffs ≡ + 1
variation5 = refl
variation3 : action 3 curved3 c3coeffs - action 4 diamond c3coeffs
           ≡ + 0 - + 1
variation3 = refl

-- The flat interval has zero self-variation: the stationarity reference.
--
-- 平坦区间自变分为零：平稳性参考。
stationary-flat : action 4 diamond c3coeffs - action 4 diamond c3coeffs
                ≡ + 0
stationary-flat = refl
