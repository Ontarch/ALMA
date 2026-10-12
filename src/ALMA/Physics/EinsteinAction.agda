------------------------------------------------------------------------
-- Einstein–Hilbert action as a combinatorial chain functional
--
-- The Einstein–Hilbert action on a causal set is a finite weighted sum
-- over chain counts. This module supplies the action, its interval form,
-- and the variation skeleton.
--
-- 爱因斯坦–希尔伯特作用量作为组合链泛函
--
-- 因果集上的爱因斯坦–希尔伯特作用量是链计数上的有限加权和。本模块
-- 给出作用量、其区间形式与变分骨架。
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
open ALMA.Physics.CausalSet.Core using (chains; between; events)
open import ALMA.Physics.CausalCurvature using (curved5; curved3)

------------------------------------------------------------------------
-- Weighted action over total k-chain counts
--
-- On a causal set the action has no integral over a continuum volume:
-- it is the integer weighted sum
--
--   action coeffs = Σ_k coeff_k · chains k .
--
-- The coefficients coeff_k carry the dimension and the
-- fundamental-volume calibration and are an argument.
--
-- 总 k-链计数上的加权作用量
--
-- 因果集上的作用量无需对连续体积积分：它是整数加权和
--
--   action coeffs = Σ_k coeff_k · chains k 。
--
-- 系数 coeff_k 携带维度与基本体积标定，作为参数。

weighted : List ℤ → ℕ → (ℕ → ℕ) → ℤ
weighted [] k f = + 0
weighted (c ∷ cs) k f = c * + (f k) + weighted cs (suc k) f

action : ∀ n (o : Fin n → Fin n → Bool) → List ℤ → ℤ
action n o coeffs = weighted coeffs 1 (chains n o)

------------------------------------------------------------------------
-- Interval form
--
-- Every k-chain has a unique least and greatest event, so summing the
-- endpoint-fixed chain count between over all event pairs recovers the
-- total number of k-chains:
--
--   Σ_{x, y} between k x y = chains k ,
--
--   action coeffs = Σ_{x, y} Σ_k coeff_k · between k x y .
--
-- The identity is checked on the three reference intervals.
--
-- 区间形式
--
-- 每条 k-链有唯一的最小与最大事件，故对所有事件对求和端点固定链数
-- between，即复原 k-链总数：
--
--   Σ_{x, y} between k x y = chains k ，
--
--   action coeffs = Σ_{x, y} Σ_k coeff_k · between k x y 。
--
-- 该恒等式在三个参考区间上检验。

sumBetween : ∀ n (o : Fin n → Fin n → Bool) → ℕ → ℕ
sumBetween n o k =
  sumOver (events n o) λ x →
  sumOver (events n o) λ y → between n o k x y

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
-- The three-chain action (coeffs 0, 0, 1) on the reference intervals
--
-- 参考区间上的三链作用量（系数 0, 0, 1）

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
-- The discrete variation compares the action of two finite intervals;
-- stationarity, the causal-set analogue of the Einstein equation, is
-- the condition that this variation vanish. The flat interval has zero
-- self-variation, giving the stationarity reference.
--
-- 相对平直区间的离散变分
--
-- 离散变分比较两个有限区间的作用量；平稳性（爱因斯坦方程在因果集
-- 的对应）即该变分消失的条件。平直区间自变分为零，作为平稳性参考。

variation5 : action 5 curved5 c3coeffs - action 4 diamond c3coeffs ≡ + 1
variation5 = refl
variation3 : action 3 curved3 c3coeffs - action 4 diamond c3coeffs
           ≡ + 0 - + 1
variation3 = refl

stationary-flat : action 4 diamond c3coeffs - action 4 diamond c3coeffs
                ≡ + 0
stationary-flat = refl
