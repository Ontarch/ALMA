------------------------------------------------------------------------
-- Four-dimensional Benincasa–Dowker action
--
-- The integer chain core of the four-dimensional Benincasa–Dowker
-- action, computed purely from the causal order. The physical
-- calibration factors are external and are not formalized here.
--
-- 四维 Benincasa–Dowker 作用量
--
-- 四维 Benincasa–Dowker 作用量的整数链核，纯由因果序计算。物理标定
-- 因子为外部因素，不在此形式化。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.FourDAction where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _≡ᵇ_ to _≡ℕᵇ_)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ALMA.Physics.CausalSet using (diamond; boolFilter; sumOver; module Core)
open Core using (events; interval-volume)

------------------------------------------------------------------------
-- k-abundance
--
-- N_k counts strictly ordered pairs (x, y) whose inclusive order
-- interval has cardinality exactly k + 2:
--
--   N_k = |{ (x, y) : x ≺ y, |I[x, y]| = k + 2 }| .
--
-- k-丰度
--
-- N_k 计数包含区间基数恰为 k + 2 的严格可比对 (x, y)：
--
--   N_k = |{ (x, y)：x ≺ y，|I[x, y]| = k + 2 }| 。

abundance : ∀ n (o : Fin n → Fin n → Bool) → ℕ → ℕ
abundance n o k =
  sumOver (events n o) λ x →
  sumOver (boolFilter (λ y → o x y) (events n o)) λ y →
  if interval-volume n o x y ≡ℕᵇ (k +ℕ 2) then 1 else 0

N0 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N0 n o = abundance n o 0
N1 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N1 n o = abundance n o 1
N2 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N2 n o = abundance n o 2
N3 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N3 n o = abundance n o 3

------------------------------------------------------------------------
-- Integer four-dimensional BD core
--
-- The discrete scalar curvature at an event x and the action over a
-- finite causal set C with n events are
--
--   R(x) = (4 / √6) · (1 / l²) · [ 1 − N₀(x) + 9 N₁(x)
--                                   − 16 N₂(x) + 8 N₃(x) ] ,
--
--   S(C) / ℏ = (4 / √6) · (l / l_p)² · [ n − N₀ + 9 N₁
--                                          − 16 N₂ + 8 N₃ ] .
--
-- Only the bracketed integer is formalized here. The factors (4 / √6),
-- (1 / l²) and (l / l_p)² contain the irrational √6 and are external
-- calibrations; no ℝ and no analysis enter the core.
--
-- 四维 BD 整数核
--
-- 事件 x 处的离散标量曲率与含 n 事件的有限因果集 C 上的作用量为
--
--   R(x) = (4 / √6) · (1 / l²) · [ 1 − N₀(x) + 9 N₁(x)
--                                   − 16 N₂(x) + 8 N₃(x) ] ，
--
--   S(C) / ℏ = (4 / √6) · (l / l_p)² · [ n − N₀ + 9 N₁
--                                          − 16 N₂ + 8 N₃ ] 。
--
-- 此处仅形式化方括号内的整数。因子 (4 / √6)、(1 / l²) 与 (l / l_p)²
-- 含无理数 √6，为外部标定；核内无需 ℝ、无需分析。

bd4 : ∀ n (o : Fin n → Fin n → Bool) → ℤ
bd4 n o =
  + n
  - + (N0 n o)
  + + 9 * + (N1 n o)
  - + 16 * + (N2 n o)
  + + 8 * + (N3 n o)

------------------------------------------------------------------------
-- Diamond reference
--
-- The four-point diamond is a 1+1 poset rather than a four-dimensional
-- sprinkling, so a non-zero four-dimensional action is the expected
-- outcome. The lemmas below validate the exact counting and weighting,
-- not a physical zero.
--
-- 菱形参考
--
-- 四点菱形是 1+1 偏序而非四维 sprinkling，故四维作用量非零是预期
-- 结果。下列引理验证精确计数与加权，而非物理零值。

diamond-N0 : N0 4 diamond ≡ 4
diamond-N0 = refl
diamond-N1 : N1 4 diamond ≡ 0
diamond-N1 = refl
diamond-N2 : N2 4 diamond ≡ 1
diamond-N2 = refl
diamond-N3 : N3 4 diamond ≡ 0
diamond-N3 = refl

diamond-bd4 : bd4 4 diamond ≡ + 0 - + 16
diamond-bd4 = refl
